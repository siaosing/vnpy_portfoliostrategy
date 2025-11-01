import importlib
import glob
import os
import re
import traceback
import pandas as pd
from collections import defaultdict
from pathlib import Path
from types import ModuleType
from collections.abc import Callable
from datetime import datetime, timedelta
from random import randint
from concurrent.futures import ThreadPoolExecutor

from vnpy.event import Event, EventEngine
from vnpy.trader.engine import BaseEngine, MainEngine, LogEngine
from vnpy.trader.object import (
    OrderRequest,
    CancelRequest,
    SubscribeRequest,
    HistoryRequest,
    LogData,
    TickData,
    OrderData,
    TradeData,
    PositionData,
    IOData,
    BarData,
    ContractData
)
from vnpy.trader.event import (
    EVENT_TICK,
    EVENT_ORDER,
    EVENT_TRADE,
    EVENT_POSITION,
    EVENT_IO
)
from vnpy.trader.constant import (
    Direction,
    OrderType,
    Interval,
    Exchange,
    Offset,
    Status
)
from vnpy.trader.utility import load_json, save_json, extract_vt_symbol, round_to, ZoneInfo
from vnpy.trader.datafeed import BaseDatafeed, get_datafeed
from vnpy.trader.database import BaseDatabase, get_database, DB_TZ

from .base import (
    APP_NAME,
    EVENT_PORTFOLIO_LOG,
    EVENT_PORTFOLIO_STRATEGY,
    EngineType
)
from .locale import _
from .template import StrategyTemplate

CHINA_TZ = ZoneInfo("Asia/Shanghai")       # 中国时区

instrument_lock = load_json('instrument_lock.json')
instrument_lock = instrument_lock["instrument_lock"]
# tradedate pre_date
trade_calendar = pd.read_csv(".vntrader/factor_paras/trade_calendar.csv", index_col=0)
trade_calendar = trade_calendar.drop_duplicates()
trade_calendar = trade_calendar[(trade_calendar.isOpen==1)]
today = datetime.now().strftime('%Y-%m-%d')
time_now = datetime.now().strftime('%H:%M')
trade_date = today
if time_now >= '19:00':
    trade_date = list(trade_calendar[trade_calendar.prevTradeDate == today]["calendarDate"])[0]
trade_log_path = '.vntrader/trade_log/'
if not os.path.exists(trade_log_path):
    try:
        os.makedirs(trade_log_path)
    except OSError:
        pass

order_settings = load_json('order_settings.json')
MAX_ORDER_VOLUME = order_settings['MAX_ORDER_VOLUME']
ORDER_INTERVAL = randint(2,order_settings['ORDER_INTERVAL'])  # 下单时间间隔 2-5秒 太短可能没有收到成交回报 没有及时更新self.pos_data
# 单笔最大下单量
# MAX_ORDER_VOLUME ={
#     "IF":1,
#     "IC":1,
#     "IH":1,
#     "IM":1,
#     "TL":1,
#     "AU":1,
#     "SC":1,
#     "CU":1,
#     "BC":1,
#     "SN":1,
#     "LH":1,
#     "J":1,
#     "PB":1,
#     "FG":1,
#     "DEFAULT":2
# }
# # 下单时间间隔
# ORDER_INTERVAL = 3

class StrategyEngine(BaseEngine):
    """组合策略引擎
    策略不再做订单管理维护, 全部上移至组合引擎管理, 方便多策略内部撮合订单以降低
    手续费和避免自成交. 策略只需要维护理论仓位, 当策略的理论仓位更新时修改引擎的
    target_data_diff字典, 引擎在给所有订阅了该tick.vt_symbol的策略分发完tick后
    汇总计算所需执行交易的手数, 调用execute_trade发单之后清空target_pos_diff字
    典, 在随后的update_order和update_trade中记录订单和成交信息供盘后计算pnl.
    """

    engine_type: EngineType = EngineType.LIVE

    setting_filename: str = "portfolio_strategy_setting.json"
    data_filename: str = "portfolio_strategy_data.json"
    portfolio_data_filename: str = "portfolio_data.json"

    def __init__(self, main_engine: MainEngine, event_engine: EventEngine) -> None:
        """"""
        super().__init__(main_engine, event_engine, APP_NAME)

        self.strategy_data: dict[str, dict] = {}
        self.portfolio_data: dict[str, dict] = {}

        self.classes: dict[str, type[StrategyTemplate]] = {}
        self.strategies: dict[str, StrategyTemplate] = {}

        self.symbol_strategy_map: dict[str, list[StrategyTemplate]] = defaultdict(list)
        # self.orderid_strategy_map: dict[str, StrategyTemplate] = {}
        self.price_add: int = 1

        # 委托缓存容器
        self.orders: dict[str, OrderData] = {}
        self.active_orderids: set[str] = set()
        self.to_be_cancelled_orders: dict[str, OrderData] = {}
        self.last_order_time: dict[str, datetime] = defaultdict(datetime) # 记录每个合约上次下单时间
        self.pending_volumes: dict[str, int] = defaultdict(int) # 记录每个合约剩余需要下单的量

        self.init_executor: ThreadPoolExecutor = ThreadPoolExecutor(max_workers=1)

        self.vt_tradeids: set[str] = set()

        # self.offset_converter: OffsetConverter = OffsetConverter(self.main_engine)
        # 持仓数据字典
        self.pos_data: dict[str, int] = defaultdict(int)        # 实际持仓
        self.target_data_diff: dict[str, dict[str,int]] = defaultdict(lambda:defaultdict(int))     # 各个策略需要交易的净手数

        # 数据库和数据服务
        self.database: BaseDatabase = get_database()
        self.datafeed: BaseDatafeed = get_datafeed()


    def load_portfolio_data(self) -> None:
        """加载组合数据"""
        self.portfolio_data = load_json(self.portfolio_data_filename)
        # 恢复组合持仓状态
        data: dict | None = self.portfolio_data.get("pos_data", None)
        if data:
            self.pos_data.update(data)
            self.write_log(f"self.pos_data is restored as {self.pos_data}.")

    def sync_portfolio_data(self) -> None:
        """保存组合数据到文件"""
        data: dict = self.pos_data
        data = {k:v for k,v in data.items() if v}
        self.portfolio_data["pos_data"] = data
        save_json(self.portfolio_data_filename, self.portfolio_data)

    def init_engine(self) -> None:
        """初始化引擎"""
        self.init_datafeed()
        self.load_strategy_class()
        self.load_strategy_setting()
        self.load_strategy_data()
        self.register_event()
        self.load_portfolio_data()
        self.write_log(_("组合策略引擎初始化成功"))

    def close(self) -> None:
        """关闭"""
        self.stop_all_strategies()
        # 同步数据状态
        self.sync_portfolio_data()

    def init_datafeed(self) -> None:
        """初始化数据服务"""
        result: bool = self.datafeed.init(self.write_log)
        if result:
            self.write_log(_("数据服务初始化成功"))

    def query_bar_from_datafeed(
        self, symbol: str, exchange: Exchange, interval: Interval, start: datetime, end: datetime
    ) -> list[BarData]:
        """通过数据服务获取历史数据"""
        req: HistoryRequest = HistoryRequest(
            symbol=symbol,
            exchange=exchange,
            interval=interval,
            start=start,
            end=end
        )
        data: list[BarData] = self.datafeed.query_bar_history(req, self.write_log)
        return data

    def on_event(self, type: str, data: object = None) -> None:
        """
        General event push.
        """
        event: Event = Event(type, data)
        self.event_engine.put(event)

    def register_event(self) -> None:
        """注册事件引擎"""
        self.event_engine.register(EVENT_TICK, self.process_tick_event)
        self.event_engine.register(EVENT_ORDER, self.process_order_event)
        self.event_engine.register(EVENT_TRADE, self.process_trade_event)
        #self.event_engine.register(EVENT_POSITION, self.process_position_event)
        self.event_engine.register(EVENT_IO, self.process_io_event)

        log_engine: LogEngine = self.main_engine.get_engine("log")
        log_engine.register_log(EVENT_PORTFOLIO_LOG)

    def process_tick_event(self, event: Event) -> None:
        """行情数据推送"""
        tick: TickData = event.data

        strategies: list = self.symbol_strategy_map[tick.vt_symbol]
        if not strategies:
            return

        for strategy in strategies:
            if strategy.inited:
                self.call_strategy_func(strategy, strategy.on_tick, tick)
        # 所有策略处理完tick之后由StrategyEngine.on_tick()检查是否有仓位偏差需要交易执行
        self.on_tick(tick)

    def process_order_event(self, event: Event) -> None:
        """委托数据推送"""
        order: OrderData = event.data
        self.update_order(order)

    def process_trade_event(self, event: Event) -> None:
        """成交数据推送"""
        trade: TradeData = event.data

        # 过滤重复的成交推送
        if trade.vt_tradeid in self.vt_tradeids:
            return
        self.vt_tradeids.add(trade.vt_tradeid)
        if trade.vt_orderid in self.orders:
            # self.write_log(f"process_trade_event: {trade}")
            self.update_trade(trade)


    def process_io_event(self, event: Event) -> None:
        io: IOData = event.data
        filename = io.filename
        content = io.content
        if os.path.exists(filename):
            content.to_csv(filename, index=False, mode='a', header=False, lineterminator='\n')
        else:
            content.to_csv(filename, index=False, mode='a', header=True, lineterminator='\n')


    def on_tick(self, tick: TickData) -> None:
        # 检查是否有未成交单 若有需撤单重发
        self.check_unfinished_order(tick)
        vt_symbol = tick.vt_symbol

        # 先检查是否有待执行的下单量
        if vt_symbol in self.pending_volumes:
            pending_volume = self.pending_volumes[vt_symbol]
            if pending_volume:
                self.execute_trade(vt_symbol, pending_volume, tick)
                return  # 优先处理待执行订单 本轮不处理新的目标仓位

        # 处理新的目标仓位
        diff_pos = round(sum(self.target_data_diff[vt_symbol].values()))
        if diff_pos:
            self.execute_trade(vt_symbol, diff_pos, tick)
        self.target_data_diff[vt_symbol]: dict[str,int] = defaultdict(int)


    def execute_trade(self, vt_symbol: str, volume: int, tick: TickData) -> None:
        """
        execute abs(volume) of vt_symbol @ price with split order logic
        """
        # 获取品种最大下单量
        symbol = vt_symbol.split('.')[0]
        instrument = re.sub('\\d', '', symbol).upper()
        max_order_volume = MAX_ORDER_VOLUME.get(instrument, MAX_ORDER_VOLUME["DEFAULT"])

        # 检查下单时间间隔
        current_time = tick.datetime
        last_order_time = self.last_order_time.get(vt_symbol, None)
        if last_order_time and current_time - last_order_time < timedelta(seconds=ORDER_INTERVAL):
            # 如果下单时间间隔不够 保存待执行量并返回
            self.pending_volumes[vt_symbol] = volume
            return

        # 计算本次实际下单量
        order_volume = min(abs(volume), max_order_volume)
        if volume < 0:
            order_volume = -order_volume

        # 更新剩余需要下单的数量
        remaining_volume = volume - order_volume
        if remaining_volume:
            self.pending_volumes[vt_symbol] = remaining_volume
        else:
            self.pending_volumes.pop(vt_symbol, None)

        # 执行下单
        current_pos = self.get_pos(vt_symbol)
        target_pos = current_pos + order_volume
        lock_flag = True if instrument in instrument_lock else False

        if order_volume > 0:  # long
            price = tick.ask_price_1  # 默认对手价
            if tick.ask_volume_1 >= tick.bid_volume_1 * 20:  # prone to decline
                price = tick.last_price
            # else:
            #     price = tick.ask_price_1
            if current_pos < 0:
                if target_pos <= 0:
                    self.cover(vt_symbol, price, volume=order_volume, lock=lock_flag)
                    self.write_log(f"cover {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {order_volume}, lock = {lock_flag}")
                elif target_pos > 0:
                    self.cover(vt_symbol, price, abs(current_pos), lock=lock_flag)
                    self.buy(vt_symbol, price, target_pos, lock=lock_flag)
                    self.write_log(f"cover {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {abs(current_pos)}, lock = {lock_flag}")
                    self.write_log(f"buy {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {target_pos}, lock = {lock_flag}")
            else:
                self.buy(vt_symbol, price, order_volume, lock=lock_flag)
                self.write_log(f"buy {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {order_volume},lock = {lock_flag}")
        elif order_volume < 0:  # short
            price = tick.bid_price_1  # 默认对手价
            if tick.bid_volume_1 >= tick.ask_volume_1 * 20:  # prone to climb
                price = tick.last_price
            # else:
            #     # price = tick.last_price + self.price_add * self.get_pricetick(vt_symbol)
            #     price = tick.last_price

            if current_pos > 0:
                if target_pos>= 0:
                    self.sell(vt_symbol, price, abs(order_volume), lock=lock_flag)
                    self.write_log(f"sell {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {abs(order_volume)}, lock = {lock_flag}")
                elif target_pos < 0:
                    self.sell(vt_symbol, price, current_pos, lock=lock_flag)
                    self.short(vt_symbol, price, abs(target_pos), lock=lock_flag)
                    self.write_log(f"sell {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {current_pos}, lock = {lock_flag}")
                    self.write_log(f"short {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {abs(target_pos)}, lock = {lock_flag}")
            else:
                self.short(vt_symbol, price, abs(order_volume), lock=lock_flag)
                self.write_log(f"short {vt_symbol} @ price = {price: g} with tick.last_price = {tick.last_price: g} and volume =  {abs(order_volume)}, lock = {lock_flag}")

        # 更新下单时间
        self.last_order_time[vt_symbol] = current_time


    def check_unfinished_order(self, tick: TickData) -> None:
        """ check untraded orders,cancel and chase"""
        for active_orderid in self.active_orderids:  # avoid set changed during iteration error
            if active_orderid:
                active_order = self.get_order(vt_orderid=active_orderid)
                if active_order and active_order.vt_symbol == tick.vt_symbol and active_order.datetime and tick.datetime - active_order.datetime >= timedelta(seconds=20):
                    self.cancel_order(vt_orderid=active_order.vt_orderid)
                    self.write_log(f'cancel order {active_order.vt_orderid} now------------------')
                    self.to_be_cancelled_orders[active_order.vt_orderid] = active_order
        for vt_orderid in self.to_be_cancelled_orders.copy():
            if vt_orderid:
                order = self.get_order(vt_orderid=vt_orderid)  # 最新状态
                if order.status == Status.CANCELLED and order.vt_symbol == tick.vt_symbol:
                    self.write_log(f"order cancelled successfully:{order}")
                    if order.direction == Direction.LONG:
                        new_price = tick.last_price + self.get_pricetick(tick.vt_symbol) * self.price_add
                    else:
                        new_price = tick.last_price - self.get_pricetick(tick.vt_symbol) * self.price_add

                    symbol = tick.vt_symbol.split('.')[0]
                    instrument = re.sub('\\d', '', symbol).upper()
                    lock_flag = True if instrument in instrument_lock else False
                    new_vt_orderids = self.send_order(vt_symbol=tick.vt_symbol, direction=order.direction, offset=order.offset,
                                                      price=new_price, volume=order.volume - order.traded, lock=lock_flag, net=False)
                    self.write_log(f'auto-chasing,new_vt_orderids = {new_vt_orderids}----------------')
                    self.to_be_cancelled_orders.pop(vt_orderid, None)

    def buy(self, vt_symbol: str, price: float, volume: float, lock: bool = False, net: bool = False) -> list[str]:
        """
        Send buy order to open a long position.
        """
        return self.send_order(vt_symbol, Direction.LONG, Offset.OPEN, price, volume, lock, net)

    def sell(self, vt_symbol: str, price: float, volume: float, lock: bool = False, net: bool = False) -> list[str]:
        """
        Send sell order to close a long position.
        """
        return self.send_order(vt_symbol, Direction.SHORT, Offset.CLOSE, price, volume, lock, net)

    def short(self, vt_symbol: str, price: float, volume: float, lock: bool = False, net: bool = False) -> list[str]:
        """
        Send short order to open as short position.
        """
        return self.send_order(vt_symbol, Direction.SHORT, Offset.OPEN, price, volume, lock, net)

    def cover(self, vt_symbol: str, price: float, volume: float, lock: bool = False, net: bool = False) -> list[str]:
        """
        Send cover order to close a short position.
        """
        return self.send_order(vt_symbol, Direction.LONG, Offset.CLOSE, price, volume, lock, net)

    def send_order(
        self,
        vt_symbol: str,
        direction: Direction,
        offset: Offset,
        price: float,
        volume: float,
        lock: bool,
        net: bool,
    ) -> list:
        """发送委托"""
        contract: ContractData | None = self.main_engine.get_contract(vt_symbol)
        if not contract:
            self.write_log(_("委托失败，找不到合约：{}").format(vt_symbol))
            return []

        price = round_to(price, contract.pricetick)
        volume = round_to(volume, contract.min_volume)

        original_req: OrderRequest = OrderRequest(
            symbol=contract.symbol,
            exchange=contract.exchange,
            direction=direction,
            offset=offset,
            type=OrderType.LIMIT,
            price=price,
            volume=volume,
            reference=f"{APP_NAME}_{datetime.now().strftime('%H%M%S')}"
        )

        req_list: list[OrderRequest] = self.main_engine.convert_order_request(
            original_req,
            contract.gateway_name,
            lock,
            net
        )

        vt_orderids: list = []

        for req in req_list:
            vt_orderid: str = self.main_engine.send_order(
                req, contract.gateway_name)

            if not vt_orderid:
                continue

            vt_orderids.append(vt_orderid)

            self.main_engine.update_order_request(req, vt_orderid, contract.gateway_name)

        for vt_orderid in vt_orderids:
            self.active_orderids.add(vt_orderid)
        self.write_log(f"self.active_orderids = {self.active_orderids}")

        return vt_orderids

    def cancel_order(self, vt_orderid: str) -> None:
        """委托撤单"""
        order: OrderData | None = self.get_order(vt_orderid)
        if not order:
            self.write_log(f"撤单失败，找不到委托{vt_orderid}")
            return

        req: CancelRequest = order.create_cancel_request()
        self.main_engine.cancel_order(req, order.gateway_name)

    def cancel_all(self) -> None:
        """全撤活动委托"""
        for vt_orderid in list(self.active_orderids):
            self.cancel_order(vt_orderid)

    def get_engine_type(self) -> EngineType:
        """获取引擎类型"""
        return self.engine_type

    def get_pricetick(self, vt_symbol: str) -> float | None:
        """获取合约价格跳动"""
        contract: ContractData | None = self.main_engine.get_contract(vt_symbol)

        if contract:
            pricetick: float = contract.pricetick
            return pricetick
        else:
            return None

    def get_size(self, vt_symbol: str) -> int | None:
        """获取合约乘数"""
        contract: ContractData | None = self.main_engine.get_contract(vt_symbol)

        if contract:
            size: int = contract.size
            return size
        else:
            return None

    def load_bars(self, strategy: StrategyTemplate, days: int, interval: Interval) -> None:
        """加载历史数据"""
        vt_symbols: list = strategy.vt_symbols
        dts_set: set[datetime] = set()
        history_data: dict[tuple, BarData] = {}

        # 通过接口、数据服务、数据库获取历史数据
        for vt_symbol in vt_symbols:
            data: list[BarData] = self.load_bar(vt_symbol, days, interval)

            for bar in data:
                dts_set.add(bar.datetime)
                history_data[(bar.datetime, vt_symbol)] = bar

        dts: list[datetime] = list(dts_set)
        dts.sort()

        bars: dict = {}

        for dt in dts:
            for vt_symbol in vt_symbols:
                bar = history_data.get((dt, vt_symbol), None)

                # 如果获取到合约指定时间的历史数据，缓存进bars字典
                if bar:
                    bars[vt_symbol] = bar
                # 如果获取不到，但bars字典中已有合约数据缓存, 使用之前的数据填充
                elif vt_symbol in bars:
                    old_bar: BarData = bars[vt_symbol]

                    bar = BarData(
                        symbol=old_bar.symbol,
                        exchange=old_bar.exchange,
                        datetime=dt,
                        open_price=old_bar.close_price,
                        high_price=old_bar.close_price,
                        low_price=old_bar.close_price,
                        close_price=old_bar.close_price,
                        gateway_name=old_bar.gateway_name
                    )
                    bars[vt_symbol] = bar

            self.call_strategy_func(strategy, strategy.on_bars, bars)

    def load_bar(self, vt_symbol: str, days: int, interval: Interval) -> list[BarData]:
        """加载单个合约历史数据"""
        symbol, exchange = extract_vt_symbol(vt_symbol)
        end: datetime = datetime.now(DB_TZ)
        start: datetime = end - timedelta(days)
        contract: ContractData | None = self.main_engine.get_contract(vt_symbol)
        data: list[BarData]

        # 通过接口获取历史数据
        if contract and contract.history_data:
            req: HistoryRequest = HistoryRequest(
                symbol=symbol,
                exchange=exchange,
                interval=interval,
                start=start,
                end=end
            )
            data = self.main_engine.query_history(req, contract.gateway_name)

        # 通过数据服务获取历史数据
        else:
            data = self.query_bar_from_datafeed(symbol, exchange, interval, start, end)

        # 通过数据库获取数据
        if not data:
            data = self.database.load_bar_data(
                symbol=symbol,
                exchange=exchange,
                interval=interval,
                start=start,
                end=end,
            )

        return data

    def call_strategy_func(
        self, strategy: StrategyTemplate, func: Callable, params: object = None
    ) -> None:
        """安全调用策略函数"""
        try:
            if params:
                func(params)
            else:
                func()
        except Exception:
            strategy.trading = False
            strategy.inited = False

            msg: str = _("触发异常已停止\n{}").format(traceback.format_exc())
            self.write_log(msg, strategy)

    def add_strategy(
        self, class_name: str, strategy_name: str, vt_symbols: list, setting: dict
    ) -> None:
        """添加策略实例"""
        if strategy_name in self.strategies:
            self.write_log(_("创建策略失败，存在重名{}").format(strategy_name))
            return

        strategy_class: type[StrategyTemplate] | None = self.classes.get(class_name, None)
        if not strategy_class:
            self.write_log(_("创建策略失败，找不到策略类{}").format(class_name))
            return

        strategy: StrategyTemplate = strategy_class(self, strategy_name, vt_symbols, setting)
        self.strategies[strategy_name] = strategy

        # Add vt_symbol to strategy map.
        for vt_symbol in strategy.vt_symbols:
            strategies: list = self.symbol_strategy_map[vt_symbol]
            strategies.append(strategy)

        self.save_strategy_setting()
        self.put_strategy_event(strategy)

    def init_strategy(self, strategy_name: str) -> None:
        """初始化策略"""
        self.init_executor.submit(self._init_strategy, strategy_name)

    def _init_strategy(self, strategy_name: str) -> None:
        """初始化策略"""
        strategy: StrategyTemplate = self.strategies[strategy_name]

        if strategy.inited:
            self.write_log(_("{}已经完成初始化，禁止重复操作").format(strategy_name))
            return

        self.write_log(_("{}开始执行初始化").format(strategy_name))

        # 调用策略on_init函数
        self.call_strategy_func(strategy, strategy.on_init)

        # 恢复策略状态
        data: dict | None = self.strategy_data.get(strategy_name, None)
        if data:
            for name in strategy.variables:
                value: object | None = data.get(name, None)
                if value is None:
                    continue

                # 对于持仓和目标数据字典，需要使用dict.update更新defaultdict
                if name in {"pos_data", "target_data"}:
                    strategy_data = getattr(strategy, name)
                    strategy_data.update(value)
                if isinstance(value,dict):
                    strategy_data = getattr(strategy, name)
                    strategy_data.update(value)
                # 对于其他int/float/str/bool字段则可以直接赋值
                else:
                    setattr(strategy, name, value)

        # 订阅行情
        for vt_symbol in strategy.vt_symbols:
            contract: ContractData | None = self.main_engine.get_contract(vt_symbol)
            if contract:
                req: SubscribeRequest = SubscribeRequest(
                    symbol=contract.symbol, exchange=contract.exchange)
                self.main_engine.subscribe(req, contract.gateway_name)
            else:
                self.write_log(_("行情订阅失败，找不到合约{}").format(vt_symbol), strategy)

        # 推送策略事件通知初始化完成状态
        strategy.inited = True
        self.put_strategy_event(strategy)
        self.write_log(_("{}初始化完成").format(strategy_name))

    def start_strategy(self, strategy_name: str) -> None:
        """启动策略"""
        strategy: StrategyTemplate = self.strategies[strategy_name]
        if not strategy.inited:
            self.write_log(_("策略{}启动失败，请先初始化").format(strategy.strategy_name))
            return

        if strategy.trading:
            self.write_log(_("{}已经启动，请勿重复操作").format(strategy_name))
            return

        # 调用策略on_start函数
        self.call_strategy_func(strategy, strategy.on_start)

        # 推送策略事件通知启动完成状态
        strategy.trading = True
        self.put_strategy_event(strategy)

    def stop_strategy(self, strategy_name: str) -> None:
        """停止策略"""
        strategy: StrategyTemplate = self.strategies[strategy_name]
        if not strategy.trading:
            return

        # 调用策略on_stop函数
        self.call_strategy_func(strategy, strategy.on_stop)

        # 将交易状态设为False
        strategy.trading = False

        # 撤销全部委托
        strategy.cancel_all()

        # 同步数据状态
        self.sync_strategy_data(strategy)

        # 推送策略事件通知停止完成状态
        self.put_strategy_event(strategy)

    def edit_strategy(self, strategy_name: str, setting: dict) -> None:
        """编辑策略参数"""
        strategy: StrategyTemplate = self.strategies[strategy_name]
        strategy.update_setting(setting)

        self.save_strategy_setting()
        self.put_strategy_event(strategy)

    def remove_strategy(self, strategy_name: str) -> bool:
        """移除策略实例"""
        strategy: StrategyTemplate = self.strategies[strategy_name]
        if strategy.trading:
            self.write_log(_("策略{}移除失败，请先停止").format(strategy.strategy_name))
            return False

        for vt_symbol in strategy.vt_symbols:
            strategies: list = self.symbol_strategy_map[vt_symbol]
            strategies.remove(strategy)

        for vt_orderid in strategy.active_orderids:
            if vt_orderid in self.orderid_strategy_map:
                self.orderid_strategy_map.pop(vt_orderid)

        self.strategies.pop(strategy_name)
        self.save_strategy_setting()

        self.strategy_data.pop(strategy_name, None)
        save_json(self.data_filename, self.strategy_data)

        return True

    def load_strategy_class(self) -> None:
        """加载策略类"""
        path1: Path = Path(__file__).parent.joinpath("strategies")
        self.load_strategy_class_from_folder(path1, "vnpy_portfoliostrategy.strategies")

        path2: Path = Path.cwd().joinpath("strategies")
        self.load_strategy_class_from_folder(path2, "strategies")

    def load_strategy_class_from_folder(self, path: Path, module_name: str = "") -> None:
        """通过指定文件夹加载策略类"""
        for suffix in ["py", "pyd", "so"]:
            pathname: str = str(path.joinpath(f"*.{suffix}"))
            for filepath in glob.glob(pathname):
                stem: str = Path(filepath).stem
                strategy_module_name: str = f"{module_name}.{stem}"
                self.load_strategy_class_from_module(strategy_module_name)

    def load_strategy_class_from_module(self, module_name: str) -> None:
        """通过策略文件加载策略类"""
        try:
            module: ModuleType = importlib.import_module(module_name)

            for name in dir(module):
                value = getattr(module, name)
                if (isinstance(value, type) and issubclass(value, StrategyTemplate) and value is not StrategyTemplate):
                    self.classes[value.__name__] = value
        except:  # noqa
            msg: str = _("策略文件{}加载失败，触发异常：\n{}").format(module_name, traceback.format_exc())
            self.write_log(msg)

    def load_strategy_data(self) -> None:
        """加载策略数据"""
        self.strategy_data = load_json(self.data_filename)
        self.write_log(f"self.strategy_data is restored as {self.strategy_data}.")

    def sync_strategy_data(self, strategy: StrategyTemplate) -> None:
        """保存策略数据到文件"""
        data: dict = strategy.get_variables()
        data.pop("inited")      # 不保存策略状态信息
        data.pop("trading")

        data['pos_data'] = {k:v for k,v in data['pos_data'].items() if v}
        self.strategy_data[strategy.strategy_name] = data
        save_json(self.data_filename, self.strategy_data)

    def get_all_strategy_class_names(self) -> list:
        """获取所有加载策略类名"""
        return list(self.classes.keys())

    def get_strategy_class_parameters(self, class_name: str) -> dict:
        """获取策略类参数"""
        strategy_class: type[StrategyTemplate] = self.classes[class_name]

        parameters: dict = {}
        for name in strategy_class.parameters:
            parameters[name] = getattr(strategy_class, name)

        return parameters

    def get_strategy_parameters(self, strategy_name: str) -> dict:
        """获取策略参数"""
        strategy: StrategyTemplate = self.strategies[strategy_name]
        return strategy.get_parameters()

    def init_all_strategies(self) -> None:
        """初始化所有策略"""
        for strategy_name in self.strategies.keys():
            self.init_strategy(strategy_name)

    def start_all_strategies(self) -> None:
        """启动所有策略"""
        for strategy_name in self.strategies.keys():
            self.start_strategy(strategy_name)

    def stop_all_strategies(self) -> None:
        """停止所有策略"""
        for strategy_name in self.strategies.keys():
            self.stop_strategy(strategy_name)

    def load_strategy_setting(self) -> None:
        """加载策略配置"""
        strategy_setting: dict = load_json(self.setting_filename)

        for strategy_name, strategy_config in strategy_setting.items():
            self.add_strategy(
                strategy_config["class_name"],
                strategy_name,
                strategy_config["vt_symbols"],
                strategy_config["setting"]
            )

    def save_strategy_setting(self) -> None:
        """保存策略配置"""
        strategy_setting: dict = {}

        for name, strategy in self.strategies.items():
            strategy_setting[name] = {
                "class_name": strategy.__class__.__name__,
                "vt_symbols": strategy.vt_symbols,
                "setting": strategy.get_parameters()
            }

        save_json(self.setting_filename, strategy_setting)

    def put_strategy_event(self, strategy: StrategyTemplate) -> None:
        """推送事件更新策略界面"""
        data: dict = strategy.get_data()
        event: Event = Event(EVENT_PORTFOLIO_STRATEGY, data)
        self.event_engine.put(event)

    def write_log(self, msg: str, strategy: StrategyTemplate | None = None) -> None:
        """输出日志"""
        if strategy:
            msg = f"{strategy.strategy_name}: {msg}"

        log: LogData = LogData(msg=msg, gateway_name=APP_NAME)
        event: Event = Event(type=EVENT_PORTFOLIO_LOG, data=log)
        self.event_engine.put(event)

    def send_email(self, msg: str, strategy: StrategyTemplate | None = None) -> None:
        """发送邮件"""
        if strategy:
            subject: str = f"{strategy.strategy_name}"
        else:
            subject = _("组合策略引擎")

        self.main_engine.send_email(subject, msg)

    def record_trade_log(self, trade: dict) -> None:
        single_trade = pd.DataFrame([trade])
        filename = trade_log_path + trade_date.replace('-', '') + '.csv'
        io_data = IOData(filename=filename, content=single_trade)
        self.on_event(type=EVENT_IO, data=io_data)

    def update_trade(self, trade: TradeData) -> None:
        """
        Callback of new trade data update.
        """
        # self.write_log(f"update_trade: {trade}")
        if trade.direction == Direction.LONG:
            self.pos_data[trade.vt_symbol] += trade.volume
        else:
            self.pos_data[trade.vt_symbol] -= trade.volume
        direction_flag = int(trade.direction == Direction.SHORT)
        trade_log = {'StrategyOrderID': trade.vt_orderid, 'InstrumentID': trade.vt_symbol,
                     'Time': trade.datetime.strftime('%Y%m%d_%H%M%S'), 'Direction': direction_flag,
                     'Size': trade.volume, 'Price': trade.price, 'TradeorOrder': 'Trade'}
        self.write_log(f"trade_log: {trade_log}")
        self.record_trade_log(trade_log)
        # self.sync_strategy_data()
        self.sync_portfolio_data()
        self.write_log(f"self.pos_data: {self.pos_data}")


    def update_order(self, order: OrderData) -> None:
        """
        Callback of new order data update.
        """
        if order.vt_orderid not in self.active_orderids:  #非本进程发单不做处理
            return

        if order.vt_orderid not in self.orders:
            direction_flag = int(order.direction == Direction.SHORT)

            if order.datetime is None:
                dt = datetime.now()
                # dt: datetime = dt.replace(tzinfo=CHINA_TZ)
                # order.datetime = dt
            else:
                dt = order.datetime
            order_log = {'StrategyOrderID': order.vt_orderid, 'InstrumentID': order.vt_symbol,
                         'Time': dt.strftime('%Y%m%d_%H%M%S'), 'Direction': direction_flag,
                         'Size': order.volume, 'Price': order.price, 'TradeorOrder': 'Order'}
            self.record_trade_log(order_log)
        self.orders[order.vt_orderid] = order

        if not order.is_active() and order.vt_orderid in self.active_orderids:
            self.active_orderids.remove(order.vt_orderid)

    def get_order(self, vt_orderid: str) -> Optional[OrderData]:
        """查询委托数据"""
        return self.orders.get(vt_orderid, None)

    def get_all_active_orderids(self) -> list[OrderData]:
        """获取全部活动状态的委托号"""
        return list(self.active_orderids)

    def get_pos(self, vt_symbol: str) -> int:
        """查询当前持仓"""
        return self.pos_data.get(vt_symbol, 0)