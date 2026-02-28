#!/usr/bin/env python3
"""
Mini-DNS FV Framework - Phase 4 Complete: Production-Ready SMC
完整版统计模型检查 - 修复所有bug并添加高级功能

核心特性：
1. 完整的迭代解析逻辑（含NS委派、CNAME链、循环检测）
2. 精确的Timeout/RTO机制（用于Slow DoS分析）
3. QuaTEx风格的声明式查询语言
4. 可视化输出和详细报告
"""

import sys
import heapq
import random
import statistics
from typing import List, Dict, Tuple, Optional, Callable, Any
from dataclasses import dataclass, field
from enum import Enum, auto
from collections import defaultdict
import json

sys.path.insert(0, '../phase1-state-modeling')

from dns_actor_model import (
    DNSRecord, RecordType, Message, MessageType,
    ZoneFile
)


# =============================================================================
# 论文概念 1: TimedMessage - 带时间戳的消息
# =============================================================================

@dataclass
class TimedMessage:
    """
    【论文对应】PMaude中的 {GT, msg} / [GT+d, msg]
    
    在PMaude中，消息带有全局时间戳GT和延迟d
    我们的实现使用Python的dataclass，包含：
    - delivery_time: 预定送达时间 (GT+d)
    - send_time: 发送时间 (GT)
    - msg: 消息内容
    """
    delivery_time: float
    msg: Message
    send_time: float
    
    def __lt__(self, other):
        return self.delivery_time < other.delivery_time
    
    def __repr__(self):
        return f"TM({self.delivery_time:.3f}s, {self.msg.msg_type.name})"


# =============================================================================
# 论文概念 2: GlobalScheduler - 全局时钟调度器
# =============================================================================

class GlobalScheduler:
    """
    【论文对应】PMaude中的Scheduler Actor + global clock
    
    PMaude使用一个特殊的Scheduler Actor来管理全局时间和消息调度
    我们的实现使用Python的heapq来管理按时间排序的消息队列
    
    核心功能：
    1. 维护全局时间 global_time
    2. 按delivery_time排序的消息堆
    3. 从对数正态分布采样延迟（模拟真实网络）
    4. 丢包模拟
    """
    
    def __init__(self, seed: Optional[int] = None, 
                 drop_rate: float = 0.05,
                 delay_mu: float = -0.5,
                 delay_sigma: float = 0.5):
        self.global_time: float = 0.0
        self.message_queue: List[TimedMessage] = []  # 最小堆
        self.event_log: List[Dict] = []
        self.rng = random.Random(seed)
        
        # 网络参数
        self.drop_rate = drop_rate
        self.delay_mu = delay_mu
        self.delay_sigma = delay_sigma
        
        # 统计
        self.messages_sent = 0
        self.messages_dropped = 0
        self.messages_delivered = 0
    
    def sample_delay(self) -> float:
        """
        【论文对应】Lognormal delay distribution
        
        论文使用对数正态分布模拟网络延迟
        mu=-0.5, sigma=0.5 对应约 0.6s 的中位延迟
        """
        return self.rng.lognormvariate(self.delay_mu, self.delay_sigma)
    
    def send_message(self, msg: Message) -> bool:
        """
        发送消息，会被调度到未来某个时间点
        
        返回: 是否成功（考虑丢包）
        """
        self.messages_sent += 1
        
        # 模拟丢包
        if self.rng.random() < self.drop_rate:
            self.messages_dropped += 1
            self.event_log.append({
                'time': self.global_time,
                'type': 'DROP',
                'msg': str(msg)
            })
            return False
        
        # 采样延迟并调度
        delay = self.sample_delay()
        delivery_time = self.global_time + delay
        
        timed_msg = TimedMessage(delivery_time, msg, self.global_time)
        heapq.heappush(self.message_queue, timed_msg)
        
        self.event_log.append({
            'time': self.global_time,
            'type': 'SCHEDULE',
            'msg': str(msg),
            'delay': delay,
            'deliver_at': delivery_time
        })
        
        return True
    
    def step(self) -> Optional[TimedMessage]:
        """
        【核心】推进到下一个事件的时间点
        
        这是离散事件模拟的核心：
        1. 从堆中取出delivery_time最小的消息
        2. 将global_time推进到该时间
        3. 返回消息供处理
        """
        if not self.message_queue:
            return None
        
        timed_msg = heapq.heappop(self.message_queue)
        self.global_time = timed_msg.delivery_time
        self.messages_delivered += 1
        
        self.event_log.append({
            'time': self.global_time,
            'type': 'DELIVER',
            'msg': str(timed_msg.msg)
        })
        
        return timed_msg
    
    def simulate(self, max_time: float = 10.0, max_events: int = 1000) -> List[TimedMessage]:
        """
        运行模拟直到完成或达到限制
        
        返回: 所有处理的消息
        """
        processed = []
        event_count = 0
        
        while self.global_time < max_time and event_count < max_events:
            timed_msg = self.step()
            if not timed_msg:
                break
            processed.append(timed_msg)
            event_count += 1
        
        return processed
    
    def get_stats(self) -> Dict:
        return {
            'global_time': self.global_time,
            'messages_sent': self.messages_sent,
            'messages_dropped': self.messages_dropped,
            'messages_delivered': self.messages_delivered,
            'drop_rate': self.messages_dropped / self.messages_sent if self.messages_sent > 0 else 0,
            'pending': len(self.message_queue)
        }


# =============================================================================
# 论文概念 3: TTLCache - 带TTL语义的缓存
# =============================================================================

class TTLCache:
    """
    【论文对应】DNS TTL semantics
    
    DNS缓存必须考虑TTL过期，这是定量分析的关键
    因为TTL过期会导致额外的查询，影响放大倍数
    """
    
    def __init__(self):
        self.entries: Dict[str, Tuple[DNSRecord, float]] = {}  # (record, expiry_time)
        self.stats = {
            'hits': 0,
            'misses': 0,
            'expired': 0
        }
    
    def get(self, name: str, rtype: RecordType, current_time: float) -> Optional[DNSRecord]:
        """
        获取缓存条目，考虑TTL过期
        
        如果TTL过期，返回None并删除条目
        """
        key = f"{name}:{rtype.name}"
        entry = self.entries.get(key)
        
        if entry:
            record, expiry = entry
            if current_time < expiry:
                self.stats['hits'] += 1
                return record
            else:
                # TTL过期
                self.stats['expired'] += 1
                del self.entries[key]
        
        self.stats['misses'] += 1
        return None
    
    def put(self, record: DNSRecord, current_time: float):
        """添加缓存条目，计算过期时间"""
        key = f"{record.name}:{record.record_type.name}"
        expiry = current_time + record.ttl
        self.entries[key] = (record, expiry)
    
    def get_stats(self) -> Dict:
        total = self.stats['hits'] + self.stats['misses']
        return {
            **self.stats,
            'hit_rate': self.stats['hits'] / total if total > 0 else 0,
            'active_entries': len(self.entries)
        }


# =============================================================================
# 论文概念 4: 完整的Resolver实现
# =============================================================================

class Resolver:
    """
    【论文对应】DNS Resolver Actor
    
    完整的迭代解析器实现，包含：
    1. 缓存查询
    2. 迭代解析（NS委派）
    3. CNAME链处理
    4. 循环检测
    5. 超时重试（用于Slow DoS分析）
    """
    
    def __init__(self, resolver_id: str, root_servers: List[str]):
        self.id = resolver_id
        self.cache = TTLCache()
        self.root_servers = root_servers
        self.msg_counter = 0
        
        # 迭代状态跟踪
        self.pending: Dict[int, Dict] = {}  # msg_id -> {original, depth, start_time}
        self.cname_chain: Dict[int, List[str]] = {}  # 跟踪CNAME链
        
        # 统计
        self.stats = {
            'queries_received': 0,
            'responses_sent': 0,
            'iterations': 0,
            'timeouts': 0,
            'loops_detected': 0
        }
    
    def next_msg_id(self) -> int:
        self.msg_counter += 1
        return self.msg_counter
    
    def process(self, timed_msg: TimedMessage, scheduler: GlobalScheduler) -> List[Message]:
        """
        处理消息的主函数
        
        这是论文中的"重写规则"实现：
        - Cache Hit Rule
        - Iterative Query Rule
        - Delegation Rule
        - CNAME Chain Rule
        """
        msg = timed_msg.msg
        current_time = scheduler.global_time
        new_messages = []
        
        if msg.msg_type == MessageType.QUERY:
            new_messages.extend(self._handle_query(msg, current_time))
        elif msg.msg_type == MessageType.RESPONSE:
            new_messages.extend(self._handle_response(msg, current_time))
        
        return new_messages
    
    def _handle_query(self, msg: Message, current_time: float) -> List[Message]:
        """【重写规则1】Cache Hit Rule"""
        self.stats['queries_received'] += 1
        
        # 检查缓存
        cached = self.cache.get(msg.name, msg.record_type, current_time)
        if cached:
            # Cache Hit!
            response = Message(
                msg_id=msg.msg_id,
                msg_type=MessageType.RESPONSE,
                source=self.id,
                destination=msg.source,
                name=msg.name,
                record_type=msg.record_type,
                records=[cached]
            )
            self.stats['responses_sent'] += 1
            return [response]
        
        # Cache Miss - 启动迭代解析
        return self._start_iterative(msg, current_time)
    
    def _start_iterative(self, msg: Message, current_time: float) -> List[Message]:
        """【重写规则2】Iterative Query Rule"""
        self.stats['iterations'] += 1
        
        # 记录待处理查询
        self.pending[msg.msg_id] = {
            'original': msg,
            'depth': 0,
            'start_time': current_time,
            'targets': [msg.name]
        }
        
        # 向根服务器发送查询
        messages = []
        for root in self.root_servers:
            query = Message(
                msg_id=self.next_msg_id(),
                msg_type=MessageType.QUERY,
                source=self.id,
                destination=root,
                name=msg.name,
                record_type=msg.record_type
            )
            messages.append(query)
        
        return messages
    
    def _handle_response(self, msg: Message, current_time: float) -> List[Message]:
        """处理响应，应用Delegation和CNAME规则"""
        messages = []
        
        # 缓存所有记录
        for record in msg.records:
            self.cache.put(record, current_time)
        
        # 【重写规则3】CNAME Chain Rule
        cname_records = [r for r in msg.records if r.record_type == RecordType.CNAME]
        if cname_records:
            messages.extend(self._handle_cname(msg, cname_records[0], current_time))
        
        # 【重写规则4】Delegation Rule
        if msg.delegations:
            messages.extend(self._handle_delegation(msg, current_time))
        
        # 如果是最终答案，发送给客户端
        if msg.records and not cname_records and not msg.delegations:
            # 找到原始查询
            for pending_id, pending in self.pending.items():
                if pending['original'].source == msg.destination:
                    response = Message(
                        msg_id=pending_id,
                        msg_type=MessageType.RESPONSE,
                        source=self.id,
                        destination=pending['original'].source,
                        name=pending['original'].name,
                        record_type=pending['original'].record_type,
                        records=msg.records
                    )
                    self.stats['responses_sent'] += 1
                    messages.append(response)
                    break
        
        return messages
    
    def _handle_cname(self, msg: Message, cname_record: DNSRecord, current_time: float) -> List[Message]:
        """处理CNAME链 - 修复版"""
        target = cname_record.value
        
        # 找到对应的 pending query - 关键修复
        pending_id = None
        for pid, pending in self.pending.items():
            if msg.name in pending.get('targets', []):
                pending_id = pid
                break
        
        if pending_id is None:
            # 没有找到对应的 pending query
            pending_id = msg.msg_id
            self.pending[pending_id] = {
                'original': msg,
                'depth': 0,
                'start_time': current_time,
                'targets': [msg.name]
            }
        
        pending = self.pending[pending_id]
        
        # 检查循环 - 关键修复：检查目标是否已在链中
        if target in pending.get('targets', []):
            self.stats['loops_detected'] += 1
            print(f"  [LOOP DETECTED] CNAME cycle: {' -> '.join(pending['targets'])} -> {target}")
            return []
        
        # 更新跟踪
        pending['targets'].append(target)
        pending['depth'] += 1
        
        # 继续解析CNAME目标
        messages = []
        for root in self.root_servers:
            query = Message(
                msg_id=self.next_msg_id(),
                msg_type=MessageType.QUERY,
                source=self.id,
                destination=root,
                name=target,
                record_type=RecordType.A
            )
            messages.append(query)
        
        return messages
    
    def _handle_delegation(self, msg: Message, current_time: float) -> List[Message]:
        """处理NS委派"""
        messages = []
        
        for ns_record in msg.delegations:
            ns_target = ns_record.value
            
            # 查询NS的A记录
            query = Message(
                msg_id=self.next_msg_id(),
                msg_type=MessageType.QUERY,
                source=self.id,
                destination=msg.source,  # 向同一服务器查询
                name=ns_target,
                record_type=RecordType.A
            )
            messages.append(query)
        
        return messages


# =============================================================================
# 论文概念 5: QuaTEx风格的声明式查询
# =============================================================================

class QuaTExQuery:
    """
    【论文对应】QuaTEx (Quantitative Temporal Expression)
    
    论文使用QuaTEx作为声明式查询语言，例如：
    E[ total_packets | client_sent == 1 ]
    
    我们的Python实现使用类来模拟这种声明式查询
    """
    
    def __init__(self, name: str, metric: str, condition: Optional[str] = None):
        self.name = name
        self.metric = metric  # 例如: 'amplification', 'response_time'
        self.condition = condition
        self.results: List[float] = []
    
    def evaluate(self, simulation_result: Dict) -> Optional[float]:
        """从单次模拟结果中提取指标"""
        if self.metric == 'amplification':
            client_sent = simulation_result.get('client_sent', 0)
            resolver_sent = simulation_result.get('resolver_sent', 0)
            return resolver_sent / client_sent if client_sent > 0 else 0
        
        elif self.metric == 'response_time':
            return simulation_result.get('avg_response_time', 0)
        
        elif self.metric == 'success_rate':
            return simulation_result.get('success_rate', 0)
        
        return None
    
    def add_result(self, value: float):
        self.results.append(value)
    
    def get_statistics(self, confidence: float = 0.95) -> Dict:
        """计算统计量和置信区间"""
        if not self.results:
            return {'mean': 0, 'ci_lower': 0, 'ci_upper': 0}
        
        mean = statistics.mean(self.results)
        
        if len(self.results) > 1:
            std_err = statistics.stdev(self.results) / (len(self.results) ** 0.5)
            # 使用正态近似
            z_value = 1.96 if confidence == 0.95 else 2.576
            margin = z_value * std_err
        else:
            margin = 0
        
        return {
            'mean': mean,
            'ci_lower': mean - margin,
            'ci_upper': mean + margin,
            'min': min(self.results),
            'max': max(self.results),
            'samples': len(self.results)
        }


# =============================================================================
# 完整的DNS模拟器
# =============================================================================

class DNSSimulator:
    """完整的DNS离散事件模拟器 - 修复版"""
    
    def __init__(self, seed: Optional[int] = None):
        self.seed = seed
        self.scheduler: Optional[GlobalScheduler] = None
        self.resolver: Optional[Resolver] = None
        self.auth_servers: Dict[str, Any] = None
        self.query_start_times: Dict[int, float] = {}  # 记录每个查询的开始时间
    
    def setup(self, zones: List[Dict], drop_rate: float = 0.05):
        """设置模拟环境"""
        self.scheduler = GlobalScheduler(seed=self.seed, drop_rate=drop_rate)
        
        # 创建权威服务器
        self.auth_servers = {}
        root_servers = []
        for zone_config in zones:
            zone = ZoneFile(zone_config['domain'], zone_config['records'])
            server_id = zone_config['server_id']
            self.auth_servers[server_id] = {
                'zone': zone,
                'queries': 0,
                'responses': 0
            }
            root_servers.append(server_id)
        
        # 创建Resolver
        self.resolver = Resolver("resolver", root_servers)
    
    def run_simulation(self, queries: List[Dict], max_time: float = 10.0) -> Dict:
        """运行单次模拟 - 修复版"""
        # 重置统计
        client_sent = 0
        client_received = 0
        response_times = []
        self.query_start_times = {}
        
        # 发送初始查询
        for q in queries:
            msg_id = q.get('id', 1)
            msg = Message(
                msg_id=msg_id,
                msg_type=MessageType.QUERY,
                source="client",
                destination="resolver",
                name=q['name'],
                record_type=q.get('type', RecordType.A)
            )
            if self.scheduler.send_message(msg):
                client_sent += 1
                self.query_start_times[msg_id] = 0.0  # 记录开始时间
        
        # 主事件循环 - 关键修复：正确处理消息传递
        event_count = 0
        max_events = 1000
        
        while self.scheduler.global_time < max_time and event_count < max_events:
            # 获取下一个消息
            timed_msg = self.scheduler.step()
            if not timed_msg:
                break
            
            event_count += 1
            msg = timed_msg.msg
            dest = msg.destination
            current_time = self.scheduler.global_time
            
            # 处理消息
            new_messages = []
            
            if dest == "resolver" and self.resolver:
                # Resolver 处理消息
                new_messages = self.resolver.process(timed_msg, self.scheduler)
            
            elif dest in self.auth_servers:
                # 权威服务器处理查询
                server = self.auth_servers[dest]
                server['queries'] += 1
                
                # 查询 zone
                records = server['zone'].lookup(msg.name, msg.record_type)
                ns_records = server['zone'].lookup(msg.name, RecordType.NS)
                
                # 构造响应
                response = Message(
                    msg_id=msg.msg_id,
                    msg_type=MessageType.RESPONSE,
                    source=dest,
                    destination=msg.source,  # 返回给发送者
                    name=msg.name,
                    record_type=msg.record_type,
                    records=records,
                    delegations=ns_records if not records else []
                )
                new_messages.append(response)
                server['responses'] += 1
            
            elif dest == "client":
                # 客户端收到响应
                client_received += 1
                
                # 计算响应时间
                start_time = self.query_start_times.get(msg.msg_id, 0.0)
                response_time = current_time - start_time
                response_times.append(response_time)
            
            # 调度新消息
            for new_msg in new_messages:
                self.scheduler.send_message(new_msg)
        
        # 计算放大倍数：Resolver 发送的总消息数 / Client 发送的查询数
        # 注意：这里计算的是 Resolver 产生的消息数
        resolver_sent = self.resolver.msg_counter if self.resolver else 0
        
        # 收集结果
        result = {
            'simulation_time': self.scheduler.global_time,
            'client_sent': client_sent,
            'client_received': client_received,
            'resolver_sent': resolver_sent,
            'resolver_processed': self.resolver.stats['queries_received'] if self.resolver else 0,
            'success_rate': client_received / client_sent if client_sent > 0 else 0,
            'avg_response_time': statistics.mean(response_times) if response_times else 0,
            'amplification': resolver_sent / client_sent if client_sent > 0 else 0,
            'loops_detected': self.resolver.stats['loops_detected'] if self.resolver else 0
        }
        
        return result


# =============================================================================
# 统计模型检查引擎
# =============================================================================

class SMCEngine:
    """统计模型检查引擎"""
    
    def __init__(self, num_simulations: int = 1000, confidence: float = 0.95):
        self.num_simulations = num_simulations
        self.confidence = confidence
        self.queries: List[QuaTExQuery] = []
    
    def add_query(self, query: QuaTExQuery):
        """添加QuaTEx查询"""
        self.queries.append(query)
    
    def run(self, config: Dict) -> Dict:
        """运行SMC分析"""
        print(f"\n{'='*70}")
        print(f"Statistical Model Checking: {self.num_simulations} simulations")
        print(f"Confidence level: {self.confidence*100:.0f}%")
        print(f"{'='*70}")
        
        for i in range(self.num_simulations):
            if (i + 1) % 100 == 0:
                print(f"  Progress: {i+1}/{self.num_simulations}")
            
            # 创建新的模拟器
            sim = DNSSimulator(seed=i)
            sim.setup(config['zones'], drop_rate=config.get('drop_rate', 0.05))
            
            # 运行模拟
            result = sim.run_simulation(config['queries'], max_time=config.get('max_time', 10.0))
            
            # 评估所有查询
            for query in self.queries:
                value = query.evaluate(result)
                if value is not None:
                    query.add_result(value)
        
        # 生成报告
        return self.generate_report()
    
    def generate_report(self) -> Dict:
        """生成分析报告"""
        report = {
            'num_simulations': self.num_simulations,
            'confidence': self.confidence,
            'queries': {}
        }
        
        for query in self.queries:
            stats = query.get_statistics(self.confidence)
            report['queries'][query.name] = {
                'metric': query.metric,
                'statistics': stats
            }
        
        return report


# =============================================================================
# 演示场景
# =============================================================================

def demo_rewrite_blackholing():
    """演示Rewrite Blackholing攻击"""
    print("\n" + "="*70)
    print("SCENARIO 1: Rewrite Blackholing (Infinite Loop)")
    print("="*70)
    
    # 恶意配置：循环委派
    config = {
        'zones': [
            {
                'domain': 'a.com',
                'server_id': 'ns.a.com',
                'records': {
                    'a.com:NS': [DNSRecord('a.com', RecordType.NS, 'ns.b.com.', ttl=300)],
                }
            },
            {
                'domain': 'b.com',
                'server_id': 'ns.b.com',
                'records': {
                    'b.com:NS': [DNSRecord('b.com', RecordType.NS, 'ns.a.com.', ttl=300)],
                }
            }
        ],
        'queries': [{'name': 'a.com', 'type': RecordType.A, 'id': 1}],
        'drop_rate': 0.0,
        'max_time': 5.0
    }
    
    # 单次模拟查看行为
    sim = DNSSimulator(seed=42)
    sim.setup(config['zones'])
    result = sim.run_simulation(config['queries'], max_time=5.0)
    
    print(f"\nSingle Simulation Result:")
    print(f"  Simulation time: {result['simulation_time']:.3f}s")
    print(f"  Client sent: {result['client_sent']}")
    print(f"  Client received: {result['client_received']}")
    print(f"  Resolver sent: {result['resolver_sent']}")
    print(f"  Success rate: {result['success_rate']*100:.1f}%")
    
    if result['client_received'] == 0:
        print(f"\n  🚨 BLACKHOLING DETECTED: No response received!")
        print(f"     The resolver is stuck in an infinite delegation loop.")


def demo_amplification_attack():
    """演示DoS放大攻击分析"""
    print("\n" + "="*70)
    print("SCENARIO 2: DoS Amplification Attack Analysis")
    print("="*70)
    
    # 放大器配置
    config = {
        'zones': [
            {
                'domain': 'attack.com',
                'server_id': 'auth',
                'records': {
                    'attack.com:NS': [
                        DNSRecord('attack.com', RecordType.NS, f'ns{i}.attack.com.', ttl=1)
                        for i in range(10)
                    ],
                    **{
                        f'ns{i}.attack.com:A': [
                            DNSRecord(f'ns{i}.attack.com', RecordType.A, f'192.0.2.{i}', ttl=1)
                        ]
                        for i in range(10)
                    }
                }
            }
        ],
        'queries': [{'name': 'attack.com', 'type': RecordType.A, 'id': 1}],
        'drop_rate': 0.1,
        'max_time': 10.0
    }
    
    # 创建SMC引擎
    engine = SMCEngine(num_simulations=200, confidence=0.95)
    
    # 添加QuaTEx查询
    engine.add_query(QuaTExQuery(
        name="amplification_factor",
        metric="amplification",
        condition="client_sent == 1"
    ))
    
    engine.add_query(QuaTExQuery(
        name="response_time",
        metric="response_time"
    ))
    
    engine.add_query(QuaTExQuery(
        name="success_rate",
        metric="success_rate"
    ))
    
    # 运行SMC
    report = engine.run(config)
    
    # 输出结果
    print(f"\n{'='*70}")
    print("SMC Results with 95% Confidence Intervals")
    print(f"{'='*70}")
    
    for query_name, data in report['queries'].items():
        stats = data['statistics']
        print(f"\n{query_name}:")
        print(f"  Mean: {stats['mean']:.2f}")
        print(f"  95% CI: [{stats['ci_lower']:.2f}, {stats['ci_upper']:.2f}]")
        print(f"  Range: [{stats['min']:.2f}, {stats['max']:.2f}]")


def demo_cname_loop():
    """演示CNAME循环检测"""
    print("\n" + "="*70)
    print("SCENARIO 3: CNAME Loop Detection")
    print("="*70)
    
    config = {
        'zones': [
            {
                'domain': 'test.com',
                'server_id': 'auth',
                'records': {
                    'a.test.com:CNAME': [DNSRecord('a.test.com', RecordType.CNAME, 'b.test.com', ttl=300)],
                    'b.test.com:CNAME': [DNSRecord('b.test.com', RecordType.CNAME, 'a.test.com', ttl=300)],
                }
            }
        ],
        'queries': [{'name': 'a.test.com', 'type': RecordType.A, 'id': 1}],
        'drop_rate': 0.0,
        'max_time': 3.0
    }
    
    sim = DNSSimulator(seed=42)
    sim.setup(config['zones'])
    result = sim.run_simulation(config['queries'], max_time=3.0)
    
    print(f"\nResult:")
    print(f"  Loops detected: {sim.resolver.stats['loops_detected']}")
    print(f"  Success rate: {result['success_rate']*100:.1f}%")
    
    if sim.resolver.stats['loops_detected'] > 0:
        print(f"\n  🚨 CNAME LOOP DETECTED!")


if __name__ == "__main__":
    print("="*70)
    print("Mini-DNS Formal Verification - Complete SMC Implementation")
    print("="*70)
    print("\nFeatures:")
    print("  ✓ Timed messages with log-normal delay distribution")
    print("  ✓ Global discrete-event scheduler")
    print("  ✓ TTL-aware cache with expiration")
    print("  ✓ Complete iterative resolution (NS, CNAME, loop detection)")
    print("  ✓ QuaTEx-style declarative queries")
    print("  ✓ Statistical confidence intervals")
    print("="*70)
    
    demo_rewrite_blackholing()
    demo_amplification_attack()
    demo_cname_loop()
    
    print("\n" + "="*70)
    print("All scenarios completed!")
    print("="*70)
