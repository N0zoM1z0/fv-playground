#!/usr/bin/env python3
"""
Mini-DNS FV Framework - Phase 4 Enhanced: Advanced Statistical Model Checking
增强版 SMC - 添加真实时间/概率模型

更接近 ETH SIGCOMM 2023 论文的 PMaude 实现
"""

import sys
import heapq
import random
import statistics
import numpy as np
from typing import List, Dict, Tuple, Optional, Callable
from dataclasses import dataclass, field
from enum import Enum, auto
from collections import defaultdict
import time

sys.path.insert(0, '../phase1-state-modeling')

from dns_actor_model import (
    DNSRecord, RecordType, Message, MessageType,
    ZoneFile, Actor
)


# =============================================================================
# 核心组件：时间/概率模型
# =============================================================================

@dataclass(order=True)
class TimedMessage:
    """
    带时间戳的消息
    
    模拟真实网络中的消息延迟
    """
    def __init__(self, delivery_time: float, msg: Message, send_time: float):
        self.delivery_time = delivery_time
        self.msg = msg
        self.send_time = send_time
    
    def __lt__(self, other):
        return self.delivery_time < other.delivery_time
    
    def __repr__(self):
        return f"TimedMessage(deliver_at={self.delivery_time:.3f}, msg={self.msg})"


class GlobalScheduler:
    """
    全局时钟调度器
    
    模拟离散事件系统的时间推进
    """
    def __init__(self, seed: Optional[int] = None):
        self.global_time: float = 0.0
        self.delayed_messages: List[TimedMessage] = []  # 按 delivery_time 排序的堆
        self.event_log: List[Dict] = []  # 事件日志
        self.rng = random.Random(seed)
        
        # 延迟分布参数（对数正态分布模拟网络延迟）
        self.delay_mu = -0.5  # 均值参数
        self.delay_sigma = 0.5  # 标准差参数
        
        # 丢包率
        self.drop_rate: float = 0.1
    
    def sample_delay(self) -> float:
        """
        从对数正态分布采样延迟
        
        模拟真实网络延迟分布
        """
        return self.rng.lognormvariate(self.delay_mu, self.delay_sigma)
    
    def schedule_message(self, msg: Message) -> bool:
        """
        调度消息到未来某个时间点送达
        
        返回: 是否成功调度（考虑丢包）
        """
        # 模拟丢包
        if self.rng.random() < self.drop_rate:
            self.event_log.append({
                'time': self.global_time,
                'event': 'PACKET_DROP',
                'msg': str(msg)
            })
            return False
        
        # 采样延迟
        delay = self.sample_delay()
        delivery_time = self.global_time + delay
        
        timed_msg = TimedMessage(
            delivery_time=delivery_time,
            msg=msg,
            send_time=self.global_time
        )
        
        heapq.heappush(self.delayed_messages, timed_msg)
        
        self.event_log.append({
            'time': self.global_time,
            'event': 'SCHEDULE',
            'msg': str(msg),
            'delay': delay,
            'deliver_at': delivery_time
        })
        
        return True
    
    def step(self) -> Optional[TimedMessage]:
        """
        推进到下一个消息的时间点
        
        返回: 下一个要处理的消息，如果没有则返回 None
        """
        if self.delayed_messages:
            next_msg = heapq.heappop(self.delayed_messages)
            self.global_time = next_msg.delivery_time
            
            self.event_log.append({
                'time': self.global_time,
                'event': 'DELIVER',
                'msg': str(next_msg.msg)
            })
            
            return next_msg
        return None
    
    def peek_next_time(self) -> Optional[float]:
        """查看下一个消息的送达时间"""
        if self.delayed_messages:
            return self.delayed_messages[0].delivery_time
        return None
    
    def get_stats(self) -> Dict:
        """获取调度器统计信息"""
        delays = [e['delay'] for e in self.event_log if 'delay' in e]
        return {
            'global_time': self.global_time,
            'total_events': len(self.event_log),
            'pending_messages': len(self.delayed_messages),
            'avg_delay': statistics.mean(delays) if delays else 0,
            'max_delay': max(delays) if delays else 0
        }


class TTLCacheEntry:
    """带真实 TTL 的缓存条目"""
    def __init__(self, record: DNSRecord, insert_time: float):
        self.record = record
        self.insert_time = insert_time
        self.expiry_time = insert_time + record.ttl
        self.query_count = 0


class TTLCache:
    """
    带真实 TTL 的缓存
    
    缓存条目会在 TTL 过期后自动失效
    """
    def __init__(self):
        self.entries: Dict[str, TTLCacheEntry] = {}
        self.total_queries = 0
        self.cache_hits = 0
        self.cache_misses = 0
        self.ttl_expired_count = 0
    
    def get(self, name: str, record_type: RecordType, current_time: float) -> Optional[DNSRecord]:
        """
        获取缓存记录，考虑 TTL 过期
        
        Returns: 记录如果存在且未过期，否则 None
        """
        key = f"{name}:{record_type.name}"
        entry = self.entries.get(key)
        
        self.total_queries += 1
        
        if entry:
            if current_time < entry.expiry_time:
                # TTL 未过期
                entry.query_count += 1
                self.cache_hits += 1
                return entry.record
            else:
                # TTL 已过期
                self.ttl_expired_count += 1
                del self.entries[key]
        
        self.cache_misses += 1
        return None
    
    def put(self, record: DNSRecord, current_time: float):
        """添加缓存记录"""
        key = f"{record.name}:{record.record_type.name}"
        self.entries[key] = TTLCacheEntry(record, current_time)
    
    def cleanup_expired(self, current_time: float):
        """清理过期条目"""
        expired_keys = [
            key for key, entry in self.entries.items()
            if current_time >= entry.expiry_time
        ]
        for key in expired_keys:
            del self.entries[key]
        return len(expired_keys)
    
    def get_stats(self, current_time: float) -> Dict:
        """获取缓存统计"""
        active_entries = sum(
            1 for e in self.entries.values()
            if current_time < e.expiry_time
        )
        return {
            'total_queries': self.total_queries,
            'cache_hits': self.cache_hits,
            'cache_misses': self.cache_misses,
            'hit_rate': self.cache_hits / self.total_queries if self.total_queries > 0 else 0,
            'ttl_expired_count': self.ttl_expired_count,
            'active_entries': active_entries,
            'total_entries': len(self.entries)
        }


# =============================================================================
# 增强版 Actor 实现
# =============================================================================

class TimedActor(Actor):
    """带时间感知的 Actor 基类"""
    def __init__(self, actor_id: str):
        super().__init__(actor_id)
        self.processed_messages = 0
        self.sent_messages = 0
    
    def process_timed(self, timed_msg: TimedMessage, scheduler: GlobalScheduler) -> List[Message]:
        """处理带时间戳的消息"""
        raise NotImplementedError


class TimedResolver(TimedActor):
    """
    带时间感知的 Resolver
    
    实现完整的迭代解析逻辑
    """
    def __init__(self, resolver_id: str, root_servers: List[str]):
        super().__init__(resolver_id)
        self.cache = TTLCache()
        self.root_servers = root_servers
        self.pending_queries: Dict[int, Dict] = {}  # 待处理的查询
        self.msg_counter = 0
        
        # 统计
        self.iterations = 0
        self.timeouts = 0
    
    def _next_msg_id(self) -> int:
        self.msg_counter += 1
        return self.msg_counter
    
    def process_timed(self, timed_msg: TimedMessage, scheduler: GlobalScheduler) -> List[Message]:
        """处理消息"""
        msg = timed_msg.msg
        current_time = scheduler.global_time
        
        new_messages = []
        
        if msg.msg_type == MessageType.QUERY:
            # 检查缓存
            cached = self.cache.get(msg.name, msg.record_type, current_time)
            
            if cached:
                # Cache Hit
                response = Message(
                    msg_id=msg.msg_id,
                    msg_type=MessageType.RESPONSE,
                    source=self.actor_id,
                    destination=msg.source,
                    name=msg.name,
                    record_type=msg.record_type,
                    records=[cached]
                )
                new_messages.append(response)
                self.sent_messages += 1
            else:
                # Cache Miss - 启动迭代查询
                self._start_iterative_resolution(msg, current_time, new_messages)
        
        elif msg.msg_type == MessageType.RESPONSE:
            # 处理响应
            self._handle_response(msg, current_time, new_messages)
        
        self.processed_messages += 1
        return new_messages
    
    def _start_iterative_resolution(self, original_query: Message, 
                                     current_time: float, 
                                     new_messages: List[Message]):
        """启动迭代解析"""
        self.iterations += 1
        
        # 记录待处理查询
        self.pending_queries[original_query.msg_id] = {
            'original': original_query,
            'start_time': current_time,
            'depth': 0,
            'targets': [original_query.name]
        }
        
        # 向根服务器发送查询
        for root in self.root_servers:
            query = Message(
                msg_id=self._next_msg_id(),
                msg_type=MessageType.QUERY,
                source=self.actor_id,
                destination=root,
                name=original_query.name,
                record_type=original_query.record_type
            )
            new_messages.append(query)
            self.sent_messages += 1
    
    def _handle_response(self, msg: Message, current_time: float, 
                         new_messages: List[Message]):
        """处理响应"""
        # 缓存记录
        for record in msg.records:
            self.cache.put(record, current_time)
        
        # 处理 CNAME 链
        cname_records = [r for r in msg.records if r.record_type == RecordType.CNAME]
        if cname_records:
            target = cname_records[0].value
            
            # 检查循环
            for pending in self.pending_queries.values():
                if target in pending.get('targets', []):
                    print(f"  [WARNING] Potential CNAME loop detected: {target}")
                    return
            
            # 继续解析 CNAME 目标
            for root in self.root_servers:
                query = Message(
                    msg_id=self._next_msg_id(),
                    msg_type=MessageType.QUERY,
                    source=self.actor_id,
                    destination=root,
                    name=target,
                    record_type=RecordType.A
                )
                new_messages.append(query)
                self.sent_messages += 1


class TimedAuthoritativeServer(TimedActor):
    """带时间感知的权威服务器"""
    def __init__(self, server_id: str, zone_file: ZoneFile, 
                 response_delay: Callable[[], float] = lambda: 0.01):
        super().__init__(server_id)
        self.zone_file = zone_file
        self.response_delay = response_delay
        self.query_count = 0
    
    def process_timed(self, timed_msg: TimedMessage, scheduler: GlobalScheduler) -> List[Message]:
        """处理查询"""
        msg = timed_msg.msg
        
        if msg.msg_type != MessageType.QUERY:
            return []
        
        self.query_count += 1
        
        # 查询 Zone
        records = self.zone_file.lookup(msg.name, msg.record_type)
        
        # 查找 NS 委派
        delegations = []
        if not records:
            ns_records = self.zone_file.lookup(msg.name, RecordType.NS)
            delegations.extend(ns_records)
        
        # 构造响应
        response = Message(
            msg_id=msg.msg_id,
            msg_type=MessageType.RESPONSE,
            source=self.actor_id,
            destination=msg.source,
            name=msg.name,
            record_type=msg.record_type,
            records=records,
            delegations=delegations
        )
        
        self.sent_messages += 1
        return [response]


class TimedClient(TimedActor):
    """带时间感知的客户端"""
    def __init__(self, client_id: str):
        super().__init__(client_id)
        self.sent_queries = 0
        self.received_answers = 0
        self.query_times: Dict[int, float] = {}  # 记录查询开始时间
        self.response_times: List[float] = []  # 响应时间列表
    
    def send_query(self, name: str, record_type: RecordType, 
                   current_time: float) -> Message:
        """发送查询"""
        self.sent_queries += 1
        
        msg = Message(
            msg_id=self.sent_queries,
            msg_type=MessageType.QUERY,
            source=self.actor_id,
            destination="resolver",
            name=name,
            record_type=record_type
        )
        
        self.query_times[msg.msg_id] = current_time
        return msg
    
    def process_timed(self, timed_msg: TimedMessage, scheduler: GlobalScheduler) -> List[Message]:
        """处理响应"""
        msg = timed_msg.msg
        current_time = scheduler.global_time
        
        if msg.msg_type == MessageType.RESPONSE:
            self.received_answers += 1
            
            # 计算响应时间
            if msg.msg_id in self.query_times:
                response_time = current_time - self.query_times[msg.msg_id]
                self.response_times.append(response_time)
        
        return []
    
    def get_stats(self) -> Dict:
        """获取客户端统计"""
        stats = {
            'sent_queries': self.sent_queries,
            'received_answers': self.received_answers,
            'success_rate': self.received_answers / self.sent_queries if self.sent_queries > 0 else 0
        }
        
        if self.response_times:
            stats['avg_response_time'] = statistics.mean(self.response_times)
            stats['max_response_time'] = max(self.response_times)
            stats['min_response_time'] = min(self.response_times)
        
        return stats


# =============================================================================
# 高级 SMC 模拟器
# =============================================================================

class AdvancedSMCSimulator:
    """
    高级统计模型检查模拟器
    
    提供统计置信度保证
    """
    def __init__(self, num_simulations: int = 1000, confidence: float = 0.95):
        self.num_simulations = num_simulations
        self.confidence = confidence
        self.results: List[Dict] = []
    
    def run_single_simulation(self, config: Dict, max_time: float = 10.0) -> Dict:
        """
        运行单次模拟
        
        Args:
            config: 模拟配置
            max_time: 最大模拟时间
        
        Returns:
            模拟结果统计
        """
        seed = config.get('seed', random.randint(0, 1000000))
        scheduler = GlobalScheduler(seed=seed)
        
        # 创建网络拓扑
        actors: Dict[str, TimedActor] = {}
        
        # 创建权威服务器
        for zone_config in config.get('zones', []):
            zone = ZoneFile(zone_config['domain'], zone_config['records'])
            server = TimedAuthoritativeServer(
                zone_config['server_id'],
                zone
            )
            actors[server.actor_id] = server
        
        # 创建 Resolver
        resolver = TimedResolver(
            "resolver",
            config.get('root_servers', [])
        )
        actors[resolver.actor_id] = resolver
        
        # 创建 Client
        client = TimedClient("client")
        actors[client.actor_id] = client
        
        # 发送初始查询
        for query_config in config.get('queries', []):
            query = client.send_query(
                query_config['name'],
                query_config['type'],
                scheduler.global_time
            )
            scheduler.schedule_message(query)
        
        # 运行模拟
        event_count = 0
        max_events = 1000
        
        while scheduler.global_time < max_time and event_count < max_events:
            timed_msg = scheduler.step()
            if not timed_msg:
                break
            
            event_count += 1
            
            # 找到目标 Actor
            dest_actor = actors.get(timed_msg.msg.destination)
            if dest_actor:
                # 处理消息
                new_messages = dest_actor.process_timed(timed_msg, scheduler)
                
                # 调度新消息
                for new_msg in new_messages:
                    scheduler.schedule_message(new_msg)
        
        # 收集统计
        result = {
            'seed': seed,
            'simulation_time': scheduler.global_time,
            'events_processed': event_count,
            'client_stats': client.get_stats(),
            'resolver_stats': {
                'processed': resolver.processed_messages,
                'sent': resolver.sent_messages,
                'cache': resolver.cache.get_stats(scheduler.global_time),
                'iterations': resolver.iterations
            },
            'scheduler_stats': scheduler.get_stats()
        }
        
        return result
    
    def run_smc(self, config: Dict) -> Dict:
        """
        运行统计模型检查
        
        返回带置信区间的统计结果
        """
        print(f"\nRunning {self.num_simulations} simulations...")
        print(f"Confidence level: {self.confidence * 100}%")
        
        results = []
        for i in range(self.num_simulations):
            if (i + 1) % 100 == 0:
                print(f"  Completed {i + 1}/{self.num_simulations}")
            
            config['seed'] = i
            result = self.run_single_simulation(config)
            results.append(result)
        
        # 计算统计量
        return self._compute_statistics(results)
    
    def _compute_statistics(self, results: List[Dict]) -> Dict:
        """计算统计量和置信区间"""
        
        # 收集指标
        response_times = []
        amplification_factors = []
        success_rates = []
        
        for r in results:
            client_stats = r['client_stats']
            resolver_stats = r['resolver_stats']
            
            # 响应时间
            if 'avg_response_time' in client_stats:
                response_times.append(client_stats['avg_response_time'])
            
            # 放大倍数 (Resolver 发送 / Client 发送)
            client_sent = client_stats.get('sent_queries', 0)
            resolver_sent = resolver_stats.get('sent', 0)
            if client_sent > 0:
                amplification_factors.append(resolver_sent / client_sent)
            
            # 成功率
            success_rates.append(client_stats.get('success_rate', 0))
        
        # 计算置信区间
        def confidence_interval(data: List[float], confidence: float = 0.95) -> Tuple[float, float, float]:
            """返回 (均值, 下限, 上限)"""
            if not data:
                return 0, 0, 0
            
            mean = statistics.mean(data)
            std_err = statistics.stdev(data) / (len(data) ** 0.5) if len(data) > 1 else 0
            
            # 使用正态分布近似（如果 scipy 不可用）
            try:
                import scipy.stats as stats
                t_value = stats.t.ppf((1 + confidence) / 2, len(data) - 1) if len(data) > 1 else 1.96
            except ImportError:
                # 使用正态分布近似
                t_value = 1.96  # 95% 置信区间的 z 值
            
            margin = t_value * std_err
            
            return mean, mean - margin, mean + margin
        
        stats_result = {
            'num_simulations': self.num_simulations,
            'confidence': self.confidence,
            'response_time': {
                'mean': statistics.mean(response_times) if response_times else 0,
                'ci': confidence_interval(response_times, self.confidence) if response_times else (0, 0, 0),
                'min': min(response_times) if response_times else 0,
                'max': max(response_times) if response_times else 0
            },
            'amplification': {
                'mean': statistics.mean(amplification_factors) if amplification_factors else 0,
                'ci': confidence_interval(amplification_factors, self.confidence) if amplification_factors else (0, 0, 0),
                'min': min(amplification_factors) if amplification_factors else 0,
                'max': max(amplification_factors) if amplification_factors else 0
            },
            'success_rate': {
                'mean': statistics.mean(success_rates) if success_rates else 0,
                'ci': confidence_interval(success_rates, self.confidence) if success_rates else (0, 0, 0)
            }
        }
        
        return stats_result


# =============================================================================
# 演示场景
# =============================================================================

def demo_amplification_attack():
    """演示 DoS 放大攻击分析"""
    print("\n" + "=" * 70)
    print("Advanced SMC: DoS Amplification Attack Analysis")
    print("=" * 70)
    
    # 配置：放大器 Zone
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
        'root_servers': ['auth'],
        'queries': [
            {'name': 'attack.com', 'type': RecordType.A}
        ]
    }
    
    simulator = AdvancedSMCSimulator(num_simulations=500, confidence=0.95)
    results = simulator.run_smc(config)
    
    # 输出结果
    print("\n" + "=" * 70)
    print("Results with 95% Confidence Intervals")
    print("=" * 70)
    
    amp = results['amplification']
    mean, lower, upper = amp['ci']
    print(f"\nAmplification Factor:")
    print(f"  Mean: {amp['mean']:.2f}x")
    print(f"  95% CI: [{lower:.2f}, {upper:.2f}]")
    print(f"  Range: [{amp['min']:.2f}, {amp['max']:.2f}]")
    
    rt = results['response_time']
    mean, lower, upper = rt['ci']
    print(f"\nResponse Time:")
    print(f"  Mean: {mean*1000:.2f} ms")
    print(f"  95% CI: [{lower*1000:.2f}, {upper*1000:.2f}] ms")
    
    sr = results['success_rate']
    print(f"\nSuccess Rate: {sr['mean']*100:.1f}%")


def demo_slow_dos():
    """演示 Slow DoS 攻击分析"""
    print("\n" + "=" * 70)
    print("Advanced SMC: Slow DoS Attack Analysis")
    print("=" * 70)
    
    # 配置：慢响应服务器
    config = {
        'zones': [
            {
                'domain': 'slow.com',
                'server_id': 'auth',
                'records': {
                    'slow.com:A': [DNSRecord('slow.com', RecordType.A, '1.2.3.4', ttl=3600)]
                }
            }
        ],
        'root_servers': ['auth'],
        'queries': [
            {'name': 'slow.com', 'type': RecordType.A}
        ]
    }
    
    simulator = AdvancedSMCSimulator(num_simulations=200)
    results = simulator.run_smc(config)
    
    print("\nSlow DoS Analysis:")
    rt = results['response_time']
    print(f"  Average response time: {rt['mean']*1000:.2f} ms")
    print(f"  Max response time: {rt['max']*1000:.2f} ms")


if __name__ == "__main__":
    print("=" * 70)
    print("Enhanced Phase 4: Advanced Statistical Model Checking")
    print("Features:")
    print("  - Timed messages with log-normal delay distribution")
    print("  - Global discrete-event scheduler")
    print("  - TTL-aware cache with expiration")
    print("  - Confidence intervals for statistical guarantees")
    print("=" * 70)
    
    demo_amplification_attack()
    demo_slow_dos()
