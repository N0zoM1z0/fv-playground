#!/usr/bin/env python3
"""
Mini-DNS FV Framework - Phase 1: Actor State Modeling
复现 ETH SIGCOMM 2023 "A Formal Framework for End-to-End DNS Resolution"

Phase 1: 建立世界观 —— Actor 状态机建模
DNS 的本质是一个异步消息传递系统
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Any
from enum import Enum, auto
import json


class RecordType(Enum):
    """DNS 记录类型"""
    A = auto()
    NS = auto()
    CNAME = auto()
    SOA = auto()
    TXT = auto()


class MessageType(Enum):
    """消息类型"""
    QUERY = auto()
    RESPONSE = auto()


@dataclass
class DNSRecord:
    """DNS 记录"""
    name: str
    record_type: RecordType
    value: str
    ttl: int = 3600


@dataclass
class Message:
    """DNS 消息 (Query 或 Response)"""
    msg_id: int
    msg_type: MessageType
    source: str
    destination: str
    name: str
    record_type: RecordType
    records: List[DNSRecord] = field(default_factory=list)
    delegations: List[DNSRecord] = field(default_factory=list)
    
    def __repr__(self):
        if self.msg_type == MessageType.QUERY:
            return f"Query({self.msg_id}, {self.name}, {self.record_type.name})"
        else:
            return f"Response({self.msg_id}, {self.name}, {len(self.records)} records)"


@dataclass
class ZoneFile:
    """
    权威服务器的 Zone File（只读字典）
    例如: {"a.com": [NS("ns.b.com"), A("1.2.3.4")]}
    """
    domain: str
    records: Dict[str, List[DNSRecord]] = field(default_factory=dict)
    
    def lookup(self, name: str, record_type: RecordType) -> List[DNSRecord]:
        """查询记录"""
        key = f"{name}:{record_type.name}"
        return self.records.get(key, [])
    
    def has_record(self, name: str) -> bool:
        """检查是否有该域名的记录"""
        for key in self.records.keys():
            if key.startswith(name + ":"):
                return True
        return False


@dataclass
class CacheEntry:
    """缓存条目"""
    record: DNSRecord
    timestamp: float
    query_count: int = 0  # 用于统计查询次数


class DNSCache:
    """
    Resolver 的缓存
    记录解析过的域名和查询次数（用于定量分析）
    """
    def __init__(self):
        self.entries: Dict[str, CacheEntry] = {}
        self.query_stats: Dict[str, int] = {}  # 统计每个域名的查询次数
        self.total_queries = 0
        self.total_responses = 0
    
    def get(self, name: str, record_type: RecordType) -> Optional[DNSRecord]:
        """获取缓存记录"""
        key = f"{name}:{record_type.name}"
        entry = self.entries.get(key)
        if entry:
            self.query_stats[key] = self.query_stats.get(key, 0) + 1
            self.total_queries += 1
            return entry.record
        return None
    
    def put(self, record: DNSRecord):
        """添加缓存记录"""
        key = f"{record.name}:{record.record_type.name}"
        import time
        self.entries[key] = CacheEntry(record, time.time())
        self.total_responses += 1
    
    def get_stats(self) -> Dict[str, Any]:
        """获取缓存统计信息"""
        return {
            "total_queries": self.total_queries,
            "total_responses": self.total_responses,
            "unique_entries": len(self.entries),
            "query_distribution": self.query_stats
        }


@dataclass
class IterativeState:
    """
    Resolver 的迭代查询状态
    记录当前查询进行到了哪一步
    """
    original_query: str
    current_target: str
    pending_queries: Set[str] = field(default_factory=set)
    resolved_chain: List[str] = field(default_factory=list)
    depth: int = 0
    
    def __post_init__(self):
        if not self.current_target:
            self.current_target = self.original_query


class Actor:
    """Actor 基类"""
    def __init__(self, actor_id: str):
        self.actor_id = actor_id
        self.inbox: List[Message] = []
        self.outbox: List[Message] = []
    
    def receive(self, msg: Message):
        """接收消息"""
        self.inbox.append(msg)
    
    def process(self) -> List[Message]:
        """处理消息，返回发出的消息"""
        raise NotImplementedError


class Client(Actor):
    """
    客户端 Actor
    状态：只需记录 waiting_for_response
    """
    def __init__(self, client_id: str):
        super().__init__(client_id)
        self.waiting_for_response = False
        self.received_answer = False
        self.answer: Optional[Message] = None
        self.sent_queries = 0
    
    def send_query(self, name: str, record_type: RecordType) -> Message:
        """发送查询请求"""
        self.sent_queries += 1
        self.waiting_for_response = True
        msg = Message(
            msg_id=self.sent_queries,
            msg_type=MessageType.QUERY,
            source=self.actor_id,
            destination="resolver",
            name=name,
            record_type=record_type
        )
        return msg
    
    def process(self) -> List[Message]:
        """处理收到的响应"""
        messages = []
        for msg in self.inbox:
            if msg.msg_type == MessageType.RESPONSE:
                self.received_answer = True
                self.waiting_for_response = False
                self.answer = msg
                print(f"[{self.actor_id}] Received answer: {msg}")
        self.inbox.clear()
        return messages


class AuthoritativeServer(Actor):
    """
    权威服务器 Actor
    状态：它的 Zone File（只读字典）
    """
    def __init__(self, server_id: str, zone_file: ZoneFile):
        super().__init__(server_id)
        self.zone_file = zone_file
        self.received_queries = 0
        self.sent_responses = 0
    
    def process(self) -> List[Message]:
        """处理查询，返回响应"""
        messages = []
        for msg in self.inbox:
            if msg.msg_type == MessageType.QUERY:
                self.received_queries += 1
                
                # 查询 Zone File
                records = self.zone_file.lookup(msg.name, msg.record_type)
                
                # 查找委派记录 (NS)
                delegations = []
                if not records:
                    # 尝试查找 NS 记录
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
                
                messages.append(response)
                self.sent_responses += 1
                print(f"[{self.actor_id}] Query: {msg.name} -> {len(records)} records, {len(delegations)} delegations")
        
        self.inbox.clear()
        return messages


class Resolver(Actor):
    """
    递归解析器 Actor (最复杂)
    状态：Cache + Iterative_State
    """
    def __init__(self, resolver_id: str, root_servers: List[str]):
        super().__init__(resolver_id)
        self.cache = DNSCache()
        self.root_servers = root_servers
        self.iterative_states: Dict[int, IterativeState] = {}
        self.pending_queries: Dict[int, Message] = {}
        self.msg_counter = 0
    
    def _next_msg_id(self) -> int:
        """生成下一个消息 ID"""
        self.msg_counter += 1
        return self.msg_counter
    
    def process(self) -> List[Message]:
        """
        处理消息的核心逻辑
        实现重写规则：
        1. Cache Hit 规则
        2. Delegation 规则
        3. CNAME 追溯规则
        """
        messages = []
        
        for msg in self.inbox:
            if msg.msg_type == MessageType.QUERY:
                # 来自 Client 的查询
                messages.extend(self._handle_client_query(msg))
            elif msg.msg_type == MessageType.RESPONSE:
                # 来自 Auth Server 的响应
                messages.extend(self._handle_auth_response(msg))
        
        self.inbox.clear()
        return messages
    
    def _handle_client_query(self, msg: Message) -> List[Message]:
        """处理客户端查询 (Cache Hit 规则)"""
        messages = []
        
        # 检查缓存
        cached = self.cache.get(msg.name, msg.record_type)
        if cached:
            # Cache Hit!
            print(f"[{self.actor_id}] Cache HIT for {msg.name}")
            response = Message(
                msg_id=msg.msg_id,
                msg_type=MessageType.RESPONSE,
                source=self.actor_id,
                destination=msg.source,
                name=msg.name,
                record_type=msg.record_type,
                records=[cached]
            )
            messages.append(response)
        else:
            # Cache Miss，开始迭代查询
            print(f"[{self.actor_id}] Cache MISS for {msg.name}, starting iterative resolution")
            state = IterativeState(
                original_query=msg.name,
                current_target=msg.name
            )
            self.iterative_states[msg.msg_id] = state
            
            # 向根服务器发送查询
            for root in self.root_servers:
                query = Message(
                    msg_id=self._next_msg_id(),
                    msg_type=MessageType.QUERY,
                    source=self.actor_id,
                    destination=root,
                    name=msg.name,
                    record_type=msg.record_type
                )
                messages.append(query)
                state.pending_queries.add(query.msg_id)
        
        return messages
    
    def _handle_auth_response(self, msg: Message) -> List[Message]:
        """处理权威服务器响应 (Delegation/CNAME 规则)"""
        messages = []
        
        # 缓存收到的记录
        for record in msg.records:
            self.cache.put(record)
            print(f"[{self.actor_id}] Cached: {record.name} -> {record.value}")
        
        # 处理 CNAME (CNAME 追溯规则)
        cname_records = [r for r in msg.records if r.record_type == RecordType.CNAME]
        if cname_records:
            cname_target = cname_records[0].value
            print(f"[{self.actor_id}] CNAME chain: {msg.name} -> {cname_target}")
            
            # 发送新的查询
            for root in self.root_servers:
                query = Message(
                    msg_id=self._next_msg_id(),
                    msg_type=MessageType.QUERY,
                    source=self.actor_id,
                    destination=root,
                    name=cname_target,
                    record_type=RecordType.A
                )
                messages.append(query)
        
        # 处理委派 (Delegation 规则)
        if msg.delegations:
            for ns_record in msg.delegations:
                ns_target = ns_record.value
                print(f"[{self.actor_id}] Delegation: query {ns_target} for {msg.name}")
                
                # 查询 NS 的 A 记录
                query = Message(
                    msg_id=self._next_msg_id(),
                    msg_type=MessageType.QUERY,
                    source=self.actor_id,
                    destination=msg.source,  # 向同一个服务器查询
                    name=ns_target,
                    record_type=RecordType.A
                )
                messages.append(query)
        
        return messages


class GlobalState:
    """
    全局状态 (The Soup)
    包含所有 Actor 和正在飞行的 Messages
    """
    def __init__(self):
        self.actors: Dict[str, Actor] = {}
        self.inflight_messages: List[Message] = []
        self.message_history: List[Message] = []
        self.step_count = 0
    
    def add_actor(self, actor: Actor):
        """添加 Actor"""
        self.actors[actor.actor_id] = actor
    
    def send_message(self, msg: Message):
        """发送消息到网络"""
        self.inflight_messages.append(msg)
        self.message_history.append(msg)
    
    def deliver_messages(self):
        """投递消息到目标 Actor"""
        for msg in self.inflight_messages:
            if msg.destination in self.actors:
                self.actors[msg.destination].receive(msg)
        self.inflight_messages.clear()
    
    def step(self) -> bool:
        """
        执行一步重写规则
        返回是否还有活动
        """
        self.step_count += 1
        print(f"\n=== Step {self.step_count} ===")
        
        # 投递消息
        self.deliver_messages()
        
        # 让每个 Actor 处理消息
        new_messages = []
        for actor in self.actors.values():
            msgs = actor.process()
            new_messages.extend(msgs)
        
        # 新消息进入网络
        for msg in new_messages:
            self.send_message(msg)
        
        # 检查是否还有活动
        has_activity = len(self.inflight_messages) > 0
        for actor in self.actors.values():
            if actor.inbox:
                has_activity = True
                break
        
        return has_activity
    
    def run(self, max_steps: int = 100) -> Dict[str, Any]:
        """运行模拟直到完成或达到最大步数"""
        print("\n" + "=" * 70)
        print("Starting DNS Resolution Simulation")
        print("=" * 70)
        
        for i in range(max_steps):
            if not self.step():
                print(f"\nSimulation completed after {i+1} steps")
                break
        else:
            print(f"\nSimulation stopped after {max_steps} steps (possible loop)")
        
        return self.get_stats()
    
    def get_stats(self) -> Dict[str, Any]:
        """获取统计信息"""
        stats = {
            "total_steps": self.step_count,
            "total_messages": len(self.message_history),
            "actors": {}
        }
        
        for actor_id, actor in self.actors.items():
            if isinstance(actor, Resolver):
                stats["actors"][actor_id] = {
                    "type": "Resolver",
                    "cache_stats": actor.cache.get_stats()
                }
            elif isinstance(actor, Client):
                stats["actors"][actor_id] = {
                    "type": "Client",
                    "sent_queries": actor.sent_queries,
                    "received_answer": actor.received_answer
                }
            elif isinstance(actor, AuthoritativeServer):
                stats["actors"][actor_id] = {
                    "type": "AuthServer",
                    "received_queries": actor.received_queries,
                    "sent_responses": actor.sent_responses
                }
        
        return stats


def demo_normal_resolution():
    """演示正常的 DNS 解析流程"""
    print("\n" + "=" * 70)
    print("Demo: Normal DNS Resolution")
    print("=" * 70)
    
    # 创建全局状态
    state = GlobalState()
    
    # 创建权威服务器和 Zone Files
    root_zone = ZoneFile(".", {
        "com:NS": [DNSRecord("com", RecordType.NS, "ns.com.")],
    })
    
    com_zone = ZoneFile("com", {
        "example.com:NS": [DNSRecord("example.com", RecordType.NS, "ns.example.com.")],
        "ns.example.com:A": [DNSRecord("ns.example.com", RecordType.A, "1.2.3.4")],
    })
    
    example_zone = ZoneFile("example.com", {
        "www.example.com:A": [DNSRecord("www.example.com", RecordType.A, "93.184.216.34")],
    })
    
    root_server = AuthoritativeServer("root", root_zone)
    com_server = AuthoritativeServer("com", com_zone)
    example_server = AuthoritativeServer("example", example_zone)
    
    state.add_actor(root_server)
    state.add_actor(com_server)
    state.add_actor(example_server)
    
    # 创建解析器
    resolver = Resolver("resolver", ["root"])
    state.add_actor(resolver)
    
    # 创建客户端并发送查询
    client = Client("client")
    state.add_actor(client)
    
    query = client.send_query("www.example.com", RecordType.A)
    state.send_message(query)
    
    # 运行模拟
    stats = state.run(max_steps=20)
    
    print("\n" + "=" * 70)
    print("Simulation Statistics")
    print("=" * 70)
    print(json.dumps(stats, indent=2))


def demo_cname_chain():
    """演示 CNAME 链式解析"""
    print("\n" + "=" * 70)
    print("Demo: CNAME Chain Resolution")
    print("=" * 70)
    
    state = GlobalState()
    
    # Zone with CNAME
    zone = ZoneFile("test.com", {
        "alias.test.com:CNAME": [DNSRecord("alias.test.com", RecordType.CNAME, "real.test.com")],
        "real.test.com:A": [DNSRecord("real.test.com", RecordType.A, "1.2.3.4")],
    })
    
    auth_server = AuthoritativeServer("auth", zone)
    state.add_actor(auth_server)
    
    resolver = Resolver("resolver", ["auth"])
    state.add_actor(resolver)
    
    client = Client("client")
    state.add_actor(client)
    
    query = client.send_query("alias.test.com", RecordType.A)
    state.send_message(query)
    
    stats = state.run(max_steps=10)
    
    print("\n" + "=" * 70)
    print("CNAME Chain Statistics")
    print("=" * 70)
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    demo_normal_resolution()
    demo_cname_chain()
