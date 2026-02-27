#!/usr/bin/env python3
"""
Mini-DNS FV Framework - Phase 2: Rewriting Rules
复现 ETH SIGCOMM 2023 DNS 重写逻辑

Phase 2: 让世界运转 —— 定义重写规则
"""

import sys
sys.path.insert(0, '../phase1-state-modeling')

from dns_actor_model import (
    Actor, Client, Resolver, AuthoritativeServer,
    Message, MessageType, DNSRecord, RecordType,
    ZoneFile, GlobalState, IterativeState
)
from typing import List, Dict, Optional
from dataclasses import dataclass, field


class RewritingRule:
    """
    重写规则基类
    当满足条件 A 时，把状态 A 变成状态 B，并可能发出消息 C
    """
    def __init__(self, name: str):
        self.name = name
    
    def match(self, actor: Actor, msg: Message) -> bool:
        """匹配条件"""
        raise NotImplementedError
    
    def rewrite(self, actor: Actor, msg: Message) -> List[Message]:
        """重写：返回新消息"""
        raise NotImplementedError


class CacheHitRule(RewritingRule):
    """
    重写规则 1: Cache Hit 规则
    
    匹配: Resolver 收到 Client 的 Query(Q)，且 Q 在 Cache 中
    重写: 吃掉这个 Query，向池子里吐出一个发给 Client 的 Response(A)
    """
    def __init__(self):
        super().__init__("CacheHit")
    
    def match(self, actor: Actor, msg: Message) -> bool:
        if not isinstance(actor, Resolver):
            return False
        if msg.msg_type != MessageType.QUERY:
            return False
        # 检查缓存
        cached = actor.cache.get(msg.name, msg.record_type)
        return cached is not None
    
    def rewrite(self, actor: Resolver, msg: Message) -> List[Message]:
        cached = actor.cache.get(msg.name, msg.record_type)
        print(f"[Rule:CacheHit] {msg.name} found in cache -> {cached.value}")
        
        response = Message(
            msg_id=msg.msg_id,
            msg_type=MessageType.RESPONSE,
            source=actor.actor_id,
            destination=msg.source,
            name=msg.name,
            record_type=msg.record_type,
            records=[cached]
        )
        return [response]


class DelegationRule(RewritingRule):
    """
    重写规则 2: Delegation 规则 (收到 NS 记录)
    
    匹配: Resolver 收到 Auth Server 返回的委派 Response(NS="ns.b.com")
    重写: 更新 Resolver 的 Iterative_State，
          并向池子里吐出一个新的子查询 Query(name="ns.b.com", type=A)
    """
    def __init__(self):
        super().__init__("Delegation")
    
    def match(self, actor: Actor, msg: Message) -> bool:
        if not isinstance(actor, Resolver):
            return False
        if msg.msg_type != MessageType.RESPONSE:
            return False
        # 检查是否有委派记录
        return len(msg.delegations) > 0
    
    def rewrite(self, actor: Resolver, msg: Message) -> List[Message]:
        messages = []
        
        for ns_record in msg.delegations:
            ns_target = ns_record.value
            print(f"[Rule:Delegation] Following NS delegation to {ns_target}")
            
            # 更新迭代状态
            if msg.msg_id in actor.iterative_states:
                state = actor.iterative_states[msg.msg_id]
                state.current_target = ns_target
                state.depth += 1
            
            # 发送子查询：查询 NS 的 A 记录
            query = Message(
                msg_id=actor._next_msg_id(),
                msg_type=MessageType.QUERY,
                source=actor.actor_id,
                destination="root",  # 简化：向根查询
                name=ns_target,
                record_type=RecordType.A
            )
            messages.append(query)
        
        return messages


class CNAMEChainRule(RewritingRule):
    """
    重写规则 3: CNAME 追溯规则
    
    匹配: Resolver 收到 Response(CNAME="x.com")
    重写: 吃掉响应，吐出一个针对 "x.com" 的新查询
    """
    def __init__(self):
        super().__init__("CNAMEChain")
    
    def match(self, actor: Actor, msg: Message) -> bool:
        if not isinstance(actor, Resolver):
            return False
        if msg.msg_type != MessageType.RESPONSE:
            return False
        # 检查是否有 CNAME 记录
        cname_records = [r for r in msg.records if r.record_type == RecordType.CNAME]
        return len(cname_records) > 0
    
    def rewrite(self, actor: Resolver, msg: Message) -> List[Message]:
        cname_records = [r for r in msg.records if r.record_type == RecordType.CNAME]
        cname_target = cname_records[0].value
        
        print(f"[Rule:CNAMEChain] Following CNAME chain: {msg.name} -> {cname_target}")
        
        # 更新迭代状态
        if msg.msg_id in actor.iterative_states:
            state = actor.iterative_states[msg.msg_id]
            state.resolved_chain.append(msg.name)
            state.current_target = cname_target
        
        # 发送新查询
        query = Message(
            msg_id=actor._next_msg_id(),
            msg_type=MessageType.QUERY,
            source=actor.actor_id,
            destination="root",
            name=cname_target,
            record_type=RecordType.A
        )
        
        return [query]


class IterativeQueryRule(RewritingRule):
    """
    重写规则 4: 迭代查询启动规则
    
    匹配: Resolver 收到 Client 查询，且 Cache Miss
    重写: 创建 Iterative_State，向根服务器发送查询
    """
    def __init__(self):
        super().__init__("IterativeQuery")
    
    def match(self, actor: Actor, msg: Message) -> bool:
        if not isinstance(actor, Resolver):
            return False
        if msg.msg_type != MessageType.QUERY:
            return False
        # 检查是否来自 Client
        if not msg.source.startswith("client"):
            return False
        # 检查缓存
        cached = actor.cache.get(msg.name, msg.record_type)
        return cached is None  # Cache Miss
    
    def rewrite(self, actor: Resolver, msg: Message) -> List[Message]:
        print(f"[Rule:IterativeQuery] Cache miss for {msg.name}, starting iterative resolution")
        
        # 创建迭代状态
        state = IterativeState(
            original_query=msg.name,
            current_target=msg.name,
            depth=0
        )
        actor.iterative_states[msg.msg_id] = state
        
        # 向根服务器发送查询
        messages = []
        for root in actor.root_servers:
            query = Message(
                msg_id=actor._next_msg_id(),
                msg_type=MessageType.QUERY,
                source=actor.actor_id,
                destination=root,
                name=msg.name,
                record_type=msg.record_type
            )
            messages.append(query)
            state.pending_queries.add(query.msg_id)
        
        return messages


class RuleEngine:
    """
    规则引擎
    按优先级应用重写规则
    """
    def __init__(self):
        self.rules: List[RewritingRule] = [
            CacheHitRule(),        # 最高优先级：缓存命中
            CNAMEChainRule(),      # CNAME 追溯
            DelegationRule(),      # 委派处理
            IterativeQueryRule(),  # 启动迭代查询
        ]
    
    def apply(self, actor: Actor, msg: Message) -> List[Message]:
        """应用规则，返回生成的消息"""
        for rule in self.rules:
            if rule.match(actor, msg):
                print(f"  [RuleEngine] Applied rule: {rule.name}")
                return rule.rewrite(actor, msg)
        return []


class ResolverWithRules(Resolver):
    """
    使用规则引擎的 Resolver
    """
    def __init__(self, resolver_id: str, root_servers: List[str]):
        super().__init__(resolver_id, root_servers)
        self.rule_engine = RuleEngine()
    
    def process(self) -> List[Message]:
        """使用规则引擎处理消息"""
        messages = []
        
        for msg in self.inbox:
            new_msgs = self.rule_engine.apply(self, msg)
            messages.extend(new_msgs)
            
            # 缓存收到的记录
            if msg.msg_type == MessageType.RESPONSE:
                for record in msg.records:
                    self.cache.put(record)
        
        self.inbox.clear()
        return messages


def demo_rewrite_rules():
    """演示重写规则"""
    print("\n" + "=" * 70)
    print("Demo: DNS Rewriting Rules")
    print("=" * 70)
    
    state = GlobalState()
    
    # 创建 Zone Files
    root_zone = ZoneFile(".", {
        "com:NS": [DNSRecord("com", RecordType.NS, "ns.com.")],
    })
    
    com_zone = ZoneFile("com", {
        "example.com:NS": [DNSRecord("example.com", RecordType.NS, "ns.example.com.")],
        "ns.example.com:A": [DNSRecord("ns.example.com", RecordType.A, "1.2.3.4")],
    })
    
    example_zone = ZoneFile("example.com", {
        "www.example.com:CNAME": [DNSRecord("www.example.com", RecordType.CNAME, "real.example.com")],
        "real.example.com:A": [DNSRecord("real.example.com", RecordType.A, "93.184.216.34")],
    })
    
    # 添加权威服务器
    state.add_actor(AuthoritativeServer("root", root_zone))
    state.add_actor(AuthoritativeServer("com", com_zone))
    state.add_actor(AuthoritativeServer("example", example_zone))
    
    # 使用带规则引擎的 Resolver
    resolver = ResolverWithRules("resolver", ["root"])
    state.add_actor(resolver)
    
    # 客户端
    client = Client("client")
    state.add_actor(client)
    
    # 发送查询
    query = client.send_query("www.example.com", RecordType.A)
    state.send_message(query)
    
    # 运行
    stats = state.run(max_steps=20)
    
    print("\n" + "=" * 70)
    print("Rewriting Rules Statistics")
    print("=" * 70)
    import json
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    demo_rewrite_rules()
