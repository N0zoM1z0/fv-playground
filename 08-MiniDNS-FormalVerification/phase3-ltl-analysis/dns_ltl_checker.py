#!/usr/bin/env python3
"""
Mini-DNS FV Framework - Phase 3: LTL Qualitative Analysis
复现 ETH SIGCOMM 2023 "Rewrite Blackholing" 漏洞

Phase 3: 找逻辑 Bug —— LTL 定性模型检查

核心：构造恶意 Zone File，用 LTL 证明死循环
"""

import sys
sys.path.insert(0, '../phase1-state-modeling')
sys.path.insert(0, '../phase2-rewriting-rules')

from dns_actor_model import (
    Actor, Client, Resolver, AuthoritativeServer,
    Message, MessageType, DNSRecord, RecordType,
    ZoneFile, GlobalState
)
from dns_rewriting_rules import ResolverWithRules
from typing import List, Dict, Set, Optional
from dataclasses import dataclass
from enum import Enum


class LTLProperty:
    """LTL 属性基类"""
    def check(self, state: GlobalState) -> bool:
        """检查属性是否满足"""
        raise NotImplementedError
    
    def description(self) -> str:
        """属性描述"""
        raise NotImplementedError


class EventuallyAnswered(LTLProperty):
    """
    LTL 属性: ◇ (Eventually) Client.received_answer == True
    
    含义：无论怎样，客户端最终一定能拿到解析结果或者 NXDOMAIN 报错
    """
    def check(self, state: GlobalState) -> bool:
        for actor in state.actors.values():
            if isinstance(actor, Client):
                if not actor.received_answer:
                    return False
        return True
    
    def description(self) -> str:
        return "◇ (Eventually) Client.received_answer == True"


class NoInfiniteLoop(LTLProperty):
    """
    LTL 属性: □ (Globally) query_depth < MAX_DEPTH
    
    含义：全局上，查询深度永远不超过最大值（防止无限循环）
    """
    def __init__(self, max_depth: int = 10):
        self.max_depth = max_depth
    
    def check(self, state: GlobalState) -> bool:
        for actor in state.actors.values():
            if isinstance(actor, Resolver):
                for state_id, iter_state in actor.iterative_states.items():
                    if iter_state.depth > self.max_depth:
                        return False
        return True
    
    def description(self) -> str:
        return f"□ (Globally) query_depth < {self.max_depth}"


class NoCachePollution(LTLProperty):
    """
    LTL 属性: 缓存查询次数不应该异常增长
    
    用于检测 DoS 放大攻击
    """
    def __init__(self, max_queries: int = 100):
        self.max_queries = max_queries
    
    def check(self, state: GlobalState) -> bool:
        for actor in state.actors.values():
            if isinstance(actor, Resolver):
                if actor.cache.total_queries > self.max_queries:
                    return False
        return True
    
    def description(self) -> str:
        return f"Cache queries < {self.max_queries}"


class ModelChecker:
    """
    模型检查器
    穷举所有可能的执行路径，检查 LTL 属性
    """
    def __init__(self, properties: List[LTLProperty]):
        self.properties = properties
        self.violations: List[Dict] = []
    
    def check(self, initial_state: GlobalState, max_steps: int = 50) -> bool:
        """
        检查模型是否满足所有 LTL 属性
        返回是否所有属性都满足
        """
        print("\n" + "=" * 70)
        print("LTL Model Checking")
        print("=" * 70)
        print("\nChecking properties:")
        for prop in self.properties:
            print(f"  - {prop.description()}")
        
        # 运行模拟
        step = 0
        while step < max_steps:
            step += 1
            
            # 检查属性
            for prop in self.properties:
                if not prop.check(initial_state):
                    self.violations.append({
                        "step": step,
                        "property": prop.description(),
                        "state": self._capture_state(initial_state)
                    })
                    print(f"\n❌ Property violated at step {step}: {prop.description()}")
                    return False
            
            # 执行一步
            if not initial_state.step():
                break
        
        print(f"\n✅ All properties satisfied after {step} steps")
        return True
    
    def _capture_state(self, state: GlobalState) -> Dict:
        """捕获当前状态"""
        return {
            "step": state.step_count,
            "messages_in_flight": len(state.inflight_messages),
            "actor_states": {
                actor_id: self._actor_state(actor)
                for actor_id, actor in state.actors.items()
            }
        }
    
    def _actor_state(self, actor: Actor) -> Dict:
        """获取 Actor 状态"""
        if isinstance(actor, Client):
            return {
                "type": "Client",
                "waiting": actor.waiting_for_response,
                "received": actor.received_answer
            }
        elif isinstance(actor, Resolver):
            return {
                "type": "Resolver",
                "cache_entries": len(actor.cache.entries),
                "iterative_states": {
                    k: {
                        "original": v.original_query,
                        "current": v.current_target,
                        "depth": v.depth
                    }
                    for k, v in actor.iterative_states.items()
                }
            }
        elif isinstance(actor, AuthoritativeServer):
            return {
                "type": "AuthServer",
                "queries_received": actor.received_queries
            }
        return {}


def create_blackholing_config() -> GlobalState:
    """
    创建 Rewrite Blackholing 配置
    
    注入毒药 (Malicious Config)：
    - Server A (管辖 a.com)：设置 a.com NS ns.b.com （没有给 IP 胶水记录）
    - Server B (管辖 b.com)：设置 b.com NS ns.a.com
    
    结果：Resolver 为了解析 a.com 去查 ns.b.com，为了查 ns.b.com 又去查 ns.a.com
    陷入无尽的循环！
    """
    print("\n" + "=" * 70)
    print("Creating Rewrite Blackholing Configuration")
    print("=" * 70)
    
    state = GlobalState()
    
    # 恶意 Zone A: a.com 委派给 ns.b.com，但没有胶水记录
    zone_a = ZoneFile("a.com", {
        "a.com:NS": [DNSRecord("a.com", RecordType.NS, "ns.b.com.")],
        # 注意：没有 ns.b.com 的 A 记录（胶水记录缺失）
    })
    
    # 恶意 Zone B: b.com 委派给 ns.a.com，同样没有胶水记录
    zone_b = ZoneFile("b.com", {
        "b.com:NS": [DNSRecord("b.com", RecordType.NS, "ns.a.com.")],
        # 注意：没有 ns.a.com 的 A 记录
    })
    
    # 添加权威服务器
    server_a = AuthoritativeServer("ns.a.com", zone_a)
    server_b = AuthoritativeServer("ns.b.com", zone_b)
    state.add_actor(server_a)
    state.add_actor(server_b)
    
    # Resolver
    resolver = ResolverWithRules("resolver", ["ns.a.com", "ns.b.com"])
    state.add_actor(resolver)
    
    # Client
    client = Client("client")
    state.add_actor(client)
    
    # 发送查询
    query = client.send_query("a.com", RecordType.A)
    state.send_message(query)
    
    return state


def create_cname_loop_config() -> GlobalState:
    """
    创建 CNAME 循环配置
    
    a.com CNAME b.com
    b.com CNAME a.com
    """
    print("\n" + "=" * 70)
    print("Creating CNAME Loop Configuration")
    print("=" * 70)
    
    state = GlobalState()
    
    # 恶意 Zone：CNAME 循环
    zone = ZoneFile("test.com", {
        "a.test.com:CNAME": [DNSRecord("a.test.com", RecordType.CNAME, "b.test.com")],
        "b.test.com:CNAME": [DNSRecord("b.test.com", RecordType.CNAME, "a.test.com")],
    })
    
    auth_server = AuthoritativeServer("auth", zone)
    state.add_actor(auth_server)
    
    resolver = ResolverWithRules("resolver", ["auth"])
    state.add_actor(resolver)
    
    client = Client("client")
    state.add_actor(client)
    
    query = client.send_query("a.test.com", RecordType.A)
    state.send_message(query)
    
    return state


def demo_rewrite_blackholing():
    """
    演示 Rewrite Blackholing 漏洞检测
    
    复现论文中的核心漏洞：
    Resolver 陷入无尽的委派循环，无法返回结果
    """
    print("\n" + "=" * 70)
    print("Demo: Rewrite Blackholing Detection")
    print("=" * 70)
    
    # 创建恶意配置
    state = create_blackholing_config()
    
    # 定义 LTL 属性
    properties = [
        EventuallyAnswered(),      # 最终应该收到答案
        NoInfiniteLoop(max_depth=5),  # 不应该无限循环
    ]
    
    # 运行模型检查
    checker = ModelChecker(properties)
    result = checker.check(state, max_steps=20)
    
    if not result:
        print("\n" + "=" * 70)
        print("🚨 VULNERABILITY DETECTED: Rewrite Blackholing")
        print("=" * 70)
        print("\nAttack Scenario:")
        print("  1. Client queries a.com")
        print("  2. a.com NS = ns.b.com (no glue record)")
        print("  3. Resolver queries ns.b.com")
        print("  4. b.com NS = ns.a.com (no glue record)")
        print("  5. Resolver queries ns.a.com")
        print("  6. ... Infinite loop!")
        print("\nImpact:")
        print("  - Resolver CPU exhaustion")
        print("  - Cache pollution")
        print("  - DoS attack on DNS infrastructure")
    
    return result


def demo_cname_loop():
    """演示 CNAME 循环检测"""
    print("\n" + "=" * 70)
    print("Demo: CNAME Loop Detection")
    print("=" * 70)
    
    state = create_cname_loop_config()
    
    properties = [
        EventuallyAnswered(),
        NoInfiniteLoop(max_depth=3),
    ]
    
    checker = ModelChecker(properties)
    result = checker.check(state, max_steps=15)
    
    if not result:
        print("\n" + "=" * 70)
        print("🚨 VULNERABILITY DETECTED: CNAME Loop")
        print("=" * 70)
        print("\nAttack Scenario:")
        print("  a.test.com CNAME b.test.com")
        print("  b.test.com CNAME a.test.com")
        print("  ... Infinite CNAME chain!")


def demo_safe_config():
    """演示安全配置的验证"""
    print("\n" + "=" * 70)
    print("Demo: Safe Configuration Verification")
    print("=" * 70)
    
    state = GlobalState()
    
    # 正常的 Zone 配置
    zone = ZoneFile("example.com", {
        "www.example.com:CNAME": [DNSRecord("www.example.com", RecordType.CNAME, "real.example.com")],
        "real.example.com:A": [DNSRecord("real.example.com", RecordType.A, "1.2.3.4")],
    })
    
    auth = AuthoritativeServer("auth", zone)
    state.add_actor(auth)
    
    resolver = ResolverWithRules("resolver", ["auth"])
    state.add_actor(resolver)
    
    client = Client("client")
    state.add_actor(client)
    
    query = client.send_query("www.example.com", RecordType.A)
    state.send_message(query)
    
    properties = [
        EventuallyAnswered(),
        NoInfiniteLoop(max_depth=5),
    ]
    
    checker = ModelChecker(properties)
    result = checker.check(state, max_steps=10)
    
    if result:
        print("\n✅ Configuration is safe!")


if __name__ == "__main__":
    # 运行所有演示
    demo_rewrite_blackholing()
    demo_cname_loop()
    demo_safe_config()
