# 08-MiniDNS-FormalVerification

## 项目概述

**复现 ETH SIGCOMM 2023: "A Formal Framework for End-to-End DNS Resolution"**

这是一个 Mini-DNS 形式化验证框架，复现了苏黎世联邦理工学院（ETH Zurich）发表在 SIGCOMM 2023 的 DNS 形式化验证工作。

### 核心创新

论文最牛的地方在于：**把"找逻辑 Bug（定性）"和"算 DoS 放大倍数（定量）"在同一个数学模型里完美融合**。

### 技术栈

- **原论文**: Maude（重写逻辑引擎）+ PVeStA（统计模型检查器）
- **本复现**: Python + Z3/SimPy（敏捷复现派）

## 四阶段路线图

### Phase 1: Actor 状态机建模

**目标**: 建立世界观 —— 定义消息、实体和全局状态

**核心概念**:
- **消息 (Messages)**: `Query(id, name, type)` 和 `Response(id, answers, delegations)`
- **实体 (Actors)**:
  - Client (客户端): 状态只需记录 `waiting_for_response`
  - Auth Server (权威服务器): 状态是它的 `Zone File`
  - Resolver (递归解析器): 状态包含 `Cache` 和 `Iterative_State`
- **全局状态 (Global Configuration)**: 包含所有 Actor 和正在飞行的 Messages 的"大池子"

**文件**: `phase1-state-modeling/dns_actor_model.py`

**运行**:
```bash
cd phase1-state-modeling
python3 dns_actor_model.py
```

### Phase 2: 重写规则

**目标**: 让世界运转 —— 定义重写规则

**核心规则**:

1. **Cache Hit 规则**
   - 匹配: Resolver 收到 Client 的 `Query(Q)`，且 `Q` 在 Cache 中
   - 重写: 吃掉 Query，吐出 `Response(A)`

2. **Delegation 规则**
   - 匹配: Resolver 收到 `Response(NS="ns.b.com")`
   - 重写: 更新 `Iterative_State`，发送子查询 `Query(name="ns.b.com", type=A)`

3. **CNAME 追溯规则**
   - 匹配: Resolver 收到 `Response(CNAME="x.com")`
   - 重写: 发送针对 `"x.com"` 的新查询

**文件**: `phase2-rewriting-rules/dns_rewriting_rules.py`

**运行**:
```bash
cd phase2-rewriting-rules
python3 dns_rewriting_rules.py
```

### Phase 3: LTL 定性模型检查

**目标**: 找逻辑 Bug —— 复现 "Rewrite Blackholing" 漏洞

**核心漏洞**:
- **Rewrite Blackholing**: 委派循环导致 Resolver 陷入死循环
- **CNAME Loop**: CNAME 链式循环

**LTL 属性**:
- `◇ (Eventually) Client.received_answer == True`
- `□ (Globally) query_depth < MAX_DEPTH`

**攻击场景**:
```
Server A (a.com): a.com NS = ns.b.com (无胶水记录)
Server B (b.com): b.com NS = ns.a.com (无胶水记录)

结果: Resolver 查 a.com → 查 ns.b.com → 查 b.com → 查 ns.a.com → ...
陷入无尽的循环！
```

**文件**: `phase3-ltl-analysis/dns_ltl_checker.py`

**运行**:
```bash
cd phase3-ltl-analysis
python3 dns_ltl_checker.py
```

### Phase 4: SMC 定量分析

**目标**: 算 DoS 放大倍数 —— 统计模型检查

**核心问题**: 黑客发 1 个包，能让 Resolver 替他发多少个包出去？

**方法**:
1. 引入概率（丢包率 10%）
2. 构造放大器 Zone（10 个 NS 记录 + 短 TTL）
3. 蒙特卡洛模拟 1000 次
4. 计算期望放大倍数 E[N]

**预期结果**:
```
Packet Loss: 10%
  Expected Amplification Factor: 30x
  Attacker sends: 1 packet (60 bytes)
  Resolver sends: 30 packets
  Bandwidth amplification: 30x
```

**文件**: `phase4-quantitative-smc/dns_quantitative_smc.py`

**运行**:
```bash
cd phase4-quantitative-smc
python3 dns_quantitative_smc.py
```

## 与原论文的对比

| 特性 | 原论文 (Maude+PVeStA) | 本复现 (Python) |
|-----|---------------------|----------------|
| 重写逻辑 | Maude 原生支持 | Python 模拟 |
| LTL 检查 | Maude LTL Model Checker | Python 状态穷举 |
| 定量分析 | PVeStA | Python Monte Carlo |
| 学习曲线 | 陡峭 | 平缓 |
| 可扩展性 | 高 | 中 |

## 学习价值

1. **理解 DNS 协议本质**: 异步消息传递系统
2. **形式化验证思维**: 从"测试"到"证明"
3. **安全研究方法论**: 定性 + 定量结合
4. **工业级应用**: 参考 AWS/Azure 的 DNS 验证实践

## 扩展方向

1. **支持完整 RFC**: 实现 EDNS0、DNSSEC 等扩展
2. **性能优化**: 使用并行计算加速 Monte Carlo
3. **可视化**: 添加 DNS 解析过程可视化
4. **真实数据**: 使用真实 Zone File 进行验证

## 参考资源

- [原论文: A Formal Framework for End-to-End DNS Resolution](https://www.research-collection.ethz.ch/handle/20.500.11850/561246)
- [Maude 官网](http://maude.cs.illinois.edu/)
- [PVeStA](https://github.com/fersanch/pvesta)
- [ETH SACS 实验室](https://www.inf.ethz.ch/research/groups/sacs.html)
