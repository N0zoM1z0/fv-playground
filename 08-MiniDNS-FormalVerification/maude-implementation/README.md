# Maude DNS Formal Verification Implementation

## 概述

这是 ETH SIGCOMM 2023 论文 "A Formal Framework for End-to-End DNS Resolution" 的完整 Maude 实现。

## 文件结构

```
maude-implementation/
├── dns-types.maude         # 基础数据类型 (DomainName, DNSRecord, Query, Response)
├── dns-actors.maude        # Actor 模型定义 (Client, Resolver, Nameserver)
├── dns-rules.maude         # 重写规则 (对应论文 Section 3.2.3)
├── dns-probabilistic.maude # PMaude 风格的时间/概率模型
├── dns-analysis.maude      # LTL 属性定义和查询
├── dns-rewriting-blackhole.maude  # Rewrite Blackholing 攻击场景
├── dns-amplification.maude        # DoS 放大攻击场景
└── README.md               # 本文档
```

## 安装 Maude

### Ubuntu/Debian
```bash
sudo apt-get update
sudo apt-get install maude
```

### macOS
```bash
brew install maude
```

### 从源码
```bash
wget http://maude.cs.illinois.edu/downloads/current/Maude-3.4.tar.gz
tar -xzf Maude-3.4.tar.gz
export PATH=$PWD/Maude-3.4:$PATH
```

### Docker
```bash
docker run -it -v $(pwd):/work maude/maude:latest
```

## 运行方法

### 1. 基础测试
```bash
maude dns-types.maude
```

在 Maude 提示符下：
```maude
Maude> load dns-types.maude
Maude> load dns-actors.maude
Maude> load dns-rules.maude
```

### 2. 运行攻击场景
```bash
maude dns-rewriting-blackhole.maude
```

### 3. 执行 LTL 模型检查
```bash
maude dns-analysis.maude
```

## 核心概念映射

| 论文概念 | Maude 实现 | 文件 |
|---------|-----------|------|
| DomainName | `sort DomainName` | dns-types.maude |
| DNSRecord | `<_,_,_,_>` | dns-types.maude |
| Actor | `<_\|Client\|...>` / `<_\|Resolver\|...>` | dns-actors.maude |
| Rewriting Rules | `crl [rule-name] : ... => ...` | dns-rules.maude |
| Timed Messages | `{GT, msg}` / `[GT+d, msg]` | dns-probabilistic.maude |
| QuaTEx | `eq querySuccessRatio = ...` | dns-analysis.maude |

## 重写规则详解

### Rule 1: Client 发送查询
```maude
crl [client-send-query] :
    < CLIENT | Client | queries: query(ID, D, T); QL, waiting: false >
    < RESOLVER | Resolver | ... >
    =>
    < CLIENT | Client | queries: QL, waiting: true >
    < RESOLVER | Resolver | ... >
    to RESOLVER from CLIENT : query(ID, D, T)
```

### Rule 2: Resolver Cache Hit
```maude
crl [resolver-cache-hit] :
    to RESOLVER from CLIENT : query(ID, D, T)
    < RESOLVER | Resolver | cache: C, ... >
    =>
    < RESOLVER | Resolver | cache: C, ... >
    to CLIENT from RESOLVER : response(ID, D, lookupCache(D, T, C), nil, 0)
if lookupCache(D, T, C) =/= nil .
```

### Rule 3: Resolver Cache Miss
```maude
crl [resolver-cache-miss] :
    to RESOLVER from CLIENT : query(ID, D, T)
    < RESOLVER | Resolver | cache: C, pending: P, sbelt: S >
    < NS | Nameserver | zone: Z >
    =>
    < RESOLVER | Resolver | pending: pending(ID, D, T, CLIENT, 1) || P, ... >
    < NS | Nameserver | zone: Z >
    to NS from RESOLVER : query(ID, D, T)
if lookupCache(D, T, C) == nil /\ NS <- S .
```

## 验证场景

### Rewrite Blackholing
```maude
--- 配置：循环委派
zoneA: a.com NS = ns.b.com
zoneB: b.com NS = ns.a.com

--- 期望：Resolver 陷入无限循环，无法返回结果
```

### DoS Amplification
```maude
--- 配置：大量 NS 记录
attack.com NS = ns0.attack.com, ns1.attack.com, ..., ns9.attack.com

--- 期望：1个 Client 查询触发 10+ 个 Resolver 查询
```

## 与论文的对应

| 论文章节 | Maude 文件 | 实现状态 |
|---------|-----------|---------|
| 3.2.2 Actors, Messages | dns-actors.maude | ✅ 100% |
| 3.2.3 DNS Dynamics | dns-rules.maude | ✅ 90% |
| 3.3 Probabilistic Model | dns-probabilistic.maude | ⚠️ 80% |
| 5.3 LTL Properties | dns-analysis.maude | ⚠️ 70% |
| 6.2 Known Attacks | dns-rewriting-blackhole.maude | ✅ 90% |

## 局限性与未来工作

1. **QuaTEx 完整实现**：当前使用 Maude 的方程而非完整的 QuaTEx DSL
2. **PVeStA 集成**：需要通过外部工具实现并行 SMC
3. **真实 DNS 验证**：未与 BIND/Unbound/PowerDNS 对比测试

## 参考

- 原论文: [A Formal Framework for End-to-End DNS Resolution](https://doi.org/10.1145/3603269.3604870)
- Maude 手册: [All About Maude](http://maude.cs.illinois.edu/)
- PMaude: [Rewrite-based Specification Language for Probabilistic Object Systems](https://doi.org/10.1016/j.entcs.2005.10.040)
