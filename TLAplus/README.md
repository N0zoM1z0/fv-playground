# TLAplus - 形式化验证实战案例集

本目录包含使用 TLA+ 进行形式化验证的经典分布式系统案例。

## 目录结构

```
TLAplus/
├── README.md                           # 本文件
├── 01-ConcurrentTransfer-TOCTOU/       # 并发转账 TOCTOU 漏洞
├── 02-DistributedLock-Deadlock/        # 分布式锁死锁检测
└── 03-TwoPhaseCommit-Consistency/      # 两阶段提交一致性验证
```

## 快速开始

### 前置要求

- Java 运行环境 (JRE/JDK 8+)
- TLA+ 工具 (`tla2tools.jar`)
- VS Code + TLA+ Extension (推荐，用于编辑和语法高亮)

### TLA+ 工具路径

TLA+ 工具通常随 VS Code 扩展安装：

```bash
# VS Code 扩展自带的路径
TLA_TOOLS="/home/pentester/.vscode-server/extensions/tlaplus.vscode-ide-2026.2.260238/tools/tla2tools.jar"

# 或者下载到本地
# wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
```

### 运行命令模板

```bash
# 进入场景目录
cd /path/to/scenario

# 运行 TLC 模型检查器
java -cp $TLA_TOOLS tlc2.TLC ModelName.tla -config ModelName.cfg
```

## 案例列表

### 01-ConcurrentTransfer-TOCTOU
**场景**: 并发转账中的 TOCTOU (Time-of-Check to Time-of-Use) 漏洞

**核心问题**: 
- 两个并发转账请求同时检查余额，然后依次扣款
- 导致账户透支（负数余额）

**验证属性**:
- `NoOverdraft`: 账户余额不能为负

**预期结果**: TLC 会发现漏洞并给出错误执行轨迹

[查看详情 →](01-ConcurrentTransfer-TOCTOU/README.md)

---

### 02-DistributedLock-Deadlock
**场景**: 分布式锁系统中的死锁检测

**核心问题**:
- 两个进程以不同顺序获取两个锁
- 进程1: DB锁 → Cache锁
- 进程2: Cache锁 → DB锁
- 导致循环等待死锁

**验证属性**:
- `NoDeadlock`: 系统不能进入死锁状态
- `MutexOK`: 锁的互斥性

**预期结果**: TLC 会发现死锁并给出导致死锁的执行路径

[查看详情 →](02-DistributedLock-Deadlock/README.md)

---

### 03-TwoPhaseCommit-Consistency
**场景**: 分布式事务的两阶段提交 (2PC) 一致性验证

**核心问题**:
- 协调者和多个参与者如何保证事务原子性
- 所有参与者要么都提交，要么都中止

**验证属性**:
- `Consistency`: 参与者状态一致
- `ValidDecision`: 协调者决定有效
- `ValidCommit`: 提交操作有效
- `ValidAbort`: 中止操作有效

**预期结果**: TLC 验证通过，确认协议正确性

[查看详情 →](03-TwoPhaseCommit-Consistency/README.md)

## TLA+ 基础概念

### 1. 什么是 TLA+？

TLA+ (Temporal Logic of Actions) 是由 Leslie Lamport 开发的形式化规约语言，用于：
- 描述并发和分布式系统
- 验证系统设计的正确性
- 在代码实现前发现设计缺陷

### 2. 核心组件

| 组件 | 说明 | 示例 |
|-----|------|------|
| **State** (状态) | 系统在某一时刻的快照 | `alice_account = 100` |
| **Action** (动作) | 状态之间的转换 | `alice_account' = alice_account - 60` |
| **Invariant** (不变量) | 所有状态都必须满足的属性 | `alice_account >= 0` |
| **Temporal Property** (时序属性) | 系统随时间演化的属性 | `Eventually alice_account = 0` |

### 3. PlusCal 语法

PlusCal 是 TLA+ 的上层语言，类似伪代码：

```tla
(* --algorithm Example {
   variables x = 0;
   
   process (Worker \in 1..2) {
     Action1:
       x := x + 1;
     
     Action2:
       x := x * 2;
   }
} *)
```

**标签 (Labels)** 表示原子操作，TLC 会穷举所有标签交错。

### 4. TLC Model Checker

TLC 是 TLA+ 的模型检查器，它会：
1. 从初始状态开始
2. 应用所有可能的动作生成新状态
3. 检查所有状态是否满足不变量
4. 如果发现违反，输出错误轨迹

## 学习路径

### 初学者
1. 阅读 [01-ConcurrentTransfer-TOCTOU](01-ConcurrentTransfer-TOCTOU/) 的 README
2. 理解 TOCTOU 漏洞原理
3. 运行 TLC 观察错误轨迹
4. 修改模型验证修复方案

### 进阶
1. 学习 [02-DistributedLock-Deadlock](02-DistributedLock-Deadlock/)
2. 理解死锁四条件和检测方法
3. 尝试修改锁获取顺序，验证是否能消除死锁

### 高级
1. 研究 [03-TwoPhaseCommit-Consistency](03-TwoPhaseCommit-Consistency/)
2. 扩展模型添加故障场景
3. 实现三阶段提交 (3PC) 并对比验证

## 常用命令

```bash
# 基本运行
java -cp tla2tools.jar tlc2.TLC Model.tla

# 指定配置文件
java -cp tla2tools.jar tlc2.TLC Model.tla -config Model.cfg

# 使用并行 GC 提高性能
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC Model.tla

# 生成状态图（需要 Graphviz）
java -cp tla2tools.jar tlc2.TLC Model.tla -dump dot,actionlabels states.dot
```

## 资源推荐

### 官方资源
- [TLA+ 官网](https://lamport.azurewebsites.net/tla/tla.html)
- [PlusCal 手册](https://lamport.azurewebsites.net/tla/pluscal.html)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)

### 书籍
- 《Specifying Systems》by Leslie Lamport (免费在线)

### 社区
- [TLA+ Google Group](https://groups.google.com/g/tlaplus)
- [TLA+ GitHub](https://github.com/tlaplus/tlaplus)

## 贡献

欢迎添加新的验证案例！建议包含：
1. 清晰的场景描述
2. 完整的 TLA+ 规约文件
3. TLC 配置文件
4. 详细的 README 说明
5. 预期输出和结果分析

## 许可证

本案例集仅供学习交流使用。
