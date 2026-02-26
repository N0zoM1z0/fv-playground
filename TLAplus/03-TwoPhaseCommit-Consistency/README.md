# 03-TwoPhaseCommit-Consistency

## 场景描述

**分布式事务的两阶段提交 (2PC) 一致性验证**

### 业务场景
- 一个协调者 (Coordinator) 管理分布式事务
- 两个参与者 (Participants) 执行本地操作
- 协调者通过两阶段提交协议确保事务原子性

### 2PC 协议流程

```
阶段 1 (投票阶段):
  1. 协调者向所有参与者发送 Prepare 请求
  2. 每个参与者执行本地事务，投票 Yes/No
  3. 参与者将投票结果返回给协调者

阶段 2 (提交阶段):
  4. 协调者收集所有投票
     - 如果所有投票都是 Yes → 决定 Commit
     - 如果有任何 No → 决定 Abort
  5. 协调者将决定发送给所有参与者
  6. 参与者根据决定执行 Commit 或 Abort
```

### 核心问题

**如何保证所有参与者要么都提交，要么都中止？**

这是分布式系统的经典难题，涉及:
- 网络分区
- 节点故障
- 消息丢失
- 脑裂问题

## TLA+ 模型说明

### 文件结构
```
03-TwoPhaseCommit-Consistency/
├── TwoPhaseCommit.tla    # TLA+ 规约文件
├── TwoPhaseCommit.cfg    # TLC 模型检查器配置
└── README.md             # 本文件
```

### 核心概念

#### 1. 状态变量 (Variables)

| 变量 | 说明 | 取值范围 |
|-----|------|---------|
| `coordinator_state` | 协调者当前阶段 | Init → CollectingVotes → Decided → Done |
| `participant_state` | 每个参与者的状态 | Init → Voted → Committed/Aborted |
| `decision` | 协调者的最终决定 | Undecided / Commit / Abort |
| `votes` | 每个参与者的投票 | None / Yes / No |
| `committed` | 已提交的参与者集合 | 参与者子集 |

#### 2. 协议参与者

**协调者 (Coordinator)**:
```
Init → CollectingVotes → Decided → Done
   ↓         ↓              ↓
开始    收集投票       做出决定
```

**参与者 (Participant)**:
```
Init → Voted → Committed
  ↓      ↓         ↓
准备   投票      提交

或

Init → Voted → Aborted
  ↓      ↓         ↓
准备   投票      中止
```

#### 3. 一致性属性 (Properties)

##### Consistency - 一致性
```tla
~(∃ p1, p2 ∈ ProcSet :
    ∧ participant_state[p1] = "Committed"
    ∧ participant_state[p2] = "Aborted")
```

**含义**: 不允许有的参与者提交，有的参与者中止！

##### ValidDecision - 有效决定
```tla
decision = "Commit" ⇒ ∀ p ∈ ProcSet : votes[p] = "Yes"
```

**含义**: 只有当所有参与者都投 Yes 时，协调者才能决定 Commit。

##### ValidCommit - 有效提交
```tla
∀ p ∈ ProcSet :
  participant_state[p] = "Committed" ⇒ decision = "Commit"
```

**含义**: 参与者只能在协调者决定 Commit 后才能提交。

##### ValidAbort - 有效中止
```tla
∀ p ∈ ProcSet :
  participant_state[p] = "Aborted" ⇒
    (decision = "Abort" ∨ votes[p] = "No")
```

**含义**: 参与者只能在协调者决定 Abort 或自己投 No 后才能中止。

## 如何验证一致性

### 前置要求
- Java 运行环境 (JRE/JDK 8+)
- TLA+ 工具 (tla2tools.jar)

### 执行命令

```bash
# 进入场景目录
cd /home/pentester/fv/fv-playground/TLAplus/03-TwoPhaseCommit-Consistency

# 运行 TLC 模型检查器
java -cp /home/pentester/.vscode-server/extensions/tlaplus.vscode-ide-2026.2.260238/tools/tla2tools.jar tlc2.TLC TwoPhaseCommit.tla -config TwoPhaseCommit.cfg
```

### 预期输出

如果模型正确，TLC 应该输出:

```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.1E-17
  47 states generated, 22 distinct states found, 0 states left on queue.
```

这表示:
- ✅ 没有发现违反一致性的情况
- ✅ 所有可达状态都已被检查
- ✅ 2PC 协议在这个模型下是正确的

### 状态空间分析

TLC 会探索所有可能的执行路径:

| 场景 | 投票组合 | 预期结果 |
|-----|---------|---------|
| 全部 Yes | (Yes, Yes) | Commit |
| 一个 No | (Yes, No) | Abort |
| 一个 No | (No, Yes) | Abort |
| 全部 No | (No, No) | Abort |

## 扩展：故障场景

当前模型假设没有故障。可以扩展模型来验证故障场景:

### 场景 1: 协调者故障
```tla
\* 协调者在决定后、发送前崩溃
Coordinator_Crash_After_Decide ==
  /\ coordinator_state = "Decided"
  /\ coordinator_state' = "Crashed"
  /\ UNCHANGED <<decision, ...>>
```

**问题**: 参与者不知道决定，会阻塞！

### 场景 2: 参与者故障
```tla
\* 参与者在投票后崩溃
Participant_Crash_After_Vote(p) ==
  /\ participant_state[p] = "Voted"
  /\ participant_state' = [participant_state EXCEPT ![p] = "Crashed"]
```

**问题**: 协调者收不到投票，需要超时机制！

### 场景 3: 三阶段提交 (3PC)
3PC 通过引入预提交阶段来解决 2PC 的阻塞问题。

## 修复方案

### 2PC 的局限性
- **阻塞问题**: 如果协调者崩溃，参与者可能永远等待
- **脑裂问题**: 网络分区可能导致不一致

### 改进方案

#### 方案 1: 超时机制
```
参与者等待决定时设置超时
超时后询问其他参与者或中止
```

#### 方案 2: Paxos/Raft
使用共识算法选举新的协调者。

#### 方案 3: 三阶段提交 (3PC)
引入预提交阶段，减少阻塞窗口。

## 学习要点

1. **分布式事务的复杂性**: 即使简单的两阶段提交，也需要严格验证

2. **TLA+ 的价值**:
   - 🔍 穷举所有可能的投票组合
   - ✅ 验证一致性属性在所有路径下都成立
   - 🐛 发现边界情况下的协议缺陷

3. **形式化验证 vs 实现**:
   - 模型验证通过 ≠ 实现正确
   - 但模型验证失败 → 协议设计有问题

## 延伸阅读

- [Two-Phase Commit Protocol](https://en.wikipedia.org/wiki/Two-phase_commit_protocol)
- [Three-Phase Commit](https://en.wikipedia.org/wiki/Three-phase_commit_protocol)
- [FLP Impossibility](https://en.wikipedia.org/wiki/FLP_impossibility)
- [Paxos Made Simple](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf)
- [Raft Consensus](https://raft.github.io/)
