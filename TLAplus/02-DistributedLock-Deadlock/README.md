# 02-DistributedLock-Deadlock

## 场景描述

**分布式锁系统中的死锁 (Deadlock) 检测**

### 业务场景
- 两个进程需要同时获取两个资源锁：数据库锁 + 缓存锁
- **进程 1** 的获取顺序：先 DB 锁 → 再 Cache 锁
- **进程 2** 的获取顺序：先 Cache 锁 → 再 DB 锁（相反顺序！）
- 这种不一致的获取顺序会导致经典的循环等待死锁

### 死锁原理

```
时间线:
T1: 进程1 获取 DB 锁 ✓ (持有: DB)
T2: 进程2 获取 Cache 锁 ✓ (持有: Cache)
T3: 进程1 尝试获取 Cache 锁... 被占用，等待
T4: 进程2 尝试获取 DB 锁... 被占用，等待

结果: 两个进程互相等待，永远无法继续！💀 死锁
```

**死锁四条件** (Coffman Conditions):
1. ✅ 互斥：锁是互斥资源
2. ✅ 占有并等待：进程持有锁同时等待其他锁
3. ✅ 不可抢占：锁不能被强制释放
4. ✅ 循环等待：进程1等进程2，进程2等进程1

## TLA+ 模型说明

### 文件结构
```
02-DistributedLock-Deadlock/
├── DistributedLock.tla    # TLA+ 规约文件
├── DistributedLock.cfg    # TLC 模型检查器配置
└── README.md              # 本文件
```

### 核心概念

#### 1. 状态变量 (Variables)
- `db_lock`: 数据库锁状态
  - `0` = 空闲
  - `1` = 被进程 1 持有
  - `2` = 被进程 2 持有
- `cache_lock`: 缓存锁状态（同上）
- `pc`: 程序计数器，记录每个进程的执行状态

#### 2. 进程执行流程

**进程 1** (顺序: DB → Cache):
```
GetDB → GetCache → Work → Release → Done
```

**进程 2** (顺序: Cache → DB):
```
GetCache → GetDB → Work → Release → Done
```

#### 3. 安全属性 (Properties)

##### MutexOK - 互斥性
```tla
同一个锁不能被两个进程同时持有
```

##### NoDeadlock - 无死锁
```tla
~(
  /\ db_lock = 1        \* 进程1持有DB锁
  /\ cache_lock = 2     \* 进程2持有Cache锁
  /\ pc[1] = "GetCache" \* 进程1在等待Cache锁
  /\ pc[2] = "GetDB"    \* 进程2在等待DB锁
)
```

这个不变量直接描述了死锁状态！

## 如何检测死锁

### 前置要求
- Java 运行环境 (JRE/JDK 8+)
- TLA+ 工具 (tla2tools.jar)

### 执行命令

```bash
# 进入场景目录
cd /home/pentester/fv/fv-playground/TLAplus/02-DistributedLock-Deadlock

# 运行 TLC 模型检查器
java -cp /home/pentester/.vscode-server/extensions/tlaplus.vscode-ide-2026.2.260238/tools/tla2tools.jar tlc2.TLC DistributedLock.tla -config DistributedLock.cfg
```

### 预期输出

TLC 会发现 `NoDeadlock` 不变量被违反:

```
Error: Invariant NoDeadlock is violated.
Error: The behavior up to this point is:

State 1: <Initial predicate>
/& db_lock = 0
/& cache_lock = 0
/& pc = <<"GetDB", "GetCache">>

State 2: <P1_GetDB line 45...>
/& db_lock = 1
/& pc = <<"GetCache", "GetCache">>

State 3: <P2_GetCache line 85...>
/& cache_lock = 2
/& pc = <<"GetCache", "GetDB">>

State 4: <P1_GetCache line 55...>
/& pc = <<"GetCache", "GetDB">>  \* 等待中...

State 5: <P2_GetDB line 95...>
/& pc = <<"GetCache", "GetDB">>  \* 互相等待！死锁！
```

### 死锁分析

TLC 给出的错误轨迹展示了死锁的形成过程:

| 步骤 | 进程1 | 进程2 | DB锁 | Cache锁 | 说明 |
|-----|-------|-------|------|---------|------|
| 1 | GetDB | - | 1 | 0 | 进程1获取DB锁 |
| 2 | - | GetCache | 1 | 2 | 进程2获取Cache锁 |
| 3 | GetCache | - | 1 | 2 | 进程1等待Cache锁 |
| 4 | - | GetDB | 1 | 2 | 进程2等待DB锁 |
| 5 | 等待 | 等待 | 1 | 2 | 💀 死锁！互相等待 |

## 修复方案

### 方案 1: 统一锁获取顺序
所有进程按照相同的顺序获取锁（例如都先 DB 后 Cache）:
```
进程1: DB → Cache
进程2: DB → Cache  (修改为与进程1相同)
```

### 方案 2: 超时机制
获取锁时设置超时，超时后释放已持有的锁并重试:
```python
try:
    db_lock.acquire(timeout=5)
    cache_lock.acquire(timeout=5)
except TimeoutError:
    release_all_locks()
    retry()
```

### 方案 3: 死锁检测与恢复
- 维护等待图 (Wait-For Graph)
- 检测到循环时选择一个进程回滚

### 方案 4: 银行家算法
预先分配资源，确保系统始终处于安全状态。

## 学习要点

1. **死锁的隐蔽性**: 死锁只在特定的执行时序下发生，传统测试很难发现

2. **TLA+ 的优势**:
   - 🔍 穷举所有可能的执行交错
   - 🎯 精确定位导致死锁的执行路径
   - 📊 验证修复方案是否真正解决了问题

3. **设计原则**: 预防胜于治疗
   - 统一锁获取顺序是最简单有效的预防方法
   - 在系统设计阶段用 TLA+ 验证锁策略

## 延伸阅读

- [死锁 (操作系统)](https://en.wikipedia.org/wiki/Deadlock)
- [Coffman Conditions](https://en.wikipedia.org/wiki/Deadlock#Necessary_conditions)
- [银行家算法](https://en.wikipedia.org/wiki/Banker%27s_algorithm)
- [分布式锁设计模式](https://martin.kleppmann.com/2016/02/08/how-to-do-distributed-locking.html)
