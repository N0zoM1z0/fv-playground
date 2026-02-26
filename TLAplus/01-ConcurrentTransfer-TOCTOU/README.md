# 01-ConcurrentTransfer-TOCTOU

## 场景描述

**并发转账中的 TOCTOU (Time-of-Check to Time-of-Use) 漏洞**

### 业务场景
- Alice 账户有 100 元，Bob 账户有 100 元
- 系统同时收到两笔转账请求，每笔都要从 Alice 转 60 元给 Bob
- 由于并发执行和缺乏同步机制，可能导致 Alice 账户透支

### 漏洞原理

```
时间线:
T1: 请求A 检查 Alice 余额: 100 >= 60 ✓ (通过)
T2: 请求B 检查 Alice 余额: 100 >= 60 ✓ (通过，此时还没扣款！)
T3: 请求A 扣款: Alice = 100 - 60 = 40
T4: 请求B 扣款: Alice = 40 - 60 = -20  💥 透支！
```

**TOCTOU 含义**: 检查余额（Check）和使用余额（Deduct）之间存在时间窗口，
在此期间系统状态可能被其他并发操作改变。

## TLA+ 模型说明

### 文件结构
```
01-ConcurrentTransfer-TOCTOU/
├── ConcurrentTransfer.tla    # TLA+ 规约文件
├── ConcurrentTransfer.cfg    # TLC 模型检查器配置
└── README.md                 # 本文件
```

### 核心概念

#### 1. 状态变量 (Variables)
- `alice_account`: Alice 的账户余额
- `bob_account`: Bob 的账户余额
- `pc`: 程序计数器，记录每个进程当前执行到哪个标签
- `amount`: 每个进程的转账金额

#### 2. 原子操作标签 (Labels)
在 PlusCal/TLA+ 中，**标签代表原子操作**:
- `Check_Balance`: 检查余额是否充足
- `Deduct_Alice`: 扣除 Alice 的钱
- `Add_Bob`: 增加 Bob 的钱

TLC 会穷举所有进程在这些标签之间的交错执行顺序。

#### 3. 安全不变量 (Invariants)
```tla
NoOverdraft == alice_account >= 0
```
**含义**: 在任何系统状态下，Alice 的余额都不能小于 0。

当 TLC 发现违反此不变量的状态时，即表示存在漏洞。

## 如何检测漏洞

### 前置要求
- Java 运行环境 (JRE/JDK 8+)
- TLA+ 工具 (tla2tools.jar)
- VS Code + TLA+ Extension (可选，用于编辑)

### 执行命令

```bash
# 进入场景目录
cd /home/pentester/fv/fv-playground/TLAplus/01-ConcurrentTransfer-TOCTOU

# 运行 TLC 模型检查器
java -cp /home/pentester/.vscode-server/extensions/tlaplus.vscode-ide-2026.2.260238/tools/tla2tools.jar tlc2.TLC ConcurrentTransfer.tla -config ConcurrentTransfer.cfg
```

> 注意: 请根据实际安装路径调整 tla2tools.jar 的路径

### 预期输出

TLC 会在 1 秒内发现漏洞并输出错误轨迹:

```
Error: Invariant NoOverdraft is violated.
Error: The behavior up to this point is:

State 1: <Initial predicate>
/ob_account = 100
/& alice_account = 100
/& pc = <<"Check_Balance", "Check_Balance">>

State 2: <Check_Balance(1)>
/& pc = <<"Deduct_Alice", "Check_Balance">>

State 3: <Check_Balance(2)>
/& pc = <<"Deduct_Alice", "Deduct_Alice">>

State 4: <Deduct_Alice(1)>
/& alice_account = 40

State 5: <Deduct_Alice(2)>
/& alice_account = -20  <-- 透支！
```

### 漏洞分析

TLC 给出的错误轨迹清晰展示了攻击路径:

| 步骤 | 进程1 | 进程2 | Alice余额 | 说明 |
|-----|-------|-------|----------|------|
| 1 | Check_Balance | - | 100 | 检查通过 |
| 2 | - | Check_Balance | 100 | 检查也通过！ |
| 3 | Deduct_Alice | - | 40 | 第一次扣款 |
| 4 | - | Deduct_Alice | **-20** | 💥 透支！ |

## 修复方案

### 方案 1: 原子化检查+扣款
将检查和扣款合并为一个原子操作:
```tla
Transfer:
  if (alice_account >= amount) {
    alice_account := alice_account - amount;
    bob_account := bob_account + amount;
  }
```

### 方案 2: 使用锁机制
在检查前获取账户锁，确保同一时间只有一个操作。

### 方案 3: 乐观锁/版本号
使用版本号检测并发修改，失败时重试。

## 学习要点

1. **并发编程的复杂性**: 即使简单的转账逻辑，在并发场景下也可能出现严重漏洞

2. **TLA+ 的价值**:
   - 🔍 穷举所有可能的执行交错
   - ⚡ 在代码部署前发现漏洞
   - 📋 提供精确的漏洞复现路径

3. **TOCTOU 漏洞模式**: 检查和使用之间的时间窗口是攻击者的机会

## 延伸阅读

- [TLA+ 官方网站](https://lamport.azurewebsites.net/tla/tla.html)
- [PlusCal 教程](https://lamport.azurewebsites.net/tla/pluscal.html)
- [TOCTOU 漏洞 Wiki](https://en.wikipedia.org/wiki/Time-of-check_to_time-of-use)
