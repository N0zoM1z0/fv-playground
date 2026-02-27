# 04-PathTraversal-Security

## 场景描述

**Path Traversal (Directory Traversal) 路径穿越漏洞的形式化验证**

这是一个展示如何用 **Z3 (实现层)** 和 **TLA+ (架构层)** 两种不同思路来验证同一个安全问题的经典案例。

### 两种验证方法的对比

| 维度 | Z3 (SMT Solver) | TLA+ (Model Checker) |
|-----|-----------------|---------------------|
| **关注点** | 代码实现漏洞 | 架构设计正确性 |
| **输入** | 字符串约束 | 状态机抽象 |
| **输出** | 具体绕过 Payload | 漏洞执行轨迹 |
| **适用场景** | WAF规则审计、渗透测试 | 文件系统架构设计 |

---

## 思路一：Z3 实现层验证

### 目标
验证具体的字符串过滤逻辑是否存在绕过漏洞。

### 核心思想
利用 Z3 的 String 理论，将防御逻辑建模为字符串操作，让 Solver 逆向推导出能绕过防御的输入。

### 检测场景

#### 场景 1：简单替换绕过
```python
# 防御逻辑
sanitized = input.replace("../", "")

# Z3 找到的攻击输入: "....//"
# 替换后: "../"  (重新生成了恶意字符串!)
```

#### 场景 2：URL 解码顺序问题
```python
# 防御逻辑: 先过滤，后解码
step1 = input.replace("../", "")
step2 = url_decode(step1)

# Z3 找到的攻击输入: "%2e%2e%2f" (编码的 "../")
# 过滤时未匹配，解码后生成 "../"
```

#### 场景 3：空字节截断
```python
# 防御逻辑: 检查后缀
if input.endswith(".jpg"):
    allow_upload()

# Z3 找到的攻击输入: ".jpg\x00.php"
# 检查后缀看到 .jpg，实际处理被空字节截断
```

### 运行命令

```bash
cd /home/pentester/fv/fv-playground/04-PathTraversal-Security
python3 path_traversal_z3.py
```

### 预期输出

```
场景 1: 简单替换过滤绕过检测
🚨 找到绕过漏洞！
   攻击输入 (Payload): '../../'
   过滤后结果:         ''
   原理: 双写构造使得过滤后重新生成了 '../'

场景 2: URL 解码顺序绕过检测
🚨 找到绕过漏洞！
   攻击输入 (Payload): '../../E'
   原理: 编码形式的 '../' 绕过了第一层过滤

...

🔴 发现 4 个绕过漏洞！
```

---

## 思路二：TLA+ 架构层验证

### 目标
验证沙箱文件系统的路径解析算法在架构层面是否正确。

### 核心思想
将路径抽象为深度计数器，将 `..` 抽象为 `-1` 操作，验证无论如何操作都无法逃逸沙箱。

### 模型抽象

```
传统思路: 路径 = "/var/www/html"
TLA+抽象: 深度 = 3 (相对于根目录)

用户输入: "../../etc/passwd"
TLA+抽象: 操作序列 = <<-1, -1, 1, 1, 1>>
```

### 文件说明

| 文件 | 说明 |
|-----|------|
| `PathTraversal.tla` | 有漏洞的版本 (未检查边界) |
| `PathTraversalFixed.tla` | 修复后的版本 (检查边界) |
| `PathTraversal.cfg` | TLC 配置文件 |

### 运行命令

```bash
# 检测漏洞版本 (应该发现漏洞)
java -cp tla2tools.jar tlc2.TLC PathTraversal.tla -config PathTraversal.cfg

# 验证修复版本 (应该通过)
java -cp tla2tools.jar tlc2.TLC PathTraversalFixed.tla -config PathTraversalFixed.cfg
```

### 漏洞模型关键代码

```tla
ProcessPath ==
  ...
  ELSE 
    (* BUG: 没有检查是否已到根目录就直接减 *)
    /\ current_depth' = current_depth - 1
```

### 修复模型关键代码

```tla
ProcessPath ==
  ...
  ELSE 
    (* FIX: 只有在大于根深度时才允许返回 *)
    /\ IF current_depth > root_depth
       THEN 
         /\ current_depth' = current_depth - 1
       ELSE 
         /\ current_depth' = current_depth
```

### 安全不变量

```tla
PathSafe == current_depth >= root_depth
```

**含义**: 当前深度绝对不能小于沙箱根深度！

---

## 验证结果对比

### Z3 结果
- 🔴 发现 4 种绕过漏洞
- 输出具体的攻击 Payload
- 适用于代码审计和渗透测试

### TLA+ 结果
- 🔴 漏洞版本: `PathSafe` 不变量被违反
- 🟢 修复版本: 158 个状态，无错误
- 证明了修复方案在数学上的正确性

---

## 修复建议

### 1. 使用规范化路径解析
```python
import os
real_path = os.path.realpath(user_input)
if not real_path.startswith(allowed_dir):
    reject()
```

### 2. 验证最终路径
```python
from pathlib import Path
resolved = Path(base_dir, user_input).resolve()
if not str(resolved).startswith(str(base_dir)):
    reject()
```

### 3. 白名单验证
不要依赖黑名单过滤，使用白名单验证允许的字符模式。

### 4. 统一编码处理
```python
# 先解码，再验证
decoded = url_decode(input)
sanitized = sanitize(decoded)
```

---

## 学习要点

1. **分层验证的重要性**
   - Z3 验证具体实现是否存在漏洞
   - TLA+ 验证架构设计是否正确
   - 两者结合才能全面保障安全

2. **形式化方法的优势**
   - 🔍 穷举所有可能的输入组合
   - 📋 提供精确的漏洞复现路径
   - ✅ 数学证明修复方案的正确性

3. **实际应用场景**
   - **Z3**: WAF规则审计、渗透测试工具开发
   - **TLA+**: 云存储系统设计、容器沙箱验证

---

## 延伸阅读

- [Path Traversal - OWASP](https://owasp.org/www-community/attacks/Path_Traversal)
- [Z3 String Theory](https://z3prover.github.io/api/html/z3py_8py_source.html)
- [TLA+ PlusCal Tutorial](https://lamport.azurewebsites.net/tla/pluscal.html)
- [Docker Security - Path Traversal](https://docs.docker.com/engine/security/)
