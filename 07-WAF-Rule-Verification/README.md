# 07-WAF-Rule-Verification

## 场景描述

**WAF 规则逻辑完备性验证 - Web 安全 FV 核心应用**

验证 WAF 规则是否能被绕过，发现规则逻辑死角

### 为什么这是 FV 的最佳应用场景

| 特性 | 说明 |
|-----|------|
| 规则验证 | WAF 规则本质上是字符串匹配逻辑 |
| 绕过发现 | 需要找到既包含攻击特征又能通过规则的字符串 |
| 完备性 | 需要验证规则是否覆盖所有攻击变体 |

### 核心思想

```
传统渗透测试：手动尝试各种 payload
Z3 FV 方法：定义"攻击特征"和"规则约束"，让求解器自动推导绕过方式
```

## 检测场景

### 场景 1：SQL 注入 WAF 绕过

```python
# WAF 规则：拦截包含 SELECT/UNION/DROP 的请求
has_select = Contains(user_input, StringVal("SELECT"))
waf_blocks = Or(has_select, has_union, has_drop)

# Z3 找到绕过：大小写混合 "SeLeCt"
```

### 场景 2：XSS WAF 绕过

```python
# WAF 规则：拦截 <script> 标签
has_script_tag = Contains(user_input, StringVal("<script>"))

# Z3 找到绕过：使用 <img onerror=...>
```

### 场景 3：命令注入 WAF 绕过

```python
# WAF 规则：拦截 ; | && 等命令分隔符
waf_blocks = Or(has_semicolon, has_pipe, has_and)

# Z3 找到绕过：使用反引号 `command`
```

### 场景 4：规则完备性分析

分析给定攻击模式，WAF 规则是否覆盖了所有变体

```
攻击模式：路径穿越
WAF 规则：拦截 '../'

未覆盖：
  - ..\\ (Windows 反斜杠)
  - %2e%2e%2f (URL 编码)
  - ..%c0%af (UTF-8 编码)
```

## 运行命令

```bash
cd /home/pentester/fv/fv-playground/07-WAF-Rule-Verification
python3 waf_rule_verification.py
```

## 学习要点

1. **Z3 String 理论的应用**
   - Contains, Replace, Length 等字符串操作
   - 结合布尔逻辑进行复杂规则建模

2. **实际应用价值**
   - 自动化 WAF 规则审计
   - 生成绕过 payload 用于渗透测试
   - 评估商业 WAF 的防护能力

3. **局限性**
   - 复杂正则表达式可能难以建模
   - 语义分析仍需人工辅助
   - 建议结合 Fuzzing 使用

4. **最佳实践**
   - 使用规范化（Canonicalization）而非黑名单
   - 解码后再检测
   - 多层防护策略
