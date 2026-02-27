# 05-IAM-Policy-Verification

## 场景描述

**IAM 权限策略验证 - Web2 FV 的核心应用**

参考：AWS Zelkova / Azure Policy Verification

### 核心问题

当云权限策略叠加了几百条时，人脑根本算不清楚 **"User A 到底能不能删库"**

### 为什么这是 Z3 的统治区

| 特性 | 说明 |
|-----|------|
| 布尔逻辑 | IAM 策略本质上是布尔表达式（Allow/Deny） |
| 约束求解 | 需要验证是否存在违反安全策略的访问路径 |
| 组合爆炸 | 多条策略组合后，人脑无法穷举所有情况 |

### 实际应用

- **AWS Zelkova**: AWS 使用 SMT Solver 实时验证 S3 Bucket 策略
- **Azure Policy**: 验证资源访问策略的正确性
- **Kubernetes RBAC**: 验证角色绑定是否存在越权

## 检测场景

### 场景 1：策略冲突检测

验证 Allow 和 Deny 策略是否正确处理（Deny 应该优先）

```python
# 策略 1：Allow - 管理员在工作时间可以访问任何资源
allow_admin = And(is_admin, is_work_hours)

# 策略 2：Deny - 敏感资源禁止删除（任何人）
deny_sensitive_delete = And(resource_is_sensitive, action_is_delete)
```

### 场景 2：ABAC 属性组合绕过

验证基于属性的访问控制是否存在属性组合绕过

```python
# 策略：访问财务机密数据需要
# (财务部 AND 高级别 AND 工作时间 AND 公司网络)
should_allow = And(
    user_department,
    user_level,
    env_time,
    env_location
)
```

### 场景 3：权限提升路径

通过一系列操作组合，低权限用户能否获得高权限？

```
读用户数据 → 写恶意脚本 → 执行 → 修改配置 → 授权管理
```

### 场景 4：临时权限滥用

临时提升的权限没有及时回收，被恶意利用

## 运行命令

```bash
cd /home/pentester/fv/fv-playground/05-IAM-Policy-Verification
python3 iam_policy_verification.py
```

## 学习要点

1. **Z3 在 IAM 中的优势**
   - 布尔约束求解完美匹配 IAM 策略模型
   - 自动发现策略冲突和绕过路径
   - 可扩展到数百条策略的复杂场景

2. **实际部署**
   - 集成到 CI/CD 流程中
   - 策略变更前自动验证
   - 生成人类可读的审计报告

3. **与其他工具对比**
   - 比人工审计更完整（穷举所有情况）
   - 比传统 SAST 更精确（针对策略逻辑）
   - 比渗透测试更前置（设计阶段发现）
