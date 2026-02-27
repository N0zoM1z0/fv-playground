#!/usr/bin/env python3
"""
IAM 权限策略验证 - Z3 在 Web2 的核心应用

场景：验证复杂的云权限策略是否存在配置错误
参考：AWS Zelkova 使用 SMT Solver 验证 S3 Bucket 策略

核心问题：当策略叠加了几百条时，人脑根本算不清楚"User A 到底能不能删库"
"""

from z3 import Solver, Bool, And, Or, Not, sat, Implies


def check_iam_policy_conflict():
    """
    检测场景 1：Allow 和 Deny 策略冲突
    
    问题：显式 Deny 应该优先于 Allow，但配置错误可能导致意外访问
    """
    print("=" * 70)
    print("场景 1: IAM 策略冲突检测")
    print("=" * 70)
    
    s = Solver()
    
    # 定义变量
    is_admin = Bool('is_admin')
    is_work_hours = Bool('is_work_hours')
    is_internal_ip = Bool('is_internal_ip')
    resource_is_sensitive = Bool('resource_is_sensitive')
    action_is_delete = Bool('action_is_delete')
    
    # 策略 1：Allow - 管理员在工作时间可以访问任何资源
    allow_admin = And(is_admin, is_work_hours)
    
    # 策略 2：Deny - 敏感资源禁止删除（任何人）
    deny_sensitive_delete = And(resource_is_sensitive, action_is_delete)
    
    # 策略 3：Allow - 内网 IP 可以访问敏感资源
    allow_internal_sensitive = And(is_internal_ip, resource_is_sensitive)
    
    # 检查：是否存在一种情况，用户被 Allow 访问敏感资源，但不应该被允许？
    # 攻击场景：内网用户尝试删除敏感资源
    
    # 约束：用户在内网，尝试删除敏感资源
    s.add(is_internal_ip)
    s.add(resource_is_sensitive)
    s.add(action_is_delete)
    
    # 检查：这个操作是否被允许？（应该被 Deny 阻止）
    # 根据 AWS IAM 规则：显式 Deny > Allow
    is_allowed = Or(allow_admin, allow_internal_sensitive)
    is_denied = deny_sensitive_delete
    
    # 漏洞：如果 Deny 没有正确生效，就会出现未授权访问
    # 我们检查是否存在 "被 Allow 且没有被 Deny" 的情况
    bypass = And(is_allowed, Not(is_denied))
    
    s.add(bypass)
    
    print("\n检查：内网用户能否删除敏感资源？")
    print("策略: Allow(内网访问敏感资源) + Deny(删除敏感资源)")
    
    if s.check() == sat:
        print("\n🚨 发现策略配置错误！")
        m = s.model()
        print(f"   is_admin: {m[is_admin]}")
        print(f"   is_work_hours: {m[is_work_hours]}")
        print(f"   is_internal_ip: {m[is_internal_ip]}")
        print("\n分析：Deny 策略没有正确生效，用户可能越权操作！")
    else:
        print("\n✅ 策略配置正确，Deny 优先于 Allow")


def check_abac_policy_vulnerability():
    """
    检测场景 2：ABAC (Attribute-Based Access Control) 漏洞
    
    问题：基于属性的访问控制可能存在属性组合绕过
    """
    print("\n" + "=" * 70)
    print("场景 2: ABAC 属性组合绕过检测")
    print("=" * 70)
    
    s = Solver()
    
    # 用户属性
    user_department = Bool('user_department')  # 是否财务部
    user_level = Bool('user_level')            # 是否高级别
    user_location = Bool('user_location')      # 是否在公司
    
    # 资源属性
    resource_type = Bool('resource_type')      # 是否财务数据
    resource_classification = Bool('resource_classification')  # 是否机密
    
    # 环境属性
    env_time = Bool('env_time')                # 是否工作时间
    env_location = Bool('env_location')        # 是否在公司网络
    
    # ABAC 策略：访问财务机密数据需要
    # (财务部 AND 高级别 AND 工作时间 AND 公司网络)
    should_allow = And(
        user_department,
        user_level,
        env_time,
        env_location
    )
    
    # 检查：是否存在属性组合可以绕过这个策略？
    # 攻击场景：非财务部用户能否访问财务数据？
    
    s.add(Not(user_department))  # 非财务部用户
    s.add(resource_type)         # 尝试访问财务数据
    s.add(resource_classification)  # 机密数据
    
    # 漏洞：如果系统只检查部分属性，可能被绕过
    # 假设系统有漏洞：只检查 user_level 和 env_time
    vulnerable_check = And(user_level, env_time)
    
    s.add(vulnerable_check)
    
    print("\n检查：非财务部用户能否访问财务机密数据？")
    print("策略: 需要(财务部 AND 高级别 AND 工作时间 AND 公司网络)")
    print("漏洞: 系统只检查了(高级别 AND 工作时间)")
    
    if s.check() == sat:
        print("\n🚨 发现 ABAC 绕过漏洞！")
        m = s.model()
        print(f"   user_department: {m[user_department]} (非财务部)")
        print(f"   user_level: {m[user_level]} (高级别)")
        print(f"   env_time: {m[env_time]} (工作时间)")
        print("\n分析：属性检查不完整，非财务部用户可以访问财务数据！")
    else:
        print("\n✅ ABAC 策略配置正确")


def check_privilege_escalation():
    """
    检测场景 3：权限提升路径
    
    问题：通过一系列操作组合，低权限用户能否获得高权限？
    """
    print("\n" + "=" * 70)
    print("场景 3: 权限提升路径检测")
    print("=" * 70)
    
    s = Solver()
    
    # 定义操作
    can_read_user = Bool('can_read_user')
    can_write_temp = Bool('can_write_temp')
    can_execute_script = Bool('can_execute_script')
    can_modify_config = Bool('can_modify_config')
    can_grant_admin = Bool('can_grant_admin')
    
    # 权限依赖关系
    # 如果能读用户数据 + 写临时文件 + 执行脚本 → 可能修改配置
    exploit_1 = And(can_read_user, can_write_temp, can_execute_script)
    
    # 如果能修改配置 → 可能获得授权管理权限
    exploit_2 = And(can_modify_config, can_execute_script)
    
    # 最终目标：获得管理员授权权限
    can_escalate = Or(
        And(exploit_1, can_modify_config),
        exploit_2,
        can_grant_admin
    )
    
    # 低权限用户通常拥有的权限
    s.add(can_read_user)       # 可以读用户数据
    s.add(can_write_temp)      # 可以写临时文件
    s.add(can_execute_script)  # 可以执行脚本
    
    # 检查：通过这些权限能否提升到管理员？
    s.add(Not(can_grant_admin))  # 目前没有直接授权权限
    s.add(Not(can_modify_config))  # 目前不能修改配置
    
    # 检查是否存在权限提升路径
    s.add(can_escalate)
    
    print("\n检查：低权限用户能否通过操作组合提升为管理员？")
    print("用户权限: 读用户数据 + 写临时文件 + 执行脚本")
    print("攻击链: 读数据 → 写恶意脚本 → 执行 → 修改配置 → 授权管理")
    
    if s.check() == sat:
        print("\n🚨 发现权限提升路径！")
        print("\n攻击步骤:")
        print("  1. 读取用户数据获取系统信息")
        print("  2. 写入恶意脚本到临时目录")
        print("  3. 执行脚本利用系统漏洞")
        print("  4. 修改配置文件获得更高权限")
        print("  5. 最终获得管理员授权能力")
    else:
        print("\n✅ 不存在权限提升路径")


def check_temporary_permissions():
    """
    检测场景 4：临时权限滥用
    
    问题：临时提升的权限没有及时回收，被恶意利用
    """
    print("\n" + "=" * 70)
    print("场景 4: 临时权限滥用检测")
    print("=" * 70)
    
    s = Solver()
    
    # 时间变量
    t1_has_temp_access = Bool('t1_has_temp_access')  # 时间点1有临时权限
    t2_should_revoke = Bool('t2_should_revoke')       # 时间点2应该回收
    t2_actually_revoked = Bool('t2_actually_revoked') # 时间点2实际回收
    t3_user_action = Bool('t3_user_action')           # 时间点3用户操作
    
    # 策略：临时权限必须在时间点后回收
    policy_obeyed = Implies(t2_should_revoke, t2_actually_revoked)
    
    # 漏洞场景：应该回收但没有回收，用户继续操作
    vulnerability = And(
        t1_has_temp_access,
        t2_should_revoke,
        Not(t2_actually_revoked),
        t3_user_action
    )
    
    s.add(vulnerability)
    
    print("\n检查：临时权限是否存在未及时回收的漏洞？")
    print("策略: 临时权限必须在指定时间后回收")
    
    if s.check() == sat:
        print("\n🚨 发现临时权限滥用漏洞！")
        print("\n漏洞场景:")
        print("  T1: 用户获得临时权限")
        print("  T2: 应该回收权限，但实际未回收")
        print("  T3: 用户继续使用权限执行操作")
        print("\n风险：权限回收机制存在延迟或漏洞")
    else:
        print("\n✅ 临时权限回收机制正常")


def main():
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║     IAM 权限策略验证器 - Web2 FV 核心应用                            ║
║                                                                      ║
║  参考：AWS Zelkova / Azure Policy Verification                       ║
╚══════════════════════════════════════════════════════════════════════╝
""")
    
    # 运行所有检测场景
    check_iam_policy_conflict()
    check_abac_policy_vulnerability()
    check_privilege_escalation()
    check_temporary_permissions()
    
    # 总结
    print("\n" + "=" * 70)
    print("总结")
    print("=" * 70)
    print("""
Z3 在 IAM/权限验证中的核心价值：

1. 策略冲突检测
   - 自动发现 Allow/Deny 策略的冲突
   - 验证显式 Deny 是否正确优先

2. ABAC 属性组合验证
   - 检查属性条件是否完备
   - 发现属性组合绕过可能

3. 权限提升路径分析
   - 建模权限依赖关系
   - 发现间接权限提升路径

4. 时序权限验证
   - 验证临时权限生命周期
   - 检测权限回收漏洞

实际应用：
- AWS S3 Bucket 策略验证 (Zelkova)
- Azure RBAC 配置检查
- Kubernetes RBAC 审计
- 企业内部权限治理
""")


if __name__ == "__main__":
    main()
