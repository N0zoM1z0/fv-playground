#!/usr/bin/env python3
"""
WAF 规则逻辑完备性验证 - FV 在 Web 安全的核心应用

场景：验证 WAF 规则是否能被绕过
核心：用 Z3 验证 "是否存在字符串既包含攻击特征，又能通过 WAF 规则"

这是 FV 在 Web2 安全中最实际的应用之一！
"""

from z3 import Solver, String, StringVal, Contains, And, Or, Not, sat, Length
import re


def check_sql_injection_bypass():
    """
    检测场景 1：SQL 注入 WAF 规则绕过
    
    验证：简单的关键字黑名单是否能被绕过
    """
    print("=" * 70)
    print("场景 1: SQL 注入 WAF 规则绕过检测")
    print("=" * 70)
    
    s = Solver()
    
    # 定义符号变量：攻击者输入
    user_input = String('user_input')
    
    # 模拟 WAF 规则：简单的关键字黑名单
    # 规则：如果包含 "SELECT" 或 "UNION" 或 "DROP" 就拦截
    has_select = Contains(user_input, StringVal("SELECT"))
    has_union = Contains(user_input, StringVal("UNION"))
    has_drop = Contains(user_input, StringVal("DROP"))
    
    # WAF 拦截条件
    waf_blocks = Or(has_select, has_union, has_drop)
    
    # 攻击目标：构造 SQL 注入 payload
    # 需要包含 SQL 关键字的功能，但绕过 WAF 检测
    
    # 方法 1：大小写绕过
    has_select_lower = Contains(user_input, StringVal("select"))
    has_select_upper = Contains(user_input, StringVal("SELECT"))
    has_select_mixed = Contains(user_input, StringVal("SeLeCt"))
    
    # 方法 2：注释绕过
    # SEL/**/ECT
    has_comment_select = Contains(user_input, StringVal("SEL/**/ECT"))
    
    # 方法 3：编码绕过
    # %53%45%4C%45%43%54 (URL 编码)
    has_encoded_select = Contains(user_input, StringVal("%53%45%4C%45%43%54"))
    
    # 攻击 payload 必须能实现 SQL 注入
    is_sqli = Or(
        has_select_lower,
        has_select_mixed,
        has_comment_select,
        has_encoded_select
    )
    
    # 检查：是否存在 payload 能注入但不被 WAF 拦截？
    s.add(is_sqli)           # 是 SQL 注入
    s.add(Not(waf_blocks))   # 但 WAF 不拦截
    
    s.add(Length(user_input) < 50)
    s.add(Length(user_input) > 5)
    
    print("\nWAF 规则: 拦截包含 SELECT/UNION/DROP 的请求")
    print("\n检查：是否存在能绕过 WAF 的 SQL 注入 payload？")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        print(f"\n🚨 发现 WAF 绕过漏洞！")
        print(f"   Payload: {repr(payload)}")
        print(f"\n绕过技术分析:")
        if "SEL/**/ECT" in payload:
            print("   - 使用注释分割关键字")
        elif "%53" in payload:
            print("   - 使用 URL 编码")
        elif payload.upper() != payload:
            print("   - 使用大小写混合")
    else:
        print("\n✅ WAF 规则在当前约束下有效")


def check_xss_bypass():
    """
    检测场景 2：XSS WAF 规则绕过
    """
    print("\n" + "=" * 70)
    print("场景 2: XSS WAF 规则绕过检测")
    print("=" * 70)
    
    s = Solver()
    
    user_input = String('user_input')
    
    # 简单 WAF 规则：拦截 <script> 标签
    has_script_tag = Contains(user_input, StringVal("<script>"))
    waf_blocks = has_script_tag
    
    # XSS 替代方法
    # 方法 1：事件处理器
    has_onclick = Contains(user_input, StringVal("onclick"))
    has_onerror = Contains(user_input, StringVal("onerror"))
    
    # 方法 2：其他标签
    has_img_tag = Contains(user_input, StringVal("<img"))
    has_svg_tag = Contains(user_input, StringVal("<svg"))
    
    # 方法 3：编码
    has_encoded_script = Contains(user_input, StringVal("%3Cscript%3E"))
    
    # XSS payload 特征
    is_xss = Or(
        has_onclick,
        has_onerror,
        has_img_tag,
        has_svg_tag,
        has_encoded_script
    )
    
    s.add(is_xss)
    s.add(Not(waf_blocks))
    s.add(Length(user_input) < 100)
    
    print("\nWAF 规则: 拦截 <script> 标签")
    print("\n检查：是否存在能绕过 WAF 的 XSS payload？")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        print(f"\n🚨 发现 WAF 绕过漏洞！")
        print(f"   Payload: {repr(payload)}")
        print(f"\n绕过技术分析:")
        if "onclick" in payload or "onerror" in payload:
            print("   - 使用事件处理器替代 script 标签")
        elif "<img" in payload or "<svg" in payload:
            print("   - 使用其他 HTML 标签")
        elif "%3C" in payload:
            print("   - 使用 URL 编码")
    else:
        print("\n✅ WAF 规则在当前约束下有效")


def check_command_injection_bypass():
    """
    检测场景 3：命令注入 WAF 规则绕过
    """
    print("\n" + "=" * 70)
    print("场景 3: 命令注入 WAF 规则绕过检测")
    print("=" * 70)
    
    s = Solver()
    
    user_input = String('user_input')
    
    # WAF 规则：拦截常见命令分隔符
    has_semicolon = Contains(user_input, StringVal(";"))
    has_pipe = Contains(user_input, StringVal("|"))
    has_and = Contains(user_input, StringVal("&&"))
    waf_blocks = Or(has_semicolon, has_pipe, has_and)
    
    # 命令注入替代方法
    # 方法 1：换行符
    has_newline = Contains(user_input, StringVal("\n"))
    
    # 方法 2：反引号
    has_backtick = Contains(user_input, StringVal("`"))
    
    # 方法 3：$() 命令替换
    has_dollar_paren = Contains(user_input, StringVal("$("))
    
    # 方法 4：编码绕过
    has_encoded_semicolon = Contains(user_input, StringVal("%3B"))
    
    is_cmdi = Or(
        has_newline,
        has_backtick,
        has_dollar_paren,
        has_encoded_semicolon
    )
    
    s.add(is_cmdi)
    s.add(Not(waf_blocks))
    s.add(Length(user_input) < 50)
    
    print("\nWAF 规则: 拦截 ; | && 等命令分隔符")
    print("\n检查：是否存在能绕过 WAF 的命令注入 payload？")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        print(f"\n🚨 发现 WAF 绕过漏洞！")
        print(f"   Payload: {repr(payload)}")
        print(f"\n绕过技术分析:")
        if "\n" in payload:
            print("   - 使用换行符替代分号")
        elif "`" in payload:
            print("   - 使用反引号执行命令")
        elif "$(" in payload:
            print("   - 使用 $() 命令替换")
        elif "%3B" in payload:
            print("   - 使用 URL 编码")
    else:
        print("\n✅ WAF 规则在当前约束下有效")


def check_waf_rule_completeness():
    """
    检测场景 4：WAF 规则完备性分析
    
    分析：给定攻击模式，WAF 规则是否覆盖了所有变体
    """
    print("\n" + "=" * 70)
    print("场景 4: WAF 规则完备性分析")
    print("=" * 70)
    
    print("\n攻击模式分析：路径穿越的所有可能形式")
    print("-" * 70)
    
    attack_patterns = [
        ("../", "基本形式"),
        ("..\\", "Windows 反斜杠"),
        ("....//", "双写绕过"),
        ("..././", "点斜杠混合"),
        ("%2e%2e%2f", "URL 编码"),
        ("%252e%252e%252f", "双重 URL 编码"),
        ("..%c0%af", "UTF-8 编码"),
        ("../../../", "多级穿越"),
    ]
    
    # 模拟 WAF 规则：只拦截 ../
    waf_pattern = "../"
    
    print(f"\nWAF 规则: 拦截 '{waf_pattern}'")
    print("\n攻击模式覆盖分析:")
    
    bypass_patterns = []
    for pattern, desc in attack_patterns:
        if waf_pattern not in pattern:
            bypass_patterns.append((pattern, desc))
            print(f"  ⚠️  未覆盖: {desc:20s} -> {pattern}")
        else:
            print(f"  ✅ 已覆盖: {desc:20s} -> {pattern}")
    
    print(f"\n分析结果:")
    print(f"  总攻击模式: {len(attack_patterns)}")
    print(f"  已覆盖: {len(attack_patterns) - len(bypass_patterns)}")
    print(f"  未覆盖: {len(bypass_patterns)}")
    
    if bypass_patterns:
        print(f"\n🚨 发现 {len(bypass_patterns)} 个未覆盖的攻击模式！")
        print("\n建议:")
        print("  1. 使用规范化（Canonicalization）而非黑名单")
        print("  2. 解码后再检测")
        print("  3. 使用语义分析而非字符串匹配")
    else:
        print("\n✅ 规则覆盖完整")


def main():
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║     WAF 规则逻辑完备性验证器 - Web 安全 FV 核心应用                  ║
║                                                                      ║
║  验证 WAF 规则是否能被绕过，发现规则逻辑死角                         ║
╚══════════════════════════════════════════════════════════════════════╝
""")
    
    # 运行所有检测场景
    check_sql_injection_bypass()
    check_xss_bypass()
    check_command_injection_bypass()
    check_waf_rule_completeness()
    
    # 总结
    print("\n" + "=" * 70)
    print("总结")
    print("=" * 70)
    print("""
FV 在 WAF 规则验证中的核心价值：

1. 规则绕过检测
   - 自动发现规则逻辑死角
   - 生成具体的绕过 payload

2. 规则完备性分析
   - 验证规则是否覆盖所有攻击变体
   - 发现编码、大小写等绕过方式

3. 规则冲突检测
   - 发现多条规则之间的逻辑冲突
   - 验证规则优先级是否正确

4. 规则优化建议
   - 基于形式化分析给出改进建议
   - 推荐使用规范化而非黑名单

实际应用：
- ModSecurity 规则审计
- 商业 WAF 规则测试
- 自研 WAF 规则验证
- 渗透测试工具开发
""")


if __name__ == "__main__":
    main()
