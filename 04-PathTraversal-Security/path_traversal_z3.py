#!/usr/bin/env python3
"""
Path Traversal (Directory Traversal) 漏洞检测 - Z3 实现层 FV

场景：验证文件路径过滤器是否存在逻辑死角
核心：利用 Z3 的 String 理论逆向推导绕过 payload
"""

from z3 import Solver, String, StringVal, Replace, Contains, Length, sat


def check_simple_replace_bypass():
    """
    检测场景 1：简单替换过滤的绕过
    
    防御逻辑：将 "../" 替换为空字符串
    攻击目标：找到输入，使得替换后依然包含 "../"
    """
    print("=" * 70)
    print("场景 1: 简单替换过滤绕过检测")
    print("防御逻辑: input.replace('../', '')")
    print("=" * 70)

    s = Solver()
    
    # 定义符号变量：黑客输入的恶意路径
    user_input = String('user_input')
    
    # 模拟防御逻辑
    sanitized = Replace(user_input, StringVal("../"), StringVal(""))
    
    # 攻击目标：过滤后依然包含 "../"
    bypass_condition = Contains(sanitized, StringVal("../"))
    
    # 添加约束
    s.add(bypass_condition)
    s.add(Length(user_input) < 15)
    s.add(Length(user_input) > 3)
    
    print("\n正在计算是否存在绕过路径...")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        result = payload.replace("../", "")
        
        print(f"\n🚨 找到绕过漏洞！")
        print(f"   攻击输入 (Payload): {repr(payload)}")
        print(f"   过滤后结果:         {repr(result)}")
        print(f"\n原理分析:")
        print(f"   输入 '{payload}' 经过替换后变成 '{result}'")
        print(f"   双写构造使得过滤后重新生成了 '../'")
        return True, payload
    else:
        print("✅ 该逻辑在当前约束下是安全的")
        return False, None


def check_double_decode_bypass():
    """
    检测场景 2：URL 解码顺序问题
    
    防御逻辑：先过滤 "../"，然后 URL 解码
    攻击目标：找到编码后的输入，解码后形成 "../"
    """
    print("\n" + "=" * 70)
    print("场景 2: URL 解码顺序绕过检测")
    print("防御逻辑: sanitize(input) -> url_decode(input)")
    print("=" * 70)

    s = Solver()
    
    user_input = String('user_input')
    
    # 模拟防御逻辑：先替换 ../，然后解码
    # 注意：这里我们简化模型，假设 %2e = ., %2f = /
    step1 = Replace(user_input, StringVal("../"), StringVal(""))
    
    # 模拟 URL 解码：%2e%2e%2f -> ../
    step2 = Replace(step1, StringVal("%2e%2e%2f"), StringVal("../"))
    step2 = Replace(step2, StringVal("%2e%2e/"), StringVal("../"))
    step2 = Replace(step2, StringVal("..%2f"), StringVal("../"))
    
    # 攻击目标：最终包含 "../"
    bypass_condition = Contains(step2, StringVal("../"))
    
    s.add(bypass_condition)
    s.add(Length(user_input) < 30)
    s.add(Length(user_input) > 5)
    
    print("\n正在计算是否存在绕过路径...")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        
        print(f"\n🚨 找到绕过漏洞！")
        print(f"   攻击输入 (Payload): {repr(payload)}")
        print(f"\n原理分析:")
        print(f"   编码形式的 '../' 绕过了第一层的字符串替换")
        print(f"   URL 解码后重新生成了 '../'")
        return True, payload
    else:
        print("✅ 该逻辑在当前约束下是安全的")
        return False, None


def check_null_byte_bypass():
    """
    检测场景 3：空字节截断 (Null Byte Injection)
    
    防御逻辑：检查文件扩展名
    攻击目标：使用空字节截断绕过扩展名检查
    """
    print("\n" + "=" * 70)
    print("场景 3: 空字节截断绕过检测")
    print("防御逻辑: 检查扩展名是否为 .jpg/.png")
    print("=" * 70)

    s = Solver()
    
    user_input = String('user_input')
    
    # 模拟防御逻辑：检查后缀
    # 漏洞：某些系统在处理文件名时会被空字节截断
    # file.jpg%00.php 被检查为 .jpg，实际处理为 file.jpg
    
    # 构造条件：输入包含 .jpg 后缀，但空字节后有危险内容
    has_safe_ext = Contains(user_input, StringVal(".jpg"))
    has_null = Contains(user_input, StringVal("\x00"))
    
    s.add(has_safe_ext)
    s.add(has_null)
    s.add(Length(user_input) < 50)
    
    print("\n正在计算是否存在绕过路径...")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        
        print(f"\n🚨 找到绕过漏洞！")
        print(f"   攻击输入 (Payload): {repr(payload)}")
        print(f"\n原理分析:")
        print(f"   空字节 (%00) 会导致 C 语言风格的字符串截断")
        print(f"   扩展名检查看到的是 .jpg，实际处理被截断")
        return True, payload
    else:
        print("✅ 该逻辑在当前约束下是安全的")
        return False, None


def check_overlong_utf8_bypass():
    """
    检测场景 4：UTF-8 过度编码绕过
    
    防御逻辑：过滤 "../"
    攻击目标：使用 UTF-8 过度编码绕过
    """
    print("\n" + "=" * 70)
    print("场景 4: UTF-8 过度编码绕过检测")
    print("防御逻辑: 简单的字符串匹配过滤")
    print("=" * 70)

    s = Solver()
    
    user_input = String('user_input')
    
    # 模拟防御逻辑
    sanitized = Replace(user_input, StringVal("../"), StringVal(""))
    
    # 模拟 UTF-8 解码后的结果
    # %c0%ae = 过度编码的 .
    # %c0%af = 过度编码的 /
    decoded = Replace(sanitized, StringVal("%c0%ae%c0%ae%c0%af"), StringVal("../"))
    
    bypass_condition = Contains(decoded, StringVal("../"))
    
    s.add(bypass_condition)
    s.add(Length(user_input) < 50)
    
    print("\n正在计算是否存在绕过路径...")
    
    if s.check() == sat:
        m = s.model()
        payload = m[user_input].as_string()
        
        print(f"\n🚨 找到绕过漏洞！")
        print(f"   攻击输入 (Payload): {repr(payload)}")
        print(f"\n原理分析:")
        print(f"   UTF-8 过度编码可以绕过简单的字符串匹配")
        print(f"   解码后重新生成恶意字符")
        return True, payload
    else:
        print("✅ 该逻辑在当前约束下是安全的")
        return False, None


def main():
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║     Z3 Path Traversal 漏洞检测器 - 形式化验证实战                    ║
║                                                                      ║
║  使用 SMT Solver 逆向推导路径穿越绕过 payload                        ║
╚══════════════════════════════════════════════════════════════════════╝
""")
    
    vulnerabilities = []
    
    # 运行所有检测场景
    vulns = [
        check_simple_replace_bypass(),
        check_double_decode_bypass(),
        check_null_byte_bypass(),
        check_overlong_utf8_bypass(),
    ]
    
    for found, payload in vulns:
        if found:
            vulnerabilities.append(payload)
    
    # 总结
    print("\n" + "=" * 70)
    print("扫描总结")
    print("=" * 70)
    
    if vulnerabilities:
        print(f"\n🔴 发现 {len(vulnerabilities)} 个绕过漏洞！")
        print("\n建议修复方案:")
        print("  1. 使用规范化的路径解析（如 realpath/getCanonicalPath）")
        print("  2. 验证最终路径是否在允许目录内")
        print("  3. 不要依赖黑名单过滤，使用白名单验证")
        print("  4. 统一编码处理（先解码再验证）")
    else:
        print("\n🟢 未发现明显漏洞")


if __name__ == "__main__":
    main()
