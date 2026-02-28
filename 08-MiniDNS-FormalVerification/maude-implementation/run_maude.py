#!/usr/bin/env python3
"""
Maude DNS Implementation Runner
使用 Python Maude 绑定加载和执行 Maude 代码
"""

import maude
import sys
from pathlib import Path

def load_maude_module(filepath: str) -> bool:
    """加载 Maude 模块文件"""
    try:
        result = maude.load(filepath)
        if result:
            print(f"✅ Loaded: {filepath}")
            return True
        else:
            print(f"❌ Failed to load: {filepath}")
            return False
    except Exception as e:
        print(f"❌ Error loading {filepath}: {e}")
        return False

def get_module(name: str):
    """获取 Maude 模块"""
    return maude.getModule(str(name))

def test_basic_types():
    """测试基础类型模块"""
    print("\n" + "="*70)
    print("Testing DNS-TYPES Module")
    print("="*70)
    
    mod = get_module('DNS-TYPES-TEST')
    if not mod:
        print("❌ DNS-TYPES-TEST module not found")
        return False
    
    # 测试域名构造
    try:
        # 解析测试项
        test_domain = mod.parseTerm('testDomain')
        print(f"✅ Test domain: {test_domain}")
        
        test_record = mod.parseTerm('testRecord')
        print(f"✅ Test record: {test_record}")
        
        test_query = mod.parseTerm('testQuery')
        print(f"✅ Test query: {test_query}")
        
        return True
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def test_actors():
    """测试 Actor 模块"""
    print("\n" + "="*70)
    print("Testing DNS-ACTORS Module")
    print("="*70)
    
    mod = get_module('DNS-ACTORS-TEST')
    if not mod:
        print("❌ DNS-ACTORS-TEST module not found")
        return False
    
    try:
        test_config = mod.parseTerm('testConfig')
        print(f"✅ Test configuration created")
        print(f"   Config size: {len(str(test_config))} chars")
        return True
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def test_rules():
    """测试重写规则"""
    print("\n" + "="*70)
    print("Testing DNS-RULES Module")
    print("="*70)
    
    mod = get_module('DNS-RULES-TEST')
    if not mod:
        print("❌ DNS-RULES-TEST module not found")
        return False
    
    try:
        # 解析测试配置
        test_config = mod.parseTerm('simpleTest')
        print(f"✅ Initial configuration:")
        print(f"   {test_config}")
        
        # 尝试一步重写
        print("\n   Attempting rewrite...")
        result = test_config.reduce()
        print(f"   Reduced: {result}")
        
        return True
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def main():
    print("="*70)
    print("Maude DNS Formal Verification Implementation")
    print("="*70)
    print(f"Maude version: {maude.MAUDE_VERSION}")
    
    # 获取脚本所在目录
    script_dir = Path(__file__).parent
    
    # 加载模块
    modules = [
        script_dir / 'dns-types.maude',
        script_dir / 'dns-actors.maude',
        script_dir / 'dns-rules.maude',
    ]
    
    print("\n" + "="*70)
    print("Loading Maude Modules")
    print("="*70)
    
    all_loaded = True
    for mod_file in modules:
        if not load_maude_module(str(mod_file)):
            all_loaded = False
    
    if not all_loaded:
        print("\n❌ Some modules failed to load")
        return 1
    
    # 运行测试
    print("\n" + "="*70)
    print("Running Tests")
    print("="*70)
    
    results = []
    results.append(("DNS-TYPES", test_basic_types()))
    results.append(("DNS-ACTORS", test_actors()))
    results.append(("DNS-RULES", test_rules()))
    
    # 总结
    print("\n" + "="*70)
    print("Test Summary")
    print("="*70)
    
    for name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"   {status}: {name}")
    
    all_passed = all(r[1] for r in results)
    
    print("\n" + "="*70)
    if all_passed:
        print("All tests passed!")
    else:
        print("Some tests failed.")
    print("="*70)
    
    return 0 if all_passed else 1

if __name__ == '__main__':
    sys.exit(main())
