#!/usr/bin/env python3
"""
Basic Maude test
"""

import maude

print(f"Maude version: {maude.MAUDE_VERSION}")
print()

# 创建一个简单的模块测试
test_code = """
fmod TEST is
    protecting INT .
    
    sort Foo .
    op bar : Int -> Foo [ctor] .
    op add : Foo Foo -> Foo .
    
    vars X Y : Int .
    eq add(bar(X), bar(Y)) = bar(X + Y) .
endfm

mod TEST-MOD is
    protecting TEST .
    
    op test1 : -> Foo .
    eq test1 = bar(5) .
    
    op test2 : -> Foo .
    eq test2 = add(bar(3), bar(4)) .
endm
"""

# 创建临时文件
import tempfile
import os

with tempfile.NamedTemporaryFile(mode='w', suffix='.maude', delete=False) as f:
    f.write(test_code)
    temp_file = f.name

try:
    print(f"Loading test file: {temp_file}")
    result = maude.load(temp_file)
    print(f"Load result: {result}")
    
    # 获取模块
    mod = maude.getModule('TEST-MOD')
    if mod:
        print("\nModule TEST-MOD found!")
        
        # 解析项
        t1 = mod.parseTerm('test1')
        print(f"test1 = {t1}")
        
        t2 = mod.parseTerm('test2')
        print(f"test2 = {t2}")
        
        # 归约
        t2.reduce()
        print(f"test2 reduced = {t2}")
    else:
        print("Module not found")
        print("Available modules:")
        # 尝试列出模块
        
finally:
    os.unlink(temp_file)
