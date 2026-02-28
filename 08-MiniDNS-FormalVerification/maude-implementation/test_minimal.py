#!/usr/bin/env python3
"""
Minimal Maude test - no imports
"""

import maude

print(f"Maude version: {maude.MAUDE_VERSION}")
print()

# 最简单的测试 - 不使用任何导入
test_code = """
fmod MINIMAL is
    sort Nat .
    op zero : -> Nat [ctor] .
    op s : Nat -> Nat [ctor] .
    
    op add : Nat Nat -> Nat .
    
    vars X Y : Nat .
    eq add(zero, X) = X .
    eq add(s(X), Y) = s(add(X, Y)) .
endfm
"""

import tempfile
import os

with tempfile.NamedTemporaryFile(mode='w', suffix='.maude', delete=False) as f:
    f.write(test_code)
    temp_file = f.name

try:
    print(f"Loading: {temp_file}")
    result = maude.load(temp_file)
    print(f"Result: {result}")
    
    mod = maude.getModule('MINIMAL')
    if mod:
        print("\n✅ Module MINIMAL loaded!")
        
        # 测试归约
        t = mod.parseTerm('add(s(s(zero)), s(zero))')
        print(f"Term: {t}")
        t.reduce()
        print(f"Reduced: {t}")
    else:
        print("\n❌ Module not found")
        
finally:
    os.unlink(temp_file)
