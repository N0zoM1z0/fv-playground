#!/usr/bin/env python3
"""
Test Maude with inline module creation
"""

import maude
import tempfile
import os

print(f"Maude version: {maude.MAUDE_VERSION}")

# 检查是否有 maude 命令行工具
import subprocess
result = subprocess.run(['which', 'maude'], capture_output=True, text=True)
print(f"maude CLI: {result.stdout.strip() if result.returncode == 0 else 'not found'}")

# 尝试内联创建模块
print("\n--- Testing inline module creation ---")

# 创建临时文件
test_code = b"""
fmod NAT is
  sort Nat .
  op zero : -> Nat [ctor] .
  op s : Nat -> Nat [ctor] .
  op add : Nat Nat -> Nat .
  var X Y : Nat .
  eq add(zero, X) = X .
  eq add(s(X), Y) = s(add(X, Y)) .
endfm
"""

with tempfile.NamedTemporaryFile(suffix='.maude', delete=False) as f:
    f.write(test_code)
    temp_file = f.name

print(f"Created temp file: {temp_file}")
print(f"Content: {test_code.decode()}")

try:
    print("\nAttempting to load...")
    success = maude.load(temp_file)
    print(f"Load success: {success}")
    
    if success:
        mod = maude.getModule('NAT')
        print(f"Module NAT: {mod}")
        
except Exception as e:
    print(f"Error: {type(e).__name__}: {e}")
    import traceback
    traceback.print_exc()
    
finally:
    os.unlink(temp_file)
