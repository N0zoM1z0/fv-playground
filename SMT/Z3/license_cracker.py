#!/usr/bin/env python3
"""
Z3 License Key 破解器 - 入门挑战
通过多重 if-else 验证的 Key，用 Z3 逆向求解
"""

from z3 import Solver, BitVec, And, Or, sat, simplify


def verify_license_key(key_bytes):
    """
    模拟一个软件 License Key 验证算法
    key_bytes: 8 个字节的列表

    返回: (是否有效, 验证通过的阶段列表)
    """
    passed = []

    # 阶段 1: 基础格式检查
    # Key 必须以 "FV" 开头 (0x46, 0x56)
    if not (key_bytes[0] == 0x46 and key_bytes[1] == 0x56):
        return False, passed
    passed.append("Stage 1: Header check 'FV'")

    # 阶段 2: 校验和检查
    # 前 6 个字节的和必须等于第 7 个字节
    checksum = sum(key_bytes[:6]) % 256
    if key_bytes[6] != checksum:
        return False, passed
    passed.append("Stage 2: Checksum valid")

    # 阶段 3: 魔数验证
    # 第 3、4 字节组成的 16 位数必须满足特定条件
    magic = (key_bytes[2] << 8) | key_bytes[3]
    if not (magic % 7 == 3 and magic % 5 == 2):
        return False, passed
    passed.append("Stage 3: Magic number valid")

    # 阶段 4: 复杂条件链
    # 第 5 字节必须满足多重 if-else 条件
    b5 = key_bytes[4]
    if b5 < 0x30:
        return False, passed
    elif b5 < 0x40:
        if b5 % 2 != 0:
            return False, passed
    elif b5 < 0x60:
        if b5 % 3 != 1:
            return False, passed
    elif b5 < 0x80:
        if (b5 & 0x0F) != 0x05:
            return False, passed
    else:
        return False, passed
    passed.append("Stage 4: Complex condition chain valid")

    # 阶段 5: 最终验证
    # 所有字节的异或必须等于 0xFF
    xor_result = 0
    for b in key_bytes[:7]:
        xor_result ^= b
    if key_bytes[7] != xor_result:
        return False, passed
    passed.append("Stage 5: XOR checksum valid")

    return True, passed


def crack_license_key():
    """
    使用 Z3 逆向求解有效的 License Key
    """
    solver = Solver()

    # 创建 8 个 8 位无符号整数变量
    key = [BitVec(f"key_{i}", 8) for i in range(8)]

    # 约束 1: 阶段 1 - 必须以 "FV" 开头
    solver.add(key[0] == 0x46)  # 'F'
    solver.add(key[1] == 0x56)  # 'V'

    # 约束 2: 阶段 2 - 校验和
    # key[6] == sum(key[0:6]) % 256
    solver.add(key[6] == (key[0] + key[1] + key[2] + key[3] + key[4] + key[5]))

    # 约束 3: 阶段 3 - 魔数验证
    # magic = (key[2] << 8) | key[3]
    # magic % 7 == 3 and magic % 5 == 2
    magic = (key[2] << 8) | key[3]
    solver.add(magic % 7 == 3)
    solver.add(magic % 5 == 2)

    # 约束 4: 阶段 4 - 复杂条件链
    # 用 Or 表达多个可能的分支
    b5 = key[4]

    # 分支 1: 0x30 <= b5 < 0x40 且 b5 % 2 == 0
    branch1 = And(b5 >= 0x30, b5 < 0x40, b5 % 2 == 0)

    # 分支 2: 0x40 <= b5 < 0x60 且 b5 % 3 == 1
    branch2 = And(b5 >= 0x40, b5 < 0x60, b5 % 3 == 1)

    # 分支 3: 0x60 <= b5 < 0x80 且 (b5 & 0x0F) == 0x05
    branch3 = And(b5 >= 0x60, b5 < 0x80, (b5 & 0x0F) == 0x05)

    solver.add(Or(branch1, branch2, branch3))

    # 约束 5: 阶段 5 - 最终 XOR 校验
    # key[7] == XOR(key[0:7])
    solver.add(key[7] == (key[0] ^ key[1] ^ key[2] ^ key[3] ^ key[4] ^ key[5] ^ key[6]))

    # 求解
    print("正在使用 Z3 破解 License Key...")
    print("=" * 50)

    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(8):
            val = model.evaluate(key[i])
            # 简化并转换为整数
            solution.append(val.as_long() if hasattr(val, 'as_long') else int(str(val)))

        return solution
    else:
        return None


def format_key(key_bytes):
    """格式化 Key 为可读形式"""
    hex_str = ''.join(f'{b:02X}' for b in key_bytes)
    ascii_str = ''.join(chr(b) if 32 <= b < 127 else '.' for b in key_bytes)
    return f"Hex: {hex_str} | ASCII: {ascii_str}"


def main():
    print("=" * 60)
    print("     Z3 SMT 破解器 - License Key 逆向工程")
    print("=" * 60)

    # 先展示验证算法的结构
    print("\n[目标程序] License Key 验证算法结构:")
    print("-" * 60)
    print("""
    Stage 1: Header check
        key[0] == 'F' (0x46) AND key[1] == 'V' (0x56)

    Stage 2: Checksum
        key[6] == sum(key[0:6]) % 256

    Stage 3: Magic number
        magic = (key[2] << 8) | key[3]
        magic % 7 == 3 AND magic % 5 == 2

    Stage 4: Complex condition chain
        Branch 1: 0x30 <= key[4] < 0x40 AND key[4] % 2 == 0
        Branch 2: 0x40 <= key[4] < 0x60 AND key[4] % 3 == 1
        Branch 3: 0x60 <= key[4] < 0x80 AND (key[4] & 0x0F) == 0x05

    Stage 5: Final XOR
        key[7] == XOR(key[0:7])
    """)
    print("-" * 60)

    # 使用 Z3 破解
    key = crack_license_key()

    if key:
        print(f"\n[成功] 找到有效 License Key!")
        print(f"       {format_key(key)}")

        # 验证破解结果
        print("\n[验证] 用原始算法验证破解结果:")
        valid, stages = verify_license_key(key)
        for stage in stages:
            print(f"       ✓ {stage}")

        if valid:
            print(f"\n       ★ Key 完全有效! ★")

        # 展示字节分解
        print("\n[详细分析] Key 字节分解:")
        print(f"       Byte 0-1 (Header):  {key[0]:02X} {key[1]:02X} = 'FV'")
        print(f"       Byte 2-3 (Magic):   {key[2]:02X} {key[3]:02X} = {(key[2] << 8) | key[3]:04X}")
        print(f"       Byte 4 (Condition): {key[4]:02X}")
        print(f"       Byte 5 (Free):      {key[5]:02X}")
        print(f"       Byte 6 (Checksum):  {key[6]:02X} (calculated)")
        print(f"       Byte 7 (XOR):       {key[7]:02X} (calculated)")
    else:
        print("[失败] 无解!")


if __name__ == "__main__":
    main()
