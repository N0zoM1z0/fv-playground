#!/usr/bin/env python3
"""
Z3 数独求解器 - 入门挑战
使用 SMT 求解器自动解数独谜题
"""

from z3 import Solver, Int, And, Distinct, sat


def solve_sudoku(puzzle):
    """
    使用 Z3 求解数独

    puzzle: 9x9 的二维列表，0 表示空白格

    约束:
    1. num -> 1~9
    2. row is not duplicated
    3. column
    4. 3x3
    5. known numbers
    """
    solver = Solver()

    # 创建 9x9 的整数变量矩阵
    cells = [[Int(f"cell_{i}_{j}") for j in range(9)] for i in range(9)]

    # 约束1: 每个格子的值在 1-9 之间
    for i in range(9):
        for j in range(9):
            solver.add(And(cells[i][j] >= 1, cells[i][j] <= 9))

    # 约束2: 每行的数字不重复
    for i in range(9):
        solver.add(Distinct(cells[i]))

    # 约束3: 每列的数字不重复
    for j in range(9):
        solver.add(Distinct([cells[i][j] for i in range(9)]))

    # 约束4: 每个 3x3 宫格的数字不重复
    for box_row in range(3):
        for box_col in range(3):
            box_cells = []
            for i in range(3):
                for j in range(3):
                    box_cells.append(cells[box_row * 3 + i][box_col * 3 + j])
            solver.add(Distinct(box_cells))

    # 约束5: 填入已知的数字
    for i in range(9):
        for j in range(9):
            if puzzle[i][j] != 0:
                solver.add(cells[i][j] == puzzle[i][j])

    # 求解
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(9):
            row = []
            for j in range(9):
                row.append(model.evaluate(cells[i][j]).as_long())
            solution.append(row)
        return solution
    else:
        return None


def print_grid(grid, title=""):
    """打印数独网格"""
    if title:
        print(f"\n{title}")
    print("-" * 25)
    for i in range(9):
        row_str = ""
        for j in range(9):
            val = grid[i][j]
            row_str += f" {val if val != 0 else '.'} "
            if j % 3 == 2 and j < 8:
                row_str += "|"
        print(row_str)
        if i % 3 == 2 and i < 8:
            print("-" * 25)
    print("-" * 25)


def main():
    # 一个中等难度的数独谜题 (0 表示空白)
    puzzle = [
        [0, 3, 0, 0, 7, 0, 0, 0, 0],
        [6, 0, 0, 1, 9, 5, 0, 0, 0],
        [0, 9, 8, 0, 0, 0, 0, 6, 0],
        [8, 0, 0, 0, 6, 0, 0, 0, 3],
        [4, 0, 0, 8, 0, 3, 0, 0, 1],
        [7, 0, 0, 0, 2, 0, 0, 0, 6],
        [0, 6, 0, 0, 0, 0, 2, 8, 0],
        [0, 0, 0, 4, 1, 9, 0, 0, 5],
        [0, 0, 0, 0, 8, 0, 0, 7, 9],
    ]

    print("=" * 50)
    print("     Z3 SMT 求解器 - 数独破解挑战")
    print("=" * 50)

    print_grid(puzzle, "原始谜题:")

    print("\n正在使用 Z3 求解...")
    solution = solve_sudoku(puzzle)

    if solution:
        print_grid(solution, "求解结果:")

        # 验证解的正确性
        print("\n验证结果:")
        if verify_solution(solution):
            print("  ✓ 解是正确的！")
        else:
            print("  ✗ 解有误！")
    else:
        print("无解！")


def verify_solution(solution):
    """验证数独解是否正确"""
    # 检查行
    for row in solution:
        if sorted(row) != list(range(1, 10)):
            return False

    # 检查列
    for j in range(9):
        col = [solution[i][j] for i in range(9)]
        if sorted(col) != list(range(1, 10)):
            return False

    # 检查 3x3 宫格
    for box_row in range(3):
        for box_col in range(3):
            box = []
            for i in range(3):
                for j in range(3):
                    box.append(solution[box_row * 3 + i][box_col * 3 + j])
            if sorted(box) != list(range(1, 10)):
                return False

    return True


if __name__ == "__main__":
    main()
