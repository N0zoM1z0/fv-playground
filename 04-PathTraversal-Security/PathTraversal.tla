---------------------------- MODULE PathTraversal ----------------------------
(*
  Path Traversal (Directory Traversal) 安全验证 - TLA+ 架构层 FV
  
  场景：验证云端沙箱文件系统的路径解析算法
  核心：将路径抽象为序列，验证无论如何操作都无法逃逸沙箱
*)

EXTENDS Naturals, Integers, Sequences, TLC, FiniteSets

(*
  --algorithm SandboxCheck
  
  variables
    (* 沙箱根目录深度，假设 /sandbox/user/ 是深度 2 *)
    root_depth = 2,
    
    (* 当前路径栈深度 *)
    current_depth = 2,
    
    (* 攻击者输入序列：1 = 进入子目录，-1 = 返回上级 (..) *)
    (* TLC 会穷举所有可能的输入序列 *)
    user_inputs \in [1..5 -> {1, -1}],
    
    (* 记录是否尝试过逃逸 *)
    escape_attempted = FALSE;

  define
    (* 安全不变量：当前深度绝对不能小于沙箱根深度 *)
    PathSafe == current_depth >= root_depth
  end define;

  begin
    ProcessPath:
      while user_inputs /= <<>> do
        with action = Head(user_inputs) do
          if action = 1 then
            (* 进入子目录：深度 +1 *)
            current_depth := current_depth + 1;
          else
            (* 返回上级：深度 -1 *)
            (* BUG: 没有检查是否已到根目录！ *)
            current_depth := current_depth - 1;
            escape_attempted := TRUE;
          end if;
          
          (* 移除已处理的动作 *)
          user_inputs := Tail(user_inputs);
        end with;
      end while;
  end algorithm;
*)

\* ==================== 变量声明 ====================
VARIABLES 
  root_depth,       \* 沙箱根目录深度
  current_depth,    \* 当前路径深度
  user_inputs,      \* 用户输入序列
  escape_attempted, \* 是否尝试逃逸
  pc                \* 程序计数器

\* 定义变量元组
vars == <<root_depth, current_depth, user_inputs, escape_attempted, pc>>

\* 输入序列的最大长度
MAX_INPUTS == 5

\* 所有可能的输入序列
InputSequences == [1..MAX_INPUTS -> {1, -1}]

\* ==================== 初始化 ====================
Init ==
  /\ root_depth = 2
  /\ current_depth = 2
  /\ user_inputs \in InputSequences
  /\ escape_attempted = FALSE
  /\ pc = "ProcessPath"

\* ==================== 动作定义 ====================

\* 处理路径的主循环
ProcessPath ==
  /\ pc = "ProcessPath"
  /\ IF user_inputs /= <<>>
     THEN 
       LET action == Head(user_inputs)
       IN
         /\ IF action = 1
            THEN 
              /\ current_depth' = current_depth + 1
              /\ escape_attempted' = escape_attempted
            ELSE
              \* BUG: 没有检查是否已到根目录就直接减
              /\ current_depth' = current_depth - 1
              /\ escape_attempted' = TRUE
         /\ user_inputs' = Tail(user_inputs)
         /\ pc' = "ProcessPath"
     ELSE 
       /\ pc' = "Done"
       /\ UNCHANGED <<current_depth, user_inputs, escape_attempted>>
  /\ UNCHANGED root_depth

\* 终止状态
Done ==
  /\ pc = "Done"
  /\ TRUE
  /\ UNCHANGED vars

\* ==================== 下一步动作 ====================
Next ==
  ProcessPath \/ Done

\* ==================== 完整规约 ====================
Spec == Init /\ [][Next]_vars

\* ==================== 安全不变量 ====================

(*
  安全不变量 1：路径安全
  当前深度绝对不能小于沙箱根深度
  如果被违反，说明发生了路径逃逸！
*)
PathSafe == current_depth >= root_depth

(*
  安全不变量 2：状态有效性
  深度必须是非负整数
*)
ValidDepth == current_depth >= 0

(*
  安全不变量 3：根目录不可变
  沙箱根目录深度始终保持不变
*)
RootImmutable == root_depth = 2

(*
  时序属性：最终进展
  系统最终会到达终止状态（用于验证无死锁）
*)
\* EventuallyDone == <>(pc = "Done")

=============================================================================
