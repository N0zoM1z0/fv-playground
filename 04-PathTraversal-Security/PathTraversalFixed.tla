---------------------------- MODULE PathTraversalFixed ----------------------------
(*
  Path Traversal 安全验证 - 修复版本
  
  修复方案：在返回上级目录时，检查是否已到根目录
*)

EXTENDS Naturals, Integers, Sequences, TLC, FiniteSets

VARIABLES 
  root_depth,
  current_depth,
  user_inputs,
  escape_attempted,
  pc

vars == <<root_depth, current_depth, user_inputs, escape_attempted, pc>>

MAX_INPUTS == 5
InputSequences == [1..MAX_INPUTS -> {1, -1}]

Init ==
  /\ root_depth = 2
  /\ current_depth = 2
  /\ user_inputs \in InputSequences
  /\ escape_attempted = FALSE
  /\ pc = "ProcessPath"

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
              (* FIX: 只有在深度大于根深度时才允许返回上级 *)
              /\ IF current_depth > root_depth
                 THEN 
                   /\ current_depth' = current_depth - 1
                 ELSE 
                   (* 已在根目录，忽略返回上级操作 *)
                   /\ current_depth' = current_depth
              /\ escape_attempted' = TRUE
         /\ user_inputs' = Tail(user_inputs)
         /\ pc' = "ProcessPath"
     ELSE 
       /\ pc' = "Done"
       /\ UNCHANGED <<current_depth, user_inputs, escape_attempted>>
  /\ UNCHANGED root_depth

Done ==
  /\ pc = "Done"
  /\ TRUE
  /\ UNCHANGED vars

Next ==
  ProcessPath \/ Done

Spec == Init /\ [][Next]_vars

(* 安全不变量 *)
PathSafe == current_depth >= root_depth
ValidDepth == current_depth >= 0
RootImmutable == root_depth = 2

=============================================================================
