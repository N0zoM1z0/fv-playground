---------------------------- MODULE TwoPhaseCommit ----------------------------
(*
  TLA+/PlusCal 两阶段提交一致性验证案例

  场景：
  - 一个协调者 (Coordinator) 和两个参与者 (Participants)
  - 协调者发起分布式事务，参与者投票并执行
  - 验证：所有参与者要么都提交，要么都中止（原子性）

  目标：
  - 用 TLA+ 建模 2PC 协议
  - 定义一致性不变量
  - 验证在协调者故障等异常情况下的一致性
*)

EXTENDS Integers, TLC, FiniteSets, Sequences

VARIABLES
  coordinator_state,    \* 协调者状态
  participant_state,    \* 参与者状态数组 [1..2]
  decision,             \* 协调者的最终决定: "Commit", "Abort", "Undecided"
  votes,                \* 参与者的投票: [1..2] -> {"Yes", "No", "None"}
  committed             \* 记录哪些参与者已提交

CONSTANT
  ParticipantCount

ProcSet == 1..ParticipantCount

\* 状态定义
\* Coordinator: Init -> CollectingVotes -> Decided -> Done
\* Participant: Init -> Voted -> Committed/Aborted

\* ==================== 初始化 ====================
Init ==
  /\ coordinator_state = "Init"
  /\ participant_state = [p \in ProcSet |-> "Init"]
  /\ decision = "Undecided"
  /\ votes = [p \in ProcSet |-> "None"]
  /\ committed = {}

\* ==================== 协调者动作 ====================

\* 阶段 1: 协调者开始收集投票
Coordinator_StartVoting ==
  /\ coordinator_state = "Init"
  /\ coordinator_state' = "CollectingVotes"
  /\ UNCHANGED <<participant_state, decision, votes, committed>>

\* 阶段 2: 协调者收集所有投票后做决定
\* 简化：假设所有参与者都已投票
Coordinator_Decide ==
  /\ coordinator_state = "CollectingVotes"
  /\ \A p \in ProcSet : votes[p] /= "None"  \* 所有参与者都已投票
  /\ IF \A p \in ProcSet : votes[p] = "Yes"
     THEN /\ decision' = "Commit"
     ELSE /\ decision' = "Abort"
  /\ coordinator_state' = "Decided"
  /\ UNCHANGED <<participant_state, votes, committed>>

\* 阶段 3: 协调者发送决定给参与者（简化模型）
Coordinator_Finish ==
  /\ coordinator_state = "Decided"
  /\ coordinator_state' = "Done"
  /\ UNCHANGED <<participant_state, decision, votes, committed>>

\* ==================== 参与者动作 ====================

\* 参与者投票
Participant_Vote(p) ==
  /\ participant_state[p] = "Init"
  /\ votes[p] = "None"
  /\ \E v \in {"Yes", "No"} :  \* 非确定性选择投票
       /\ votes' = [votes EXCEPT ![p] = v]
  /\ participant_state' = [participant_state EXCEPT ![p] = "Voted"]
  /\ UNCHANGED <<coordinator_state, decision, committed>>

\* 参与者执行提交
Participant_Commit(p) ==
  /\ participant_state[p] = "Voted"
  /\ decision = "Commit"  \* 协调者已决定提交
  /\ participant_state' = [participant_state EXCEPT ![p] = "Committed"]
  /\ committed' = committed \union {p}
  /\ UNCHANGED <<coordinator_state, decision, votes>>

\* 参与者执行中止
Participant_Abort(p) ==
  /\ participant_state[p] = "Voted"
  /\ decision = "Abort"  \* 协调者已决定中止
  /\ participant_state' = [participant_state EXCEPT ![p] = "Aborted"]
  /\ UNCHANGED <<coordinator_state, decision, votes, committed>>

\* ==================== 终止状态 ====================
Coordinator_Done ==
  /\ coordinator_state = "Done"
  /\ TRUE
  /\ UNCHANGED <<coordinator_state, participant_state, decision, votes, committed>>

Participant_Done(p) ==
  /\ participant_state[p] \in {"Committed", "Aborted"}
  /\ TRUE
  /\ UNCHANGED <<coordinator_state, participant_state, decision, votes, committed>>

\* ==================== 下一步动作 ====================
Next ==
  \/ Coordinator_StartVoting
  \/ Coordinator_Decide
  \/ Coordinator_Finish
  \/ Coordinator_Done
  \/ \E p \in ProcSet :
       Participant_Vote(p) \/ Participant_Commit(p) \/ Participant_Abort(p) \/ Participant_Done(p)

\* 完整规约
Spec == Init /\ [][Next]_<<coordinator_state, participant_state, decision, votes, committed>>

\* ==================== 一致性属性 ====================

(*
  不变量 1：一致性 (Consistency)
  所有已提交的参与者必须一致：要么都提交，要么都中止
  
  注意：在 2PC 中，一旦协调者做出决定，所有参与者必须遵循
*)
Consistency ==
  /\ ~(\E p1, p2 \in ProcSet :
         /\ participant_state[p1] = "Committed"
         /\ participant_state[p2] = "Aborted")

(*
  不变量 2：决定有效性
  只有当所有参与者都投 "Yes" 时，协调者才能决定 "Commit"
*)
ValidDecision ==
  decision = "Commit" =>
    \A p \in ProcSet : votes[p] = "Yes"

(*
  不变量 3：提交有效性
  只有当协调者决定 "Commit" 时，参与者才能提交
*)
ValidCommit ==
  \A p \in ProcSet :
    participant_state[p] = "Committed" => decision = "Commit"

(*
  不变量 4：中止有效性
  只有当协调者决定 "Abort" 或参与者投 "No" 时，参与者才能中止
*)
ValidAbort ==
  \A p \in ProcSet :
    participant_state[p] = "Aborted" =>
      (decision = "Abort" \/ votes[p] = "No")

(*
  不变量 5：状态有效性
*)
ValidStates ==
  /\ coordinator_state \in {"Init", "CollectingVotes", "Decided", "Done"}
  /\ \A p \in ProcSet : participant_state[p] \in {"Init", "Voted", "Committed", "Aborted"}
  /\ decision \in {"Commit", "Abort", "Undecided"}
  /\ \A p \in ProcSet : votes[p] \in {"Yes", "No", "None"}

=============================================================================
