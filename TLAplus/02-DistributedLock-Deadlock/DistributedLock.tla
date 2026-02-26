---------------------------- MODULE DistributedLock ----------------------------
(*
  TLA+/PlusCal 分布式锁死锁检测案例

  场景：
  - 两个进程竞争两个资源（数据库锁 + 缓存锁）
  - 进程 1 先获取数据库锁，再获取缓存锁
  - 进程 2 先获取缓存锁，再获取数据库锁
  - 这种获取顺序可能导致死锁

  目标：
  - 用 TLA+ 建模分布式锁系统
  - 定义无死锁不变量
  - 用 TLC 发现潜在的死锁场景
*)

EXTENDS Integers, TLC, FiniteSets

VARIABLES
  db_lock,      \* 数据库锁状态: 0=空闲, 1=被进程1持有, 2=被进程2持有
  cache_lock,   \* 缓存锁状态: 0=空闲, 1=被进程1持有, 2=被进程2持有
  pc            \* 程序计数器: 记录每个进程的执行状态

\* 进程集合
ProcSet == {1, 2}

\* 进程状态定义
\* 进程1: GetDB -> GetCache -> Work -> Release
\* 进程2: GetCache -> GetDB -> Work -> Release

\* 初始化
Init ==
  /\ db_lock = 0
  /\ cache_lock = 0
  /\ pc = [self \in ProcSet |-> 
         IF self = 1 THEN "GetDB" 
         ELSE "GetCache"]

\* ==================== 进程 1 的动作 ====================
\* 进程 1: 先获取 DB 锁，再获取 Cache 锁

P1_GetDB ==
  /\ pc[1] = "GetDB"
  /\ IF db_lock = 0
     THEN /\ db_lock' = 1
          /\ pc' = [pc EXCEPT ![1] = "GetCache"]
     ELSE /\ TRUE  \* 锁被占用，等待（自旋）
          /\ pc' = [pc EXCEPT ![1] = "GetDB"]
  /\ UNCHANGED cache_lock

P1_GetCache ==
  /\ pc[1] = "GetCache"
  /\ IF cache_lock = 0
     THEN /\ cache_lock' = 1
          /\ pc' = [pc EXCEPT ![1] = "Work"]
     ELSE /\ TRUE  \* 锁被占用，等待（自旋）
          /\ pc' = [pc EXCEPT ![1] = "GetCache"]
  /\ UNCHANGED db_lock

P1_Work ==
  /\ pc[1] = "Work"
  /\ pc' = [pc EXCEPT ![1] = "Release"]
  /\ UNCHANGED <<db_lock, cache_lock>>

P1_Release ==
  /\ pc[1] = "Release"
  /\ db_lock' = 0
  /\ cache_lock' = 0
  /\ pc' = [pc EXCEPT ![1] = "Done"]

\* ==================== 进程 2 的动作 ====================
\* 进程 2: 先获取 Cache 锁，再获取 DB 锁（与进程1相反！）

P2_GetCache ==
  /\ pc[2] = "GetCache"
  /\ IF cache_lock = 0
     THEN /\ cache_lock' = 2
          /\ pc' = [pc EXCEPT ![2] = "GetDB"]
     ELSE /\ TRUE
          /\ pc' = [pc EXCEPT ![2] = "GetCache"]
  /\ UNCHANGED db_lock

P2_GetDB ==
  /\ pc[2] = "GetDB"
  /\ IF db_lock = 0
     THEN /\ db_lock' = 2
          /\ pc' = [pc EXCEPT ![2] = "Work"]
     ELSE /\ TRUE
          /\ pc' = [pc EXCEPT ![2] = "GetDB"]
  /\ UNCHANGED cache_lock

P2_Work ==
  /\ pc[2] = "Work"
  /\ pc' = [pc EXCEPT ![2] = "Release"]
  /\ UNCHANGED <<db_lock, cache_lock>>

P2_Release ==
  /\ pc[2] = "Release"
  /\ db_lock' = 0
  /\ cache_lock' = 0
  /\ pc' = [pc EXCEPT ![2] = "Done"]

\* ==================== 终止状态 ====================
P1_Done ==
  /\ pc[1] = "Done"
  /\ TRUE
  /\ UNCHANGED <<db_lock, cache_lock, pc>>

P2_Done ==
  /\ pc[2] = "Done"
  /\ TRUE
  /\ UNCHANGED <<db_lock, cache_lock, pc>>

\* ==================== 下一步动作 ====================
Next ==
  P1_GetDB \/ P1_GetCache \/ P1_Work \/ P1_Release \/ P1_Done
  \/ P2_GetCache \/ P2_GetDB \/ P2_Work \/ P2_Release \/ P2_Done

\* 完整规约
Spec == Init /\ [][Next]_<<db_lock, cache_lock, pc>>

\* ==================== 安全属性 ====================

(*
  不变量 1：互斥性
  同一个锁不能被两个进程同时持有
*)
MutexOK ==
  /\ ~(db_lock = 1 /\ db_lock = 2)  \* DB锁不能同时被1和2持有
  /\ ~(cache_lock = 1 /\ cache_lock = 2)  \* Cache锁同理

(*
  不变量 2：无死锁（简化检查）
  检查是否存在循环等待条件
  
  死锁条件：
  - 进程1持有DB锁，等待Cache锁
  - 进程2持有Cache锁，等待DB锁
*)
NoDeadlock ==
  ~(
    /\ db_lock = 1      \* 进程1持有DB锁
    /\ cache_lock = 2   \* 进程2持有Cache锁
    /\ pc[1] = "GetCache"  \* 进程1在等待Cache锁
    /\ pc[2] = "GetDB"     \* 进程2在等待DB锁
  )

(*
  不变量 3：锁状态有效性
  锁状态只能是 0, 1, 2
*)
ValidLockState ==
  /\ db_lock \in {0, 1, 2}
  /\ cache_lock \in {0, 1, 2}

(*
  不变量 4：最终进展（Liveness 属性）
  这是一个时序属性，表示系统最终应该能完成
  注意：这个属性在当前模型中会被违反，因为存在死锁！
*)
\* EventuallyDone == <>(pc[1] = "Done" /\ pc[2] = "Done")

=============================================================================
