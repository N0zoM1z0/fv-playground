---------------------------- MODULE ConcurrentTransfer ----------------------------
(*
  TLA+/PlusCal 并发转账案例 - TOCTOU 漏洞演示

n  场景：
  - Alice 账户有 100 元，Bob 账户有 100 元
  - 两个并发转账请求，每笔转 60 元
  - 由于条件竞争（TOCTOU），可能导致透支

  目标：
  - 用 PlusCal 建模并发系统
  - 定义安全不变量 NoOverdraft
  - 用 TLC Model Checker 发现漏洞
*)

EXTENDS Integers, TLC

(* --algorithm ConcurrentTransfer {

  \* 定义全局系统状态变量
  variables
    alice_account = 100,
    bob_account = 100;

  \* 定义并发的转账进程（模拟 2 个并发请求）
  process (TransferMoney \in 1..2)
    variables amount = 60;  \* 每笔请求转账 60 元
  {
    Check_Balance:  \* 标签1：检查余额（原子操作）
      if (alice_account >= amount) {

        Deduct_Alice:  \* 标签2：扣除 Alice 的钱（原子操作）
          alice_account := alice_account - amount;

        Add_Bob:  \* 标签3：增加 Bob 的钱（原子操作）
          bob_account := bob_account + amount;
      }
  }

} *)

\* 将 PlusCal 翻译成 TLA+（由 PlusCal 编译器自动生成）
\* 下面是翻译后的 TLA+ 公式（手动展开以便理解）

\* 变量声明
VARIABLES alice_account, bob_account, pc, amount

\* 进程标识符
ProcSet == (1..2)

\* 初始化
Init ==
  /\ alice_account = 100
  /\ bob_account = 100
  /\ amount = [self \in ProcSet |-> 60]
  /\ pc = [self \in ProcSet |-> "Check_Balance"]

\* Check_Balance 标签的动作
\* 这是 TOCTOU 漏洞的关键：检查余额和扣款是两个独立的原子操作
Check_Balance(self) ==
  /\ pc[self] = "Check_Balance"
  /\ IF alice_account >= amount[self]
     THEN /\ pc' = [pc EXCEPT ![self] = "Deduct_Alice"]
     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<alice_account, bob_account, amount>>

\* Deduct_Alice 标签的动作
Deduct_Alice(self) ==
  /\ pc[self] = "Deduct_Alice"
  /\ alice_account' = alice_account - amount[self]
  /\ pc' = [pc EXCEPT ![self] = "Add_Bob"]
  /\ UNCHANGED <<bob_account, amount>>

\* Add_Bob 标签的动作
Add_Bob(self) ==
  /\ pc[self] = "Add_Bob"
  /\ bob_account' = bob_account + amount[self]
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<alice_account, amount>>

\* 终止状态
done(self) ==
  /\ pc[self] = "Done"
  /\ TRUE
  /\ UNCHANGED <<alice_account, bob_account, pc, amount>>

\* 下一步动作
Next ==
  \E self \in ProcSet :
    Check_Balance(self) \/ Deduct_Alice(self) \/ Add_Bob(self) \/ done(self)

\* 完整规约
Spec == Init /\ [][Next]_<<alice_account, bob_account, pc, amount>>

\* ==================== 安全不变量（Invariants）====================

(*
  不变量 1：禁止透支
  在任何系统状态下，Alice 的余额都不能小于 0
  这就是我们要保护的安全属性！
*)
NoOverdraft == alice_account >= 0

(*
  不变量 2：资金守恒
  在任何系统状态下，两人的总钱数必须永远是 200
*)
TotalFundsConsistent == alice_account + bob_account = 200

(*
  不变量 3：Bob 余额非负
  Bob 的余额也不能小于 0
*)
BobNoOverdraft == bob_account >= 0

=============================================================================
