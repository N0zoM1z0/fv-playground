---- MODULE ConcurrentTransfer_TTrace_1772125317 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ConcurrentTransfer

_expression ==
    LET ConcurrentTransfer_TEExpression == INSTANCE ConcurrentTransfer_TEExpression
    IN ConcurrentTransfer_TEExpression!expression
----

_trace ==
    LET ConcurrentTransfer_TETrace == INSTANCE ConcurrentTransfer_TETrace
    IN ConcurrentTransfer_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        alice_account = (-20)
        /\
        amount = (<<60, 60>>)
        /\
        pc = (<<"Add_Bob", "Add_Bob">>)
        /\
        bob_account = (100)
    )
----

_init ==
    /\ bob_account = _TETrace[1].bob_account
    /\ alice_account = _TETrace[1].alice_account
    /\ amount = _TETrace[1].amount
    /\ pc = _TETrace[1].pc
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ bob_account  = _TETrace[i].bob_account
        /\ bob_account' = _TETrace[j].bob_account
        /\ alice_account  = _TETrace[i].alice_account
        /\ alice_account' = _TETrace[j].alice_account
        /\ amount  = _TETrace[i].amount
        /\ amount' = _TETrace[j].amount
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("ConcurrentTransfer_TTrace_1772125317.json", _TETrace)

=============================================================================

 Note that you can extract this module `ConcurrentTransfer_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `ConcurrentTransfer_TEExpression.tla` file takes precedence 
  over the module `ConcurrentTransfer_TEExpression` below).

---- MODULE ConcurrentTransfer_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, ConcurrentTransfer

expression == 
    [
        \* To hide variables of the `ConcurrentTransfer` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        bob_account |-> bob_account
        ,alice_account |-> alice_account
        ,amount |-> amount
        ,pc |-> pc
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_bob_accountUnchanged |-> bob_account = bob_account'
        
        \* Format the `bob_account` variable as Json value.
        \* ,_bob_accountJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(bob_account)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_bob_accountModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].bob_account # _TETrace[s-1].bob_account
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE ConcurrentTransfer_TETrace ----
\*EXTENDS IOUtils, TLC, ConcurrentTransfer
\*
\*trace == IODeserialize("ConcurrentTransfer_TTrace_1772125317.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE ConcurrentTransfer_TETrace ----
EXTENDS TLC, ConcurrentTransfer

trace == 
    <<
    ([alice_account |-> 100,amount |-> <<60, 60>>,pc |-> <<"Check_Balance", "Check_Balance">>,bob_account |-> 100]),
    ([alice_account |-> 100,amount |-> <<60, 60>>,pc |-> <<"Deduct_Alice", "Check_Balance">>,bob_account |-> 100]),
    ([alice_account |-> 100,amount |-> <<60, 60>>,pc |-> <<"Deduct_Alice", "Deduct_Alice">>,bob_account |-> 100]),
    ([alice_account |-> 40,amount |-> <<60, 60>>,pc |-> <<"Add_Bob", "Deduct_Alice">>,bob_account |-> 100]),
    ([alice_account |-> -20,amount |-> <<60, 60>>,pc |-> <<"Add_Bob", "Add_Bob">>,bob_account |-> 100])
    >>
----


=============================================================================

---- CONFIG ConcurrentTransfer_TTrace_1772125317 ----

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Fri Feb 27 01:01:58 CST 2026