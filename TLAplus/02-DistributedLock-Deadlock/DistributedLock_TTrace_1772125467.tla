---- MODULE DistributedLock_TTrace_1772125467 ----
EXTENDS DistributedLock, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET DistributedLock_TEExpression == INSTANCE DistributedLock_TEExpression
    IN DistributedLock_TEExpression!expression
----

_trace ==
    LET DistributedLock_TETrace == INSTANCE DistributedLock_TETrace
    IN DistributedLock_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        cache_lock = (2)
        /\
        pc = (<<"GetCache", "GetDB">>)
        /\
        db_lock = (1)
    )
----

_init ==
    /\ cache_lock = _TETrace[1].cache_lock
    /\ pc = _TETrace[1].pc
    /\ db_lock = _TETrace[1].db_lock
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ cache_lock  = _TETrace[i].cache_lock
        /\ cache_lock' = _TETrace[j].cache_lock
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc
        /\ db_lock  = _TETrace[i].db_lock
        /\ db_lock' = _TETrace[j].db_lock

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("DistributedLock_TTrace_1772125467.json", _TETrace)

=============================================================================

 Note that you can extract this module `DistributedLock_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `DistributedLock_TEExpression.tla` file takes precedence 
  over the module `DistributedLock_TEExpression` below).

---- MODULE DistributedLock_TEExpression ----
EXTENDS DistributedLock, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `DistributedLock` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        cache_lock |-> cache_lock
        ,pc |-> pc
        ,db_lock |-> db_lock
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_cache_lockUnchanged |-> cache_lock = cache_lock'
        
        \* Format the `cache_lock` variable as Json value.
        \* ,_cache_lockJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(cache_lock)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_cache_lockModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].cache_lock # _TETrace[s-1].cache_lock
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE DistributedLock_TETrace ----
\*EXTENDS DistributedLock, IOUtils, TLC
\*
\*trace == IODeserialize("DistributedLock_TTrace_1772125467.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE DistributedLock_TETrace ----
EXTENDS DistributedLock, TLC

trace == 
    <<
    ([cache_lock |-> 0,pc |-> <<"GetDB", "GetCache">>,db_lock |-> 0]),
    ([cache_lock |-> 0,pc |-> <<"GetCache", "GetCache">>,db_lock |-> 1]),
    ([cache_lock |-> 2,pc |-> <<"GetCache", "GetDB">>,db_lock |-> 1])
    >>
----


=============================================================================

---- CONFIG DistributedLock_TTrace_1772125467 ----

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
\* Generated on Fri Feb 27 01:04:28 CST 2026