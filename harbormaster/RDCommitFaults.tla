---- MODULE RDCommitFaults ----
(***************************************************************************)
(* HarborMaster Stage 1b: RD-Commit (Sec. 4.2) with network and server     *)
(* faults.                                                                 *)
(*                                                                         *)
(* Extends Stage 1 (RDCommit.tla) with:                                    *)
(*   - Message drop:   the network may lose any message.                   *)
(*   - Server crash:   at most F servers are down at any time (Sec. 3.1).  *)
(*   - Server restart: a restarted server keeps its disk but loses its     *)
(*                     volatile signing key, so it may no longer vote      *)
(*                     (Sec. 4.3, "Handling restarts").                    *)
(*                                                                         *)
(* Not modeled yet: disk rollback, worker crashes, auditor (Stage 2+).     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\* ------------------------------ Constants ------------------------------
Servers == {"s1", "s2", "s3"}   \* N = 2F + 1 storage servers
F       == 1                    \* max number of servers down at any time
MaxSeq  == 3                    \* bound on log entries (keeps the model finite)

\* ------------------------------ Messages -------------------------------
AppendMsg(i)  == [type |-> "append", seq |-> i]            \* AppendEntries
VoteMsg(i, s) == [type |-> "vote",   seq |-> i, srv |-> s] \* Vote

\* -------------------------------- State --------------------------------
VARIABLES
    n,        \* seq number of the worker's last created entry    (Alg. 1)
    ci,       \* highest RD-Committed seq number                  (Alg. 1)
    stored,   \* stored[s] = last contiguous entry on s's disk    (Alg. 2)
    msgs,     \* set of messages currently in the network
    up,       \* up[s] = TRUE iff server s is running
    canVote   \* canVote[s] = TRUE iff s still has its original signing key

vars == <<n, ci, stored, msgs, up, canVote>>

Down == {s \in Servers : ~up[s]}   \* the servers currently crashed

Init ==
    /\ n = 0
    /\ ci = 0
    /\ stored  = [s \in Servers |-> 0]
    /\ msgs    = {}
    /\ up      = [s \in Servers |-> TRUE]
    /\ canVote = [s \in Servers |-> TRUE]

\* --------------------------- Protocol actions --------------------------

\* Steps 0+1 (W, W->S): create entry n+1 and send AppendEntries to all servers
Append ==
    /\ n < MaxSeq
    /\ n' = n + 1
    /\ msgs' = msgs \cup {AppendMsg(n + 1)}
    /\ UNCHANGED <<ci, stored, up, canVote>>

\* Step 2 (S->W): a running server with its original key stores the entry
\* if it extends its chain, then votes
Vote(s) ==
    /\ up[s]
    /\ canVote[s]
    /\ \E m \in msgs:
        /\ m.type = "append"
        /\ m.seq = stored[s] + 1
        /\ stored' = [stored EXCEPT ![s] = m.seq]
        /\ msgs' = msgs \cup {VoteMsg(m.seq, s)}
    /\ UNCHANGED <<n, ci, up, canVote>>

\* The set of servers whose vote for entry i is in the network
Voters(i) == {s \in Servers : VoteMsg(i, s) \in msgs}

\* Step 3 (W): RD-Commit entry i (and all earlier entries) on F+1 votes
Commit(i) ==
    /\ ci < i
    /\ i <= n
    /\ Cardinality(Voters(i)) >= F + 1
    /\ ci' = i
    /\ UNCHANGED <<n, stored, msgs, up, canVote>>

\* ---------------------------- Fault actions ----------------------------

\* The network loses message m
Drop ==
    /\ \E m \in msgs: msgs' = msgs \ {m}
    /\ UNCHANGED <<n, ci, stored, up, canVote>>

\* Server s crashes; at most F servers may be down at once.
\* Its disk (stored[s]) survives; it just stops taking steps.
Crash(s) ==
    /\ up[s]
    /\ Cardinality(Down) < F
    /\ up' = [up EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<n, ci, stored, msgs, canVote>>

\* Server s restarts with its disk intact but a fresh signing key that
\* existing workers do not accept, so it can no longer vote (Sec. 4.3)
Restart(s) ==
    /\ ~up[s]
    /\ up'      = [up      EXCEPT ![s] = TRUE]
    /\ canVote' = [canVote EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<n, ci, stored, msgs>>

\* -------------------------------- Spec ---------------------------------
Next ==
    \/ Append
    \/ \E s \in Servers: Vote(s)
    \/ \E i \in 1..MaxSeq: Commit(i)
    \/ Drop
    \/ \E s \in Servers: Crash(s) \/ Restart(s)

Spec == Init /\ [][Next]_vars

\* ----------------------------- Properties ------------------------------

\* Sanity check: every variable always holds the kind of value we expect
TypeOK ==
    /\ n \in 0..MaxSeq
    /\ ci \in 0..n
    /\ stored \in [Servers -> 0..n]
    /\ msgs \subseteq {AppendMsg(i) : i \in 1..MaxSeq}
                    \cup {VoteMsg(i, s) : i \in 1..MaxSeq, s \in Servers}
    /\ up \in [Servers -> BOOLEAN]
    /\ canVote \in [Servers -> BOOLEAN]
    /\ Cardinality(Down) <= F

\* Def. 1 (disk level): every RD-Committed entry is on at least F+1 disks
Provable ==
    \A i \in 1..ci:
        Cardinality({s \in Servers : stored[s] >= i}) >= F + 1

\* Def. 1 (as worded in Sec. 3.4): a NON-CRASHED server can prove every
\* RD-Committed entry, even while up to F servers are down
ProvableByLiveServer ==
    \A i \in 1..ci:
        \E s \in Servers: up[s] /\ stored[s] >= i

====