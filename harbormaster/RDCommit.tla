---- MODULE RDCommit ----
(***************************************************************************)
(* HarborMaster Stage 1: steady-state logging and RD-Commit (Sec. 4.2).    *)
(* One worker, N = 2F+1 storage servers. No crashes or rollbacks yet.      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\* ------------------------------ Constants ------------------------------
Servers == {"s1", "s2", "s3"}   \* N = 2F + 1 storage servers
F       == 1                    \* max number of servers that can crash
MaxSeq  == 3                    \* bound on log entries (keeps the model finite)

\* ------------------------------ Messages -------------------------------
AppendMsg(i)  == [type |-> "append", seq |-> i]            \* AppendEntries
VoteMsg(i, s) == [type |-> "vote",   seq |-> i, srv |-> s] \* Vote

\* -------------------------------- State --------------------------------
VARIABLES
    n,       \* seq number of the worker's last created entry    (Alg. 1)
    ci,      \* highest RD-Committed seq number                  (Alg. 1)
    stored,  \* stored[s] = last contiguous entry server s holds (Alg. 2)
    msgs     \* set of all messages ever sent (the network)

vars == <<n, ci, stored, msgs>>

Init ==
    /\ n = 0
    /\ ci = 0
    /\ stored = [s \in Servers |-> 0]
    /\ msgs = {}

\* ------------------------------- Actions -------------------------------

\* Steps 0+1 (W, W->S): create entry n+1 and send AppendEntries to all servers
Append ==
    /\ n < MaxSeq
    /\ n' = n + 1
    /\ msgs' = msgs \cup {AppendMsg(n + 1)}
    /\ UNCHANGED <<ci, stored>>

\* Step 2 (S->W): server s stores the entry if it extends its chain, then votes
Vote(s) ==
    \E m \in msgs:
        /\ m.type = "append"
        /\ m.seq = stored[s] + 1
        /\ stored' = [stored EXCEPT ![s] = m.seq]
        /\ msgs' = msgs \cup {VoteMsg(m.seq, s)}
        /\ UNCHANGED <<n, ci>>

\* The set of servers that have voted for entry i
Voters(i) == {s \in Servers : VoteMsg(i, s) \in msgs}

\* Step 3 (W): RD-Commit entry i once F+1 servers have voted for it
Commit(i) ==
    /\ ci < i
    /\ i <= n
    /\ Cardinality(Voters(i)) >= F + 1
    /\ ci' = i
    /\ UNCHANGED <<n, stored, msgs>>

\* -------------------------------- Spec ---------------------------------
Next ==
    \/ Append
    \/ \E s \in Servers: Vote(s)
    \/ \E i \in 1..MaxSeq: Commit(i)

Spec == Init /\ [][Next]_vars

\* ----------------------------- Properties ------------------------------
\* Sanity check: every variable always holds the kind of value we expect
TypeOK ==
    /\ n \in 0..MaxSeq
    /\ ci \in 0..n
    /\ stored \in [Servers -> 0..n]
    /\ msgs \subseteq {AppendMsg(i) : i \in 1..MaxSeq}
                    \cup {VoteMsg(i, s) : i \in 1..MaxSeq, s \in Servers}

\* Def. 1: every RD-Committed entry is stored on at least F+1 servers
Provable ==
    \A i \in 1..ci:
        Cardinality({s \in Servers : stored[s] >= i}) >= F + 1

====