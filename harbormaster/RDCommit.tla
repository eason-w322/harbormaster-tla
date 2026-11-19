---- MODULE RDCommit ----
\* Stage 1: RD-Commit (Sec. 4.2), no faults

EXTENDS Integers, FiniteSets

\* Constants
Servers == {"s1", "s2", "s3"}   \* N = 2F + 1
F       == 1                    \* max servers down at once
MaxSeq  == 3                    \* max log entries

\* Messages
AppendMsg(i)  == [type |-> "append", seq |-> i]
VoteMsg(i, s) == [type |-> "vote",   seq |-> i, srv |-> s]

\* State
VARIABLES
    n,       \* worker's last entry (Alg. 1)
    ci,      \* worker's commit index (Alg. 1)
    stored,  \* stored[s] = last entry on s's disk (Alg. 2)
    msgs     \* messages in the network

vars == <<n, ci, stored, msgs>>

Init ==
    /\ n = 0
    /\ ci = 0
    /\ stored = [s \in Servers |-> 0]
    /\ msgs = {}

\* Actions

\* Steps 0+1: create entry n+1 and send it to all servers
Append ==
    /\ n < MaxSeq
    /\ n' = n + 1
    /\ msgs' = msgs \cup {AppendMsg(n + 1)}
    /\ UNCHANGED <<ci, stored>>

\* Step 2: store the next entry in the chain, then vote
Vote(s) ==
    \E m \in msgs:
        /\ m.type = "append"
        /\ m.seq = stored[s] + 1
        /\ stored' = [stored EXCEPT ![s] = m.seq]
        /\ msgs' = msgs \cup {VoteMsg(m.seq, s)}
        /\ UNCHANGED <<n, ci>>

\* Servers that voted for entry i
Voters(i) == {s \in Servers : VoteMsg(i, s) \in msgs}

\* Step 3: commit entry i after F+1 votes
Commit(i) ==
    /\ ci < i
    /\ i <= n
    /\ Cardinality(Voters(i)) >= F + 1
    /\ ci' = i
    /\ UNCHANGED <<n, stored, msgs>>

\* Spec
Next ==
    \/ Append
    \/ \E s \in Servers: Vote(s)
    \/ \E i \in 1..MaxSeq: Commit(i)

Spec == Init /\ [][Next]_vars

\* Properties

\* Variables hold expected values
TypeOK ==
    /\ n \in 0..MaxSeq
    /\ ci \in 0..n
    /\ stored \in [Servers -> 0..n]
    /\ msgs \subseteq {AppendMsg(i) : i \in 1..MaxSeq}
                    \cup {VoteMsg(i, s) : i \in 1..MaxSeq, s \in Servers}

\* Def. 1: committed entries are on F+1 disks
Provable ==
    \A i \in 1..ci:
        Cardinality({s \in Servers : stored[s] >= i}) >= F + 1

====