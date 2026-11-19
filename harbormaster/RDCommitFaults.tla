---- MODULE RDCommitFaults ----
\* Stage 1b: RD-Commit (Sec. 4.2) with message drop, crashes and restarts

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
    n,        \* worker's last entry (Alg. 1)
    ci,       \* worker's commit index (Alg. 1)
    stored,   \* stored[s] = last entry on s's disk (Alg. 2)
    msgs,     \* messages in the network
    up,       \* up[s] = s is running
    canVote   \* canVote[s] = s has its original key

vars == <<n, ci, stored, msgs, up, canVote>>

Down == {s \in Servers : ~up[s]}

Init ==
    /\ n = 0
    /\ ci = 0
    /\ stored  = [s \in Servers |-> 0]
    /\ msgs    = {}
    /\ up      = [s \in Servers |-> TRUE]
    /\ canVote = [s \in Servers |-> TRUE]

\* Protocol actions

\* Steps 0+1: create entry n+1 and send it to all servers
Append ==
    /\ n < MaxSeq
    /\ n' = n + 1
    /\ msgs' = msgs \cup {AppendMsg(n + 1)}
    /\ UNCHANGED <<ci, stored, up, canVote>>

\* Step 2: store the next entry in the chain, then vote
Vote(s) ==
    /\ up[s]
    /\ canVote[s]
    /\ \E m \in msgs:
        /\ m.type = "append"
        /\ m.seq = stored[s] + 1
        /\ stored' = [stored EXCEPT ![s] = m.seq]
        /\ msgs' = msgs \cup {VoteMsg(m.seq, s)}
    /\ UNCHANGED <<n, ci, up, canVote>>

\* Servers that voted for entry i
Voters(i) == {s \in Servers : VoteMsg(i, s) \in msgs}

\* Step 3: commit entry i after F+1 votes
Commit(i) ==
    /\ ci < i
    /\ i <= n
    /\ Cardinality(Voters(i)) >= F + 1
    /\ ci' = i
    /\ UNCHANGED <<n, stored, msgs, up, canVote>>

\* Fault actions

\* Network loses a message
Drop ==
    /\ \E m \in msgs: msgs' = msgs \ {m}
    /\ UNCHANGED <<n, ci, stored, up, canVote>>

\* Server crashes; disk survives; at most F down
Crash(s) ==
    /\ up[s]
    /\ Cardinality(Down) < F
    /\ up' = [up EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<n, ci, stored, msgs, canVote>>

\* Server restarts with a new key, so it can't vote (Sec. 4.3)
Restart(s) ==
    /\ ~up[s]
    /\ up'      = [up      EXCEPT ![s] = TRUE]
    /\ canVote' = [canVote EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<n, ci, stored, msgs>>

\* Spec
Next ==
    \/ Append
    \/ \E s \in Servers: Vote(s)
    \/ \E i \in 1..MaxSeq: Commit(i)
    \/ Drop
    \/ \E s \in Servers: Crash(s) \/ Restart(s)

Spec == Init /\ [][Next]_vars

\* Properties

\* Variables hold expected values
TypeOK ==
    /\ n \in 0..MaxSeq
    /\ ci \in 0..n
    /\ stored \in [Servers -> 0..n]
    /\ msgs \subseteq {AppendMsg(i) : i \in 1..MaxSeq}
                    \cup {VoteMsg(i, s) : i \in 1..MaxSeq, s \in Servers}
    /\ up \in [Servers -> BOOLEAN]
    /\ canVote \in [Servers -> BOOLEAN]
    /\ Cardinality(Down) <= F

\* Def. 1: committed entries are on F+1 disks
Provable ==
    \A i \in 1..ci:
        Cardinality({s \in Servers : stored[s] >= i}) >= F + 1

\* Def. 1: a running server holds every committed entry
ProvableByLiveServer ==
    \A i \in 1..ci:
        \E s \in Servers: up[s] /\ stored[s] >= i

====