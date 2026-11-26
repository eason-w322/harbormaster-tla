---- MODULE Rollback ----
\* Stage 2a: RD-Commit with storage-server rollback attacks (Sec. 3.3, 4.3)

EXTENDS Integers, FiniteSets

\* Constants
Servers == {"s1", "s2", "s3"}   \* N = 2F + 1
F       == 1                    \* max servers that lose memory
MaxSeq  == 3                    \* max log entries

\* TRUE:  at most F servers ever crash (each crash wipes TEE memory)
\* FALSE: at most F servers down at once, but crashes can repeat
BoundTotalCrashes == FALSE

\* Messages
AppendMsg(i)  == [type |-> "append", seq |-> i]
VoteMsg(i, s) == [type |-> "vote",   seq |-> i, srv |-> s]

\* State
VARIABLES
    n,         \* worker's last entry (Alg. 1)
    ci,        \* worker's commit index (Alg. 1)
    disk,      \* disk[s] = last entry on s's disk (attacker can roll back)
    mem,       \* mem[s] = latest entry s remembers in TEE memory (Alg. 2)
    msgs,      \* messages in the network
    up,        \* up[s] = s is running
    canVote,   \* canVote[s] = s has its original key
    detected,  \* some server has reported a rollback
    attacked   \* ghost: a rollback really happened (not in the real system)

vars == <<n, ci, disk, mem, msgs, up, canVote, detected, attacked>>

Down        == {s \in Servers : ~up[s]}
EverCrashed == {s \in Servers : ~up[s] \/ ~canVote[s]}

Init ==
    /\ n = 0
    /\ ci = 0
    /\ disk     = [s \in Servers |-> 0]
    /\ mem      = [s \in Servers |-> 0]
    /\ msgs     = {}
    /\ up       = [s \in Servers |-> TRUE]
    /\ canVote  = [s \in Servers |-> TRUE]
    /\ detected = FALSE
    /\ attacked = FALSE

\* Protocol actions

\* Steps 0+1: create entry n+1 and send it to all servers
Append ==
    /\ n < MaxSeq
    /\ n' = n + 1
    /\ msgs' = msgs \cup {AppendMsg(n + 1)}
    /\ UNCHANGED <<ci, disk, mem, up, canVote, detected, attacked>>

\* Step 2: if the entry follows the latest one in memory, store it and vote.
\* A server whose disk no longer matches its memory does not extend it.
Vote(s) ==
    /\ up[s]
    /\ canVote[s]
    /\ disk[s] = mem[s]
    /\ \E m \in msgs:
        /\ m.type = "append"
        /\ m.seq = mem[s] + 1
        /\ disk' = [disk EXCEPT ![s] = m.seq]
        /\ mem'  = [mem  EXCEPT ![s] = m.seq]
        /\ msgs' = msgs \cup {VoteMsg(m.seq, s)}
    /\ UNCHANGED <<n, ci, up, canVote, detected, attacked>>

\* Servers that voted for entry i
Voters(i) == {s \in Servers : VoteMsg(i, s) \in msgs}

\* Step 3: commit entry i after F+1 votes
Commit(i) ==
    /\ ci < i
    /\ i <= n
    /\ Cardinality(Voters(i)) >= F + 1
    /\ ci' = i
    /\ UNCHANGED <<n, disk, mem, msgs, up, canVote, detected, attacked>>

\* Sec. 4.3: a running server reads its chain back from disk, starting at
\* the latest entry in memory. A missing entry means its disk was rolled back.
Detect(s) ==
    /\ up[s]
    /\ disk[s] < mem[s]
    /\ detected' = TRUE
    /\ UNCHANGED <<n, ci, disk, mem, msgs, up, canVote, attacked>>

\* Attacker and fault actions

\* The cloud provider replaces s's disk with an older version
Rollback(s) ==
    /\ disk[s] > 0
    /\ \E k \in 0..(disk[s] - 1): disk' = [disk EXCEPT ![s] = k]
    /\ attacked' = TRUE
    /\ UNCHANGED <<n, ci, mem, msgs, up, canVote, detected>>

\* Network loses a message
Drop ==
    /\ \E m \in msgs: msgs' = msgs \ {m}
    /\ UNCHANGED <<n, ci, disk, mem, up, canVote, detected, attacked>>

\* Server crashes; its TEE memory is lost
Crash(s) ==
    /\ up[s]
    /\ IF BoundTotalCrashes
          THEN canVote[s] /\ Cardinality(EverCrashed) < F
          ELSE Cardinality(Down) < F
    /\ up'  = [up  EXCEPT ![s] = FALSE]
    /\ mem' = [mem EXCEPT ![s] = 0]
    /\ UNCHANGED <<n, ci, disk, msgs, canVote, detected, attacked>>

\* Server restarts: reloads from disk (possibly rolled back) and gets a
\* new key that workers do not accept, so it can't vote (Sec. 4.3)
Restart(s) ==
    /\ ~up[s]
    /\ up'      = [up      EXCEPT ![s] = TRUE]
    /\ mem'     = [mem     EXCEPT ![s] = disk[s]]
    /\ canVote' = [canVote EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<n, ci, disk, msgs, detected, attacked>>

\* Spec
Next ==
    \/ Append
    \/ \E s \in Servers: Vote(s) \/ Detect(s)
    \/ \E i \in 1..MaxSeq: Commit(i)
    \/ \E s \in Servers: Rollback(s)
    \/ \E s \in Servers: Crash(s) \/ Restart(s)
    \* \/ Drop   (checked in Stage 1b; uncomment to include, use MaxSeq 2)

Spec == Init /\ [][Next]_vars

\* Properties

\* Variables hold expected values
TypeOK ==
    /\ n \in 0..MaxSeq
    /\ ci \in 0..n
    /\ disk \in [Servers -> 0..n]
    /\ mem  \in [Servers -> 0..n]
    /\ msgs \subseteq {AppendMsg(i) : i \in 1..MaxSeq}
                    \cup {VoteMsg(i, s) : i \in 1..MaxSeq, s \in Servers}
    /\ up \in [Servers -> BOOLEAN]
    /\ canVote \in [Servers -> BOOLEAN]
    /\ detected \in BOOLEAN
    /\ attacked \in BOOLEAN

\* Entry i's contents can still be read from some disk
Retrievable(i) == \E s \in Servers: disk[s] >= i

\* Some running server can still prove entry i existed (TEE memory)
ProvableInMemory(i) == \E s \in Servers: up[s] /\ mem[s] >= i

\* Soundness: no false alarms
Soundness == detected => attacked

\* Sec. 3.4: a committed entry is never lost without a trace: it is
\* retrievable, a running server can prove it existed, or the attack
\* has already been detected
NoSilentLoss ==
    \A i \in 1..ci: Retrievable(i) \/ ProvableInMemory(i) \/ detected

====