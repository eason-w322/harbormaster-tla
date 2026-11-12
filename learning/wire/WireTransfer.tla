---- MODULE WireTransfer ----
EXTENDS Integers

People == {"alice", "bob"}
Money == 1..10
Workers == 1..2

VARIABLES acct, amnt, from, to, pc
vars = <<acct, amnt, from, to, pc>>

Init ==
    /\ acct \in [People -> Money]
    /\ amnt \in [Workers -> 1..5]
    /\ from \in [Workers -> People]
    /\ to \in [Workers -> People]
    /\ pc = [w \in Workers |-> "Check"]

Check(w) == 
    /\ pc[w] = "Check"
    /\ IF acct[from[w]] >= amnt[w]
          THEN pc' = [pc EXCEPT ![w] = "Withdraw"]
          ELSE pc' = [pc EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<acct, amnt, from, to>>
 
Withdraw(w) ==
    /\ pc[w] = "Withdraw"
    /\ acct' = [acct EXCEPT ![from[w]] = acct[from[w]] - amnt[w]]
    /\ pc' = [pc EXCEPT ![w] = "Deposite"]
    /\ UNCHANGED <<amnt, from, to>>

Deposite(w) ==
    /\ pc[w] = "Deposite"
    /\ acct' = [acct EXCEPT ![to[w]] = acct[to[w]] + amnt[w]]
    /\ pc' = [pc EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<amnt, from, to>>

Terminating ==
    /\ pc = [w \in Workers |-> "Done"]
    /\ UNCHANGED vars

NEXT ==
    \/ \E w \in Workers: Check(w) \/ Withdraw(w) \/ Deposite(w)
    \/ Terminating
    
    
====
