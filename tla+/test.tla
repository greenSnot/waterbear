------------------------------ MODULE test ------------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS N, F, guardR1, guardR2

VARIABLES sent, ready, isByz
                          
ASSUME NF ==
  /\ guardR1 \in Nat
  /\ guardR2 \in Nat
  /\ N \in Nat
  /\ F \in Nat
  /\ (N > F) /\ (F >= 0)
  /\ guardR1 > N \div 3
  /\ guardR2 > (2 * N) \div 3

Proc == 1 .. N
vars == << sent, ready, isByz >>

rounds == 0 .. 1

UNDEFINED == "-"
BSET0 == "bset0"
BSET1 == "bset1"
BSET01 == "bset01"

PREVOTE == "prevote"
MAINVOTE0 == "mainvote0"
MAINVOTE1 == "mainvote1"
FINALVOTE0 == "finalvote0"
FINALVOTE1 == "finalvote1"
FINALVOTEx == "finalvote*"

NEXTPREVOTE0 == "0"
NEXTPREVOTE1 == "1"
NEXTPREVOTEx == "random"

DECIDE0 == "0"
DECIDE1 == "1"

Step == {
    MAINVOTE0,
    MAINVOTE1,
    FINALVOTE0,
    FINALVOTE1,
    FINALVOTEx
}

Init == 
  /\ isByz = [i \in Proc |-> IF i <= F THEN 1 ELSE 0]
  /\ sent = [i \in Proc |-> [j \in Proc |-> [s \in Step |-> 0]]]
  /\ ready = 0

Next ==
  \/ /\ ready = 0
     /\ \E a \in Proc:
        sent' = [sent EXCEPT ![a] = 1]
     /\ ready' = 1
     /\ UNCHANGED << isByz >>
  \/ /\ ready = 1
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars 

\**Symmetry == Permutations(Proc)

(* Liveness and correctness check *)


  
=============================================================================
