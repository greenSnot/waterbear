------------------------------ MODULE quadratic_aba ------------------------------

(*
To reduce computations and for simplicity, compare to the pseudocode:
1. We use "abstraction from a God's perspective" to model the protocol. (i.e., we can count the votes from honest nodes.)
2. Byzantine nodes are fixed and always in the first F nodes.
3. If possible, we only consider the worst(error-prone) cases.
4. We only simulate the possible and non-intuitive attacks. Byzantine nodes can only send inconsistent votes in the Mainvote stage.
5. The prevote stage is abstracted into "bset0", "bset1" and "bset01".
6. The "bsetX" stage is a prerequisite for the other stages.
7. Round 0 is sufficient to prove this protocol.
*)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS N, F, guardR1, guardR2

VARIABLES isByz,
          sent,
          step,
          prevoteState,
          nextPrevote, (* prevote next round *)
          decide
                          
ASSUME NF ==
  /\ guardR1 \in Nat
  /\ guardR2 \in Nat
  /\ N \in Nat
  /\ F \in Nat
  /\ (N > F) /\ (F >= 0)
  /\ guardR1 > N \div 3
  /\ guardR2 > (2 * N) \div 3

Proc == 1 .. N
vars == << sent, isByz, step, prevoteState, decide, nextPrevote >>

rounds == 0 .. 1

UNDEFINED == "-"
BSET0 == "bset0"
BSET1 == "bset1"
BSET01 == "bset01"

PREVOTE == "prevote"
VOTE0 == "vote0"
VOTE1 == "vote1"
MAINVOTE0 == "mainvote0"
MAINVOTE1 == "mainvote1"
MAINVOTEx == "mainvote*"
FINALVOTE0 == "finalvote0"
FINALVOTE1 == "finalvote1"
FINALVOTEx == "finalvote*"

NEXTPREVOTE0 == "0"
NEXTPREVOTE1 == "1"

DECIDE0 == "0"
DECIDE1 == "1"

Step == {
    VOTE0,
    VOTE1,
    MAINVOTE0,
    MAINVOTE1,
    MAINVOTEx,
    FINALVOTE0,
    FINALVOTE1,
    FINALVOTEx
}

Init ==  
  /\ sent = [i \in Proc |-> [j \in Proc |-> [s \in Step |-> 0]]]
  /\ isByz = [ i \in Proc |-> IF i <= F THEN 1 ELSE 0 ]
  /\ step = [ i \in Proc |-> UNDEFINED ] (* undefined -> prevote -> vote -> mainvote -> finalvote *)
  /\ decide = [ i \in Proc |-> UNDEFINED] (* unknown / decide 0 / decide 1 *)
  /\ nextPrevote = [ i \in Proc |-> UNDEFINED](* unknown / prevote 0 / prevote 1 *)
  /\ prevoteState = [ i \in Proc |-> UNDEFINED] (* unkonwn / bset0 / bset1 / bset01 *)

ArrSum(s) == LET
  RECURSIVE Helper(_)
  Helper(s_) == IF s_ = <<>> THEN 0 ELSE
  Head(s_) + Helper(Tail(s_))
IN Helper(s)

VoteSumS(i, _step, _set) == 
    ArrSum([s \in Proc |-> IF s \in _set THEN sent[s][i][_step] ELSE 0])
VoteSum(i, _step, _s) == 
    ArrSum([s \in Proc |-> IF s = _s THEN sent[s][i][_step] ELSE 0])

VoteFromAnyHonest(i, s) == \E j \in Proc: isByz[j] = 0 /\ sent[j][i][s] = 1
VoteFromAnyByz(i, s) == \E j \in Proc: isByz[j] = 1 /\ sent[j][i][s] = 1
VoteFromAnyFPlus1HonestGte(x, s, c) == \E k \in SUBSET {i \in Proc: isByz[i] = 0} : /\ Cardinality(k) = F + 1
                                                                                   /\ VoteSumS(x, s, k) >= c
VoteFromAnyFByzGte(x, s, c) == \E k \in SUBSET {i \in Proc: isByz[i] = 1} : /\ Cardinality(k) = F
                                                                                   /\ VoteSumS(x, s, k) >= c

Vote0(sender) ==
  /\ \/ isByz[sender] = 1
     \/ /\ isByz[sender] = 0
        /\ \/ prevoteState[sender] = BSET0
           \/ prevoteState[sender] = BSET01
  /\ step[sender] = PREVOTE
  /\ step' = [step EXCEPT ![sender] = VOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = VOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

Vote1(sender) ==
  /\ \/ isByz[sender] = 1
     \/ /\ isByz[sender] = 0
        /\ \/ prevoteState[sender] = BSET1
           \/ prevoteState[sender] = BSET01
  /\ step[sender] = PREVOTE
  /\ step' = [step EXCEPT ![sender] = VOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = VOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

MainVote0(sender) ==
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \/ isByz[sender] = 1
     \/ /\ isByz[sender] = 0
        /\ VoteFromAnyFPlus1HonestGte(sender, VOTE0, guardR1)
  /\ step' = [step EXCEPT ![sender] = MAINVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

MainVote1(sender) ==
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \/ isByz[sender] = 1
     \/ /\ isByz[sender] = 0
        /\ VoteFromAnyFPlus1HonestGte(sender, VOTE1, guardR1)
  /\ step' = [step EXCEPT ![sender] = MAINVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

MainVoteX(sender) ==
  /\ \/ isByz[sender] = 1
     \/ /\ isByz[sender] = 0
        /\ prevoteState[sender] = BSET01
        /\ VoteFromAnyHonest(sender, VOTE0)
        /\ VoteFromAnyHonest(sender, VOTE1)
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ step' = [step EXCEPT ![sender] = MAINVOTEx]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTEx THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

(*todo*)
FinalVote0(sender) ==
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ \/ isByz[sender] = 1
     \/ /\ isByz[sender] = 0
        /\ VoteFromAnyFPlus1HonestGte(sender, MAINVOTE0, guardR1)
  /\ step' = [step EXCEPT ![sender] = FINALVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

FinalVote1(sender) ==
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
  /\ VoteFromAnyFPlus1HonestGte(sender, MAINVOTE1, guardR1)
  /\ step' = [step EXCEPT ![sender] = FINALVOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

FinalVoteStar(sender) ==
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
  /\ prevoteState[sender] = BSET01
  /\ VoteFromAnyHonest(sender, MAINVOTE0)
  /\ VoteFromAnyHonest(sender, MAINVOTE1)
  /\ \/ VoteFromAnyFByzGte(sender, MAINVOTE0, F)
     \/ VoteFromAnyFByzGte(sender, MAINVOTE1, F)
  /\ step' = [step EXCEPT ![sender] = FINALVOTEx]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTEx THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

Consume(sender) ==
  \/ /\ decide[sender] = UNDEFINED
     /\ nextPrevote[sender] = UNDEFINED
     /\ \/ /\ step[sender] = UNDEFINED
           /\ \/ /\ \E i \in Proc: isByz[i] = 0 /\ prevoteState[i] = BSET0
                 /\ prevoteState' = [prevoteState EXCEPT ![sender] = BSET0]
              \/ /\ \E i \in Proc: isByz[i] = 0 /\ prevoteState[i] = BSET1
                 /\ prevoteState' = [prevoteState EXCEPT ![sender] = BSET1]
              \/ prevoteState' = [prevoteState EXCEPT ![sender] = BSET01]
           /\ step' = [step EXCEPT ![sender] = PREVOTE]
           /\ UNCHANGED << sent, isByz, decide, nextPrevote >>
        \/ /\ step[sender] # UNDEFINED
           /\ \E s \in Step:
              /\ \/ /\ s = VOTE0
                    /\ Vote0(sender)
                 \/ /\ s = VOTE1
                    /\ Vote1(sender)
                 \/ /\ s = MAINVOTE0
                    /\ MainVote0(sender)
                 \/ /\ s = MAINVOTE1
                    /\ MainVote1(sender)
                 \/ /\ s = MAINVOTEx
                    /\ MainVoteX(sender)
                 \/ /\ s = FINALVOTE0
                    /\ FinalVote0(sender)
                 \/ /\ s = FINALVOTE1
                    /\ FinalVote1(sender)
                 \/ /\ s = FINALVOTEx
                    /\ FinalVoteStar(sender)
  
Decide1(i) ==
  /\ VoteFromAnyFPlus1HonestGte(i, FINALVOTE1, guardR1)
  /\ decide' = [decide EXCEPT ![i] = DECIDE1]
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED << step, sent, prevoteState, isByz >>

Decide0(i) ==
  /\ VoteFromAnyFPlus1HonestGte(i, FINALVOTE0, guardR1)
  /\ decide' = [decide EXCEPT ![i] = DECIDE0]
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE0]
  /\ UNCHANGED << step, sent, prevoteState, isByz >>

NextPrevote0(i) ==
  /\ VoteFromAnyHonest(i, FINALVOTE0)
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE0]
  /\ UNCHANGED << step, sent, prevoteState, isByz, decide >>

NextPrevote1(i) ==
  /\ VoteFromAnyHonest(i, FINALVOTE1)
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED << step, sent, prevoteState, isByz, decide >>

NextPrevoteRandom(i) ==
  /\ \A j \in {k \in Proc: isByz[k] = 0}: step[j] = FINALVOTEx
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED << step, sent, prevoteState, isByz, decide >>

Decide(i) ==
  /\ isByz[i] = 0
  /\ decide[i] = UNDEFINED
  /\ nextPrevote[i] = UNDEFINED
  /\ \/ step[i] = FINALVOTE0
     \/ step[i] = FINALVOTE1
     \/ step[i] = FINALVOTEx
  /\ \/ Decide1(i)
     \/ Decide0(i)
     \/ NextPrevote0(i)
     \/ NextPrevote1(i)
     \/ NextPrevoteRandom(i)

Next ==
  /\ \E self \in Proc :
     \/ Consume(self)
     \/ Decide(self)
     \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in Proc : \/ Consume(self)
                                           \/ Decide(self))

\**Symmetry == Permutations(Proc)

(* Liveness and correctness check *)

(* Eventually, every honest node either decides on v or prevotes for v in the next round. *)
Corr_Ltl == 
   []<>( \/ \A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE0
         \/ \A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE1
       )
  
=============================================================================
