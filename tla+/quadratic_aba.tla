------------------------------ MODULE quadratic_aba ------------------------------

(*
To reduce computations and for simplicity, compare to the pseudocode:
1. The prevote stage is abstracted into "bset0", "bset1" and "bset01".
2. The "bsetX" stage is a prerequisite for the other stages.
2. Byzantine nodes are fixed and always in the first F nodes.
*)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS N, F, guardR1, guardR2

VARIABLES isByz,
          sent,
          step,
          prevoteState,
          nextPrevote, (* prevotes of the second round *)
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
MAINVOTEx == "mainvotex"
FINALVOTE0 == "finalvote0"
FINALVOTE1 == "finalvote1"
FINALVOTEx == "finalvote*"

NEXTPREVOTE0 == "0"
NEXTPREVOTE1 == "1"
NEXTPREVOTEx == "random"

DECIDE0 == "0"
DECIDE1 == "1"
DECIDEx == "x"

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
  /\ decide = [ i \in Proc |-> UNDEFINED] (* unknown / decide 0 / decide 1 / decide x *)
  /\ nextPrevote = [ i \in Proc |-> UNDEFINED](* unknown / prevote 0 / prevote 1 / prevote random *)
  /\ prevoteState = [ i \in Proc |-> UNDEFINED] (* unkonwn / bset0 / bset1 / bset01 *)

ArrSum(s) == LET
  RECURSIVE Helper(_)
  Helper(s_) == IF s_ = <<>> THEN 0 ELSE
  Head(s_) + Helper(Tail(s_))
IN Helper(s)

VoteSumS(i, _step, _set) == 
    ArrSum([s \in Proc |-> IF s \in _set THEN sent[s][i][_step] ELSE 0])
VoteSum(i, _step) == 
    ArrSum([s \in Proc |-> sent[s][i][_step]])

Vote0(sender) ==
  /\ step[sender] = PREVOTE
  /\ \/ prevoteState[sender] = BSET0
     \/ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = VOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = VOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

Vote1(sender) ==
  /\ step[sender] = PREVOTE
  /\ \/ prevoteState[sender] = BSET1
     \/ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = VOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = VOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

MainVote0(sender) ==
  /\ VoteSum(sender, VOTE0) >= guardR2
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \/ prevoteState[sender] = BSET0
     \/ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = MAINVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

MainVote1(sender) ==
  /\ VoteSum(sender, VOTE1) >= guardR2
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \/ prevoteState[sender] = BSET1
     \/ prevoteState[sender] = BSET01
  /\ step' = [step EXCEPT ![sender] = MAINVOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

MainVoteX(sender) ==
  /\ \/ step[sender] = VOTE1
     \/ step[sender] = VOTE0
  /\ \E i \in SUBSET Proc: /\ Cardinality(i) = guardR2
                           /\ \E j \in i, k \in i: j # k /\ sent[j][sender][VOTE0] = 1 /\ sent[k][sender][VOTE1] = 1
  /\ step' = [step EXCEPT ![sender] = MAINVOTEx]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = MAINVOTEx THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

FinalVote0(sender) ==
  /\ VoteSum(sender, VOTE0) >= guardR1
  /\ \E i \in SUBSET Proc: /\ Cardinality(i) = guardR2
                           /\ \A j \in i: sent[j][sender][MAINVOTE0] = 1
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ step' = [step EXCEPT ![sender] = FINALVOTE0]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTE0 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

FinalVote1(sender) ==
  /\ VoteSum(sender, VOTE1) >= guardR1
  /\ \E i \in SUBSET Proc: /\ Cardinality(i) = guardR2
                           /\ \A j \in i: sent[j][sender][MAINVOTE1] = 1
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ step' = [step EXCEPT ![sender] = FINALVOTE1]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTE1 THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

FinalVoteStar(sender) ==
  /\ \/ step[sender] = MAINVOTE1
     \/ step[sender] = MAINVOTE0
     \/ step[sender] = MAINVOTEx
  /\ prevoteState[sender] = BSET01
  /\ \/ /\ \/ VoteSum(sender, VOTE1) >= guardR1
           \/ VoteSum(sender, VOTE0) >= guardR1
        /\ \E i \in SUBSET Proc: /\ Cardinality(i) = guardR2
                                 /\ \A j \in {k \in i: isByz[k] = 0}: \/ step[j] = MAINVOTE0
                                                                      \/ step[j] = MAINVOTE1
                                                                      \/ step[j] = MAINVOTEx
                                 /\ ~\A j \in i: sent[j][sender][MAINVOTE1] = 1
                                 /\ ~\A j \in i: sent[j][sender][MAINVOTE0] = 1
     \/ VoteSum(sender, MAINVOTEx) >= guardR2
  /\ step' = [step EXCEPT ![sender] = FINALVOTEx]
  /\ sent' = [sent EXCEPT ![sender] = [i \in Proc |-> [s \in Step |-> IF s = FINALVOTEx THEN 1 ELSE sent[sender][i][s]]]]
  /\ UNCHANGED << isByz, prevoteState, nextPrevote, decide >>

Consume(sender) ==
  /\ decide[sender] = UNDEFINED
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
  /\ \/ prevoteState[i] = BSET1
     \/ prevoteState[i] = BSET01
  /\ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                           /\ \A j \in x: sent[j][i][FINALVOTE1] = 1
  /\ decide' = [decide EXCEPT ![i] = DECIDE1]
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED << step, sent, prevoteState, isByz >>

Decide0(i) ==
  /\ \/ prevoteState[i] = BSET0
     \/ prevoteState[i] = BSET01
  /\ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                           /\ \A j \in x: sent[j][i][FINALVOTE0] = 1
  /\ decide' = [decide EXCEPT ![i] = DECIDE0]
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE0]
  /\ UNCHANGED << step, sent, prevoteState, isByz >>

NextPrevote0(i) ==
  /\ VoteSum(i, MAINVOTE0) >= guardR1
  /\ prevoteState[i] = BSET01
  /\ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                           /\ \A j \in x: \/ sent[j][i][FINALVOTE0] = 1 
                                          \/ sent[j][i][FINALVOTEx] = 1
                           /\ \E j \in x: sent[j][i][FINALVOTEx] = 1
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE0]
  /\ UNCHANGED << step, sent, prevoteState, isByz, decide >>

NextPrevote1(i) ==
  /\ VoteSum(i, MAINVOTE1) >= guardR1
  /\ prevoteState[i] = BSET01
  /\ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                           /\ \A j \in x: \/ sent[j][i][FINALVOTE1] = 1 
                                          \/ sent[j][i][FINALVOTEx] = 1
                           /\ \E j \in x: sent[j][i][FINALVOTEx] = 1
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTE1]
  /\ UNCHANGED << step, sent, prevoteState, isByz, decide >>

NextPrevoteRandom(i) ==
  /\ prevoteState[i] = BSET01
  /\ \/ /\ VoteSum(i, MAINVOTE1) >= guardR1
        /\ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                                  /\ \A j \in x: /\ \/ sent[j][i][FINALVOTE1] = 1 
                                                    \/ sent[j][i][FINALVOTEx] = 1
                                  /\ ArrSum([s \in Proc |-> IF s \in x THEN sent[s][i][FINALVOTE1] ELSE 0]) < guardR1
     \/ /\ VoteSum(i, MAINVOTE0) >= guardR1
        /\ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                                  /\ \A j \in x: /\ \/ sent[j][i][FINALVOTE0] = 1
                                                    \/ sent[j][i][FINALVOTEx] = 1
                                  /\ ArrSum([s \in Proc |-> IF s \in x THEN sent[s][i][FINALVOTE0] ELSE 0]) < guardR1
     \/ \E x \in SUBSET Proc: /\ Cardinality(x) = guardR2
                              /\ \A j \in x: sent[j][i][FINALVOTEx] = 1
  /\ nextPrevote' = [nextPrevote EXCEPT ![i] = NEXTPREVOTEx]
  /\ UNCHANGED << step, sent, prevoteState, isByz, decide >>

Decide(i) ==
  /\ decide[i] = UNDEFINED
  /\ \/ /\ nextPrevote[i] = UNDEFINED
        /\ \/ step[i] = FINALVOTE0
           \/ step[i] = FINALVOTE1
           \/ step[i] = FINALVOTEx
        /\ \/ Decide1(i)
           \/ Decide0(i)
           \/ NextPrevote0(i)
           \/ NextPrevote1(i)
           \/ NextPrevoteRandom(i)
     \/ /\ nextPrevote[i] # UNDEFINED
        /\ \A j \in {l \in Proc: isByz[l] = 0}: nextPrevote[j] # UNDEFINED
        /\ \/ \A j \in {l \in Proc: isByz[l] = 0}: nextPrevote[j] = NEXTPREVOTE0
              (* eventually decide0 *)
              /\ decide' = [decide EXCEPT ![i] = DECIDE0]
           \/ \A j \in {l \in Proc: isByz[l] = 0}: nextPrevote[j] = NEXTPREVOTE1
              (* eventually decide1 *)
              /\ decide' = [decide EXCEPT ![i] = DECIDE1]
           \/ \E j \in {l \in Proc: isByz[l] = 0}: nextPrevote[j] = NEXTPREVOTEx
              (* eventually decidex *)
              /\ decide' = [decide EXCEPT ![i] = DECIDEx]
        /\ UNCHANGED << step, sent, prevoteState, isByz, nextPrevote >>

Next ==
  \/ /\ step[1] = UNDEFINED
     /\ \E i \in {j \in Proc: isByz[j] = 1}:
        \/ \E k \in {l \in Proc: isByz[l] = 0}:
            \/ \E s \in {MAINVOTE0, MAINVOTE1, FINALVOTE0, FINALVOTE1}:
                /\ sent[i][k][s] = 0
                /\ sent' = [sent EXCEPT ![i] = [m \in Proc |-> IF m = k THEN [_s \in Step |-> IF s = _s THEN 1 ELSE sent[i][m][_s]] ELSE sent[i][m]]]
     /\ UNCHANGED << prevoteState, isByz, decide, nextPrevote, step >>
  \/ /\ step[1] = UNDEFINED
     /\ step' = [step EXCEPT ![1] = PREVOTE]
     /\ UNCHANGED << prevoteState, isByz, decide, nextPrevote, sent >>
  \/ /\ step[1] # UNDEFINED
     /\ \E self \in {x \in Proc: isByz[x] = 0} :
        \/ Consume(self)
        \/ Decide(self)
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in {j \in Proc: isByz[j] = 0} : \/ Consume(self)
                                           \/ Decide(self))

(* Liveness and correctness check *)


(* It's obvious that once every honest node prevotes v, eventually, every honest node will mainvote v. *)

(* If all correct replicas propose iv[r] = v in round r, then any correct replica that enters round r + 1 sets iv[r+1] as v. *)
Lemma9 ==
  /\ []((\A i \in {j \in Proc: isByz[j] = 0}: step[i] = MAINVOTE0 /\ prevoteState[i] = BSET0) => <>(\A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE0 ))
  /\ []((\A i \in {j \in Proc: isByz[j] = 0}: step[i] = MAINVOTE1 /\ prevoteState[i] = BSET1) => <>(\A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE1 ))

(* If all correct replicas propose v in round r, then for any r′ > r , any correct replica that enters round r′ sets ivr′ as v.*)
(* Lemma10 *)

(* If a correct replica pi sends final-voter(v), at least one correct replica has proposed ivr = v ̄ and broadcast pre-voter (v ̄). *)
(* Lemma11 *)

(* If all correct replicas propose v, then any correct replica that terminates decides v. *)
Theorem12 ==
  /\ []((\A i \in {j \in Proc: isByz[j] = 0}: step[i] = MAINVOTE1) => <>(~\E i \in {j \in Proc: isByz[j] = 0} : decide[i] = DECIDE0 ))
  /\ []((\A i \in {j \in Proc: isByz[j] = 0}: step[i] = MAINVOTE0) => <>(~\E i \in {j \in Proc: isByz[j] = 0} : decide[i] = DECIDE1 ))

(* If a correct replica pi sends main-vote_r(v), any correct replica p_j only sends main-vote_r(v) or main-vote_r[∗] *)
Lemma13 ==
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: step[i] = MAINVOTE0) => <>(\A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE0 \/ nextPrevote[i] = NEXTPREVOTEx))
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: step[i] = MAINVOTE1) => <>(\A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE1 \/ nextPrevote[i] = NEXTPREVOTEx))

(* If a correct replica pi sends final-voter(v), any correct replica p_j only sends final-vote_r(v) or final-vote_r(x). *)
(* Lemma14 *)

(* If a correct replica pi decides v in round r , any correct replica that enters round r + 1 sets ivr+1 as v. *)
Lemma15 ==
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: decide[i] = DECIDE0) => <>(\A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE0))
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: decide[i] = DECIDE1) => <>(\A i \in {j \in Proc: isByz[j] = 0} : nextPrevote[i] = NEXTPREVOTE1))

(* If a correct replica decides v, then any correct replica that terminates decides v *)
Theorem16 == 
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: decide[i] = DECIDE0) => <>(\A i \in {j \in Proc: isByz[j] = 0} : decide[i] = DECIDE0))
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: decide[i] = DECIDE1) => <>(\A i \in {j \in Proc: isByz[j] = 0} : decide[i] = DECIDE1))
  /\ []((\E i \in {j \in Proc: isByz[j] = 0}: decide[i] = DECIDEx) => <>(\A i \in {j \in Proc: isByz[j] = 0} : decide[i] = DECIDEx))

(* If a correct replica pi sends voter(v) for v ∈ {0,1}, any correct replica eventually accepts voter(v). *)
(* Lemma17 *)

(* If a correct replica pi broadcasts a main-voter(v) or a main-voter(∗) message given that v ∈ {0,1}, any correct replica accepts the main-voter() message from pi. *)
(* Lemma18 *)

(* If a correct replica pi broadcasts a final-voter (v) or a final-voter (∗) message given that v ∈ {0, 1}, any correct replica accepts the final-voter () message. *)
(* Lemma19 *)

(* Let v1 ∈ {0,1} and v2 ∈ {0,1}. If a correct replica pi receives only n − f final-voter(x) and final-vote_r(v1) messages, another correct replica p_j only receives n− f final-vote_r(v2) and final-voter(x) messages, v1 = v2. *)
(* Lemma20 *)

(* Every correct replica eventually decides some value. *)
Theorem21 == 
   []<>( \/ \A i \in {j \in Proc: isByz[j] = 0} : \/ decide[i] = DECIDE0
                                                  \/ decide[i] = DECIDE1
                                                  \/ decide[i] = DECIDEx
       )

(* No correct replica decides twice. *)
(* Theorem22 *)

=============================================================================
