------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Dijkstra, published as EWD 840:             *)
(* Derivation of a termination detection algorithm for distributed         *)
(* computations (with W.H.J.Feijen and A.J.M. van Gasteren).               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                   \* token position
  /\ tcolor \in Color                 \* token color

(***************************************************************************)
(* Initially the token is black. The other variables may take any          *)
(* "type-correct" values.                                                  *)
(***************************************************************************)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

(***************************************************************************)
(* Node 0 may initiate a probe when it has the token and when either it is *)
(* black or the token is black. It passes a white token to node N-1 and    *)
(* paints itself white.                                                    *)
(***************************************************************************)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(***************************************************************************)
(* A node i different from 0 that possesses the token may pass it to node  *)
(* i-1 under the following circumstances:                                  *)
(*   - node i is inactive or                                               *)
(*   - node i is colored black or                                          *)
(*   - the token is black.                                                 *)
(* Note that the last two conditions will result in an inconclusive round, *)
(* since the token will be black. The token will be stained if node i is   *)
(* black, otherwise its color is unchanged. Node i will be made white.     *)
(***************************************************************************)
PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(***************************************************************************)
(* token passing actions controlled by the termination detection algorithm *)
(***************************************************************************)
System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(***************************************************************************)
(* An active node i may activate another node j by sending it a message.   *)
(* If j>i (hence activation goes against the direction of the token being  *)
(* passed), then node i becomes black.                                     *)
(***************************************************************************)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE color[i]]
  /\ UNCHANGED <<tpos, tcolor>>

(***************************************************************************)
(* Any active node may become inactive at any moment.                      *)
(***************************************************************************)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(***************************************************************************)
(* actions performed by the underlying algorithm                           *)
(***************************************************************************)
Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

(***************************************************************************)
(* next-state relation: disjunction of above actions                       *)
(***************************************************************************)
Next == System \/ Environment

vars == <<active, color, tpos, tcolor>>

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

=============================================================================
\* Modification History
\* Last modified Tue Jun 28 18:17:45 CEST 2016 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
