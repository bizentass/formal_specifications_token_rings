------------------------------- MODULE 3state -------------------------------
\* AUTHORS
\* Charuvahan Adhivarahan (charuvah@buffalo.edu) (UB Person#: 50168105)
\* Lalith Vikram Natarajan (lalithvi@buffalo.edu) (UB Person#: 50169243)

EXTENDS Integers, FiniteSets
CONSTANT N
ASSUME N \in Nat \ {0,1}
Procs == 1..(N-1)

Numberize(S) == IF S = TRUE THEN 1 ELSE 0

(* Dijkstra's 3 state
--algorithm 3state {
   variable c = [i \in 0..N |-> Numberize(i=0)];
   \*variable c = [i \in 0..N |-> ((i+1)%3)];
   fair process (i \in {0})
   {   I0: c[0] := 1;
       I1: while (TRUE)
           { 
             await (((c[0]+1)%3) = c[1]);
             c[0] := (c[1]+1)%3;    
           }
   }
   fair process (n \in {N})
   {   
       N1: while (TRUE)
           { 
             await ( (c[(N-1)] = c[0]) /\ (c[N]/=((c[N-1]+1)%3)) );
             c[N] := (c[(N-1)]+1)%3;
           }
   }
   fair process (j \in Procs)
   {   
        J1: while (TRUE)
        {
             either
                { 
                    await (((c[self]+1)%3) = c[(self-1)]);
                    c[self] := c[(self-1)];
                }
             or 
                {   
                    await (((c[self]+1)%3) = c[(self+1)]);
                    c[self] := c[(self+1)];
                }
        }
   }
} *)

\* BEGIN TRANSLATION
VARIABLES c, pc

vars == << c, pc >>

ProcSet == ({0}) \cup ({N}) \cup (Procs)

Init == (* Global variables *)
        /\ c = [i \in 0..N |-> Numberize(i=0)]
        /\ pc = [self \in ProcSet |-> CASE self \in {0} -> "I0"
                                        [] self \in {N} -> "N1"
                                        [] self \in Procs -> "J1"]

I0(self) == /\ pc[self] = "I0"
            /\ c' = [c EXCEPT ![0] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I1"]

I1(self) == /\ pc[self] = "I1"
            /\ (((c[0]+1)%3) = c[1])
            /\ c' = [c EXCEPT ![0] = (c[1]+1)%3]
            /\ pc' = [pc EXCEPT ![self] = "I1"]

i(self) == I0(self) \/ I1(self)

N1(self) == /\ pc[self] = "N1"
            /\ ( (c[(N-1)] = c[0]) /\ (c[N]/=((c[N-1]+1)%3)) )
            /\ c' = [c EXCEPT ![N] = (c[(N-1)]+1)%3]
            /\ pc' = [pc EXCEPT ![self] = "N1"]

n(self) == N1(self)

J1(self) == /\ pc[self] = "J1"
            /\ \/ /\ (((c[self]+1)%3) = c[(self-1)])
                  /\ c' = [c EXCEPT ![self] = c[(self-1)]]
               \/ /\ (((c[self]+1)%3) = c[(self+1)])
                  /\ c' = [c EXCEPT ![self] = c[(self+1)]]
            /\ pc' = [pc EXCEPT ![self] = "J1"]

j(self) == J1(self)

Next == (\E self \in {0}: i(self))
           \/ (\E self \in {N}: n(self))
           \/ (\E self \in Procs: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0} : WF_vars(i(self))
        /\ \A self \in {N} : WF_vars(n(self))
        /\ \A self \in Procs : WF_vars(j(self))

\* END TRANSLATION
T_0 == IF ( ((c[0]+1)%3) = c[1] ) THEN 1 ELSE 0
T_N == IF ( (c[(N-1)] = c[0]) /\ (c[N]/=((c[N-1]+1)%3)) ) THEN 1 ELSE 0
T == Cardinality({k \in Procs: ( (((c[k]+1)%3)=c[k-1]) \/ (((c[k]+1)%3)=c[k+1]) ) }) + T_0 + T_N
Invariant == T = 1
Stabilization == []<> Invariant
LowerBound == T >= 1
DoesNotMoveAway == [][T' <= T]_vars
MovesTowards == \A M \in 1..N+1: []<> (T <= M)
=============================================================================
\* Modification History
\* Last modified Sun Dec 13 01:56:17 EST 2015 by chartoin
\* Created Sun Dec 13 01:05:05 EST 2015 by chartoin
