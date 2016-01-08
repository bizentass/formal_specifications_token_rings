------------------------------- MODULE 4state -------------------------------
\* AUTHORS
\* Charuvahan Adhivarahan (charuvah@buffalo.edu) (UB Person#: 50168105)
\* Lalith Vikram Natarajan (lalithvi@buffalo.edu) (UB Person#: 50169243)

EXTENDS Integers, FiniteSets
CONSTANT N
ASSUME N \in Nat \ {0,1}
Procs == 1..(N-1) (* Or 0..N should J be equal to procs or not? *)

Numberize(S) == IF S = TRUE THEN 1 ELSE 0

(* Dijkstra's 4 state
--algorithm 4state {
    variable up = [i \in 0..N |-> Numberize(i=0)], c = [i \in 0..N |-> 0];
    \* variable up = [i \in 0..N |-> Numberize((i%2)=0)], c = [i \in 0..N |-> (i%2)];
   fair process (i \in {0})
   {   I0: up[self] := 1; 
       I1: while (TRUE)
           { await ((c[0] = c[1]) /\ up[1]=0);
             c[0] := (c[0]+1)%2;    
           }
   }
   fair process (n \in {N})
   {   
       N0: up[self] := 0;
       N1: while (TRUE)
           { await (c[(N-1)] /= c[N]);
             c[N] := c[(N-1)];
           }
   }
   fair process (j \in Procs)
   {    
        J1: while (TRUE)
        {
             either
                { await (c[self] /= c[(self -1)]);
                    c[self] := c[(self-1)];
                    up[self] := 1; 
                }
             or 
                { await ((c[(self)] = c[(self+1)]) /\ up[(self+1)]=0 /\ up[self]=1);
                    up[self] := 0;
                }
        }
   }  
} *)

\* BEGIN TRANSLATION
VARIABLES up, c, pc

vars == << up, c, pc >>

ProcSet == ({0}) \cup ({N}) \cup (Procs)

Init == (* Global variables *)
        /\ up = [i \in 0..N |-> Numberize(i=0)]
        /\ c = [i \in 0..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in {0} -> "I0"
                                        [] self \in {N} -> "N0"
                                        [] self \in Procs -> "J1"]

I0(self) == /\ pc[self] = "I0"
            /\ up' = [up EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I1"]
            /\ c' = c

I1(self) == /\ pc[self] = "I1"
            /\ ((c[0] = c[1]) /\ up[1]=0)
            /\ c' = [c EXCEPT ![0] = (c[0]+1)%2]
            /\ pc' = [pc EXCEPT ![self] = "I1"]
            /\ up' = up

i(self) == I0(self) \/ I1(self)

N0(self) == /\ pc[self] = "N0"
            /\ up' = [up EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "N1"]
            /\ c' = c

N1(self) == /\ pc[self] = "N1"
            /\ (c[(N-1)] /= c[N])
            /\ c' = [c EXCEPT ![N] = c[(N-1)]]
            /\ pc' = [pc EXCEPT ![self] = "N1"]
            /\ up' = up

n(self) == N0(self) \/ N1(self)

J1(self) == /\ pc[self] = "J1"
            /\ \/ /\ (c[self] /= c[(self -1)])
                  /\ c' = [c EXCEPT ![self] = c[(self-1)]]
                  /\ up' = [up EXCEPT ![self] = 1]
               \/ /\ ((c[(self)] = c[(self+1)]) /\ up[(self+1)]=0 /\ up[self]=1)
                  /\ up' = [up EXCEPT ![self] = 0]
                  /\ c' = c
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

T_0 == IF ((c[0] = c[1]) /\ (up[1] = 0)) THEN 1 ELSE 0
T_N == IF c[N] /= c[N-1] THEN 1 ELSE 0
T == Cardinality({k \in Procs: (c[k] /= c[k-1]) \/ ( (c[k]=c[k+1]) /\ (up[k]=1) /\ (up[k+1]=0) )}) + T_0 + T_N
Invariant == T = 1
Stabilization == []<> Invariant
LowerBound == T >= 1
DoesNotMoveAway == [][T' <= T]_vars
MovesTowards == \A M \in 1..N+1: []<> (T <= M)

=============================================================================
\* Modification History
\* Last modified Sun Dec 13 01:56:07 EST 2015 by chartoin
\* Created Fri Dec 11 19:03:34 EST 2015 by charuvah
