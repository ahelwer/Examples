---------- MODULE MCEcho ----------
EXTENDS Echo

\* A tiny graph with three nodes.
N1 ≜ {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 ≜ CHOOSE n ∈ N1 : TRUE

\* The tiny graph is fully meshed: 
\*      <<"a", "a">> :> FALSE @@
\*      <<"a", "b">> :> TRUE  @@
\*      <<"b", "a">> :> TRUE  @@
\*      <<"b", "b">> :> FALSE @@
\*      <<"a", "c">> :> TRUE @@
\*      <<"c", "a">> :> TRUE @@
\*      <<"b", "c">> :> TRUE  @@
\*      <<"c", "b">> :> TRUE  @@
\*      <<"c", "c">> :> FALSE
\* More concisely defined as:
R1 ≜ [ edge ∈ (N1 × N1) ↦ IF edge[1] = edge[2] 
                                THEN FALSE
                                ELSE TRUE ]

\* To get a graph that satisfies the
\* assumptions in Echo, we simply 
\* define R to be:
R2 ≜ CHOOSE r ∈ [ N1 × N1 → BOOLEAN ] : 
        ∧ IsConnected(r, N1)
        ∧ IsSymmetric(r, N1)
        ∧ IsIrreflexive(r, N1)

\* Print R to stdout at startup.
TestSpec ≜ PrintT(R) ∧ Spec        
===================================