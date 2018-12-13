--------------- MODULE test2 -------------
EXTENDS Naturals
VARIABLE x, y

A(p) == LET D(q) == q + 1
        IN D(p)

Next == x' = A(x) /\ UNCHANGED y
============================================