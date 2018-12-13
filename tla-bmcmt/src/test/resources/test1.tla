--------------- MODULE test1 -------------
EXTENDS Naturals
VARIABLE x, y, z, w

Init ==
  /\ x = {1, 2, 3}
  /\ y = {"a", "b", "c"}
  /\ z = [a : {1, 2, 3}, b : {1, 2, 3}, c : {1, 2, 3}]
  /\ w = [{1, 2, 3} -> {1, 2, 3}]

A == x >= 0

B(p) == IF y >= p
        THEN z
        ELSE w

Next == A /\ y' = B(x) /\ UNCHANGED <<x, z, w>>
============================================