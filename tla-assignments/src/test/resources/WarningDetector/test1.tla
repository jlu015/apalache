---------------------- MODULE test1 ----------------------
CONSTANT e,f,g
VARIABLE a,b,c,d,x,y,z

Next == /\ a' \in {1}
        /\ ~(b' \in {2} /\ b \in {3})
       
Init == a = 0
        
Spec == [][Next]_<< a,b >>     
==============================================================

