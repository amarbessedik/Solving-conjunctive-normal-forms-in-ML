(*---------------------------------------------------------------------------*) 
(* TESTING EXAMPLES *) 



val f1 = P;
val f2 = ~(P);
val f3 = ~(~(P));
val f4 = ~(~(~(P)));
val f5 = P v ~ P;
val f6 = P --> Q;
val f7 = P <-> Q;
val f8 = (P v Q) --> P;
val f9 = (S & T) v (Q & R);
val f10 = ~S & ~T;
val f11 = ~(P --> (~Q --> ~P));
val f12 = (P --> Q) & (Q --> R);
val f13 = ((P --> Q) &  (Q --> R))  -->  (P --> R);
val f14 = ~(((P --> ~Q) v (~P & ~Q)));
val f15 = ((P & Q) --> P);
val f16 = (P & Q) v (R & S);
val f17 = ((P --> Q) --> (~Q --> ~P));
val f18 = ((P --> ~Q) v (~P & ~Q));
val f19 = ((P --> Q) <-> (~Q --> ~P));
val f20 = ~((P --> ~Q) <-> (~P & ~Q));
val f21 = ~((P --> ~Q)  v  (~P & ~Q));
val f22 = ~(~(((P --> Q) & (Q --> R)) --> (P --> R)));
val f23 = (P --> Q) v (Q --> R);
val f24 = ((P --> Q) &  (Q --> R))  -->  (P --> R);
val f25 = ((P & Q) v (~ P & ~ R)) v ((S & T v (~ Q & ~ P)));



val tests = [f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14,f15,f16,f17,f18,f19,f20,f21,f22,f23,f24,f25];


(* END *)
(*---------------------------------------------------------------------------*) 
