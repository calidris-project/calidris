module peano.inequality where 

import peano.nat 
import peano.add
import logic as l 

greaterThan = fun a : nat => fun b : nat => l.exists nat (fun n : nat => natEqual (add b (succ n)) a);
greaterThanEq = fun a : nat => fun b : nat => l.exists nat (fun n : nat => natEqual (add b n) a);



gtImpGte : forall a : nat, forall b : nat, l.implies (greaterThan a b) (greaterThanEq a b)
         =  fun a : nat => fun b : nat => fun p : greaterThan a b 
         => p (greaterThanEq a b)
         (fun n : nat => fun p2 : natEqual (add b (succ n)) a => 
        fun t : Prop => fun pa : (forall v : nat, forall p5 : natEqual (add b v) a, t) 
         => pa (succ n) p2
         );
-- need universe polymorphism aaaaaaaaaaaaaaah