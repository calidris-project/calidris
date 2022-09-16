module peano.nat where 

import logic as l


nat : Set; 
0 : nat; 
succ : forall a : nat, nat; 

natEqual : forall a : nat, forall b : nat, Prop; 
natRefl : forall a : nat, natEqual a a ; 
natSymm : forall a : nat, forall b : nat, forall p : natEqual a b, natEqual b a; 
natTrans : forall a : nat, forall b : nat, forall c : nat, forall p1 : natEqual a b, forall p2 : natEqual b c, natEqual a c; 
succNEZ : forall a : nat, l.not (natEqual (succ a) 0); 
natConv2 : forall a : nat, forall b : nat, forall p1 : natEqual (succ a) (succ b), natEqual a b;




induction : forall p : (forall n : nat, Prop), 
    forall base : p 0, 
    forall step : (forall n : nat, forall p1 : p n, p (succ n)), 
    forall n : nat, p n;

natF = forall n : nat, nat;

leibPredicate
    = fun f : natF
    => fun a : nat => fun b : nat => forall p1 : natEqual a b, natEqual (f a) (f b);

flipPredicate : forall f : natF, forall b : nat, 
                    forall toFlip : (forall a : nat, leibPredicate f a b), forall a : nat, leibPredicate f b a 
              = fun f : natF => fun b : nat => fun toFlip : (forall a : nat, leibPredicate f a b) => fun a : nat => fun p1 : natEqual b a => 
                    natSymm (f a) (f b) (toFlip a (natSymm b a p1))
            ;

baseCaseLeib : forall f : natF, forall a : nat, leibPredicate f 0 a
     =   fun f : natF => 
        flipPredicate f 0 (
            let p = fun a : nat => leibPredicate f a 0 in
                induction p
                (fun p1 : natEqual 0 0 => natRefl (f 0))
               (fun a : nat => fun p1 : p a => fun p2 : natEqual (succ a) 0 => succNEZ a p2 (natEqual (f (succ a)) (f 0)))
        );

liftCaseLeib : forall a : nat, forall prevP : (forall f : natF, forall b : nat, leibPredicate f a b), forall f : natF, forall b : nat, leibPredicate f (succ a) b 
     = fun a : nat => fun prevP : (forall f : natF, forall b : nat, leibPredicate f a b)
         => fun f : natF 
         => let p = fun b : nat => leibPredicate f (succ a) b in
         induction p 
         (fun p1 : natEqual (succ a) 0 => succNEZ a p1 (natEqual (f (succ a)) (f 0)))
         (fun b : nat => fun p1 : p b => fun p2 : natEqual (succ a) (succ b) 
        => prevP (fun x : nat => f (succ x)) b (natConv2 a b p2));

leib : forall f : natF, forall a : nat, forall b : nat, forall p1 : natEqual a b, natEqual (f a) (f b) 
    = fun f1 : natF => fun a1 : nat =>
        let p = fun a : nat => forall f : natF, forall b : nat, leibPredicate f a b in
        induction p baseCaseLeib liftCaseLeib a1 f1; 



1 = succ 0; 
2 = succ 1; 
3 = succ 2; 
4 = succ 3; 
5 = succ 4; 
6 = succ 5; 
7 = succ 6; 
8 = succ 7; 
9 = succ 8; 
