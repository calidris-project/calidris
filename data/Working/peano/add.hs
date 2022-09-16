module peano.add where 

import peano.nat

add : forall a : nat, forall b : nat, nat; 
addZero : forall a : nat, natEqual (add a 0) a;
addInd : forall a : nat, forall b : nat, natEqual (add a (succ b)) (succ (add a b));

addZero1 : forall a : nat, natEqual (add 0 a) a
         = induction (fun a : nat => natEqual (add 0 a) a)
         (addZero 0) (fun a : nat => fun p : natEqual (add 0 a) a => 
            let t1 = add 0 (succ a) in let t2 = succ (add 0 a) in let t3 = succ a 
         in let e1 : natEqual t1 t2 = addInd 0 a 
         in let e2 : natEqual t2 t3 = leib succ (add 0 a) a p 
         in natTrans t1 t2 t3 e1 e2);





assocHyp = fun x : nat => fun y : nat => fun z : nat => natEqual (add (add x y) z) (add x (add y z));

addAssoc : forall a : nat, forall b : nat, forall c : nat, assocHyp a b c
         = fun a : nat => fun b : nat =>  
         induction (assocHyp a b)
         (  let t1 = add (add a b) 0 in let t2 = add a b in let t3 = add a (add b 0) 
         in let e1 : natEqual t1 t2 = addZero t2 
         in let e2 : natEqual t2 t3 = leib (add a) b (add b 0) (natSymm (add b 0) b (addZero b))
         in natTrans t1 t2 t3 e1 e2
            )
        (fun c : nat => fun p : assocHyp a b c => 
            let eq = natEqual 
         in let s = succ 
         in let + = add
         in let addSInd 
            = fun j : nat => fun k : nat => natSymm (+ j (s k)) (s (+ j k)) (addInd j k)
         in let t1 = + (+ a b) (s c)
         in let t2 = s (+ (+ a b) c)
         in let t3 = s (+ a (+ b c))
         in let t4 = + a (s (+ b c))
         in let t5 = + a (+ b (s c))
         in let e1 : eq t1 t2 = addInd (+ a b) c 
         in let e2 : eq t2 t3 = leib s (+ (+ a b) c) (+ a (+ b c)) p 
         in let e3 : eq t3 t4 = addSInd a (+ b c)
         in let e4 : eq t4 t5 = leib (add a) (s (+ b c)) (+ b (s c)) (addSInd b c)
         in natTrans t1 t2 t5 e1 (natTrans t2 t3 t5 e2 (natTrans t3 t4 t5 e3 e4)));


commSuccHyp = fun x : nat => fun y : nat => natEqual (add (succ x) y) (succ (add x y)); 

commSucc : forall a : nat, forall b : nat, natEqual (add (succ a) b) (succ (add a b))
         = let eq = natEqual 
         in let s = succ  
         in let + = add
         in fun a : nat 
         => induction (commSuccHyp a)
         (  let t1 = + (s a) 0 in let t2 = s a in let t3 = s (+ a 0)
         in let e1 : eq t1 t2 = addZero (s a)
         in let e2 : eq t2 t3 = leib s a (+ a 0) (natSymm (+ a 0) a (addZero a))
         in natTrans t1 t2 t3 e1 e2
         ) 
         ( fun b : nat => fun p : commSuccHyp a b => 
           let t1 = + (s a) (s b) in let t2 = s (+ (s a) b) in let t3 = s (s (+ a b))
           in let t4 = s (+ a (s b))
           in let eq1 : eq t1 t2 = addInd (s a) b
           in let eq2 : eq t2 t3 = leib s (+ (s a) b) (s (+ a b)) p 
           in let eq3 : eq t3 t4 = leib s 
                  (s (+ a b))
                  (+ a (s b))  
                  (natSymm (+ a (s b)) (s (+ a b)) (addInd a b))
           in natTrans t1 t2 t4 eq1 (natTrans t2 t3 t4 eq2 eq3)
         );


commHyp = fun x : nat => fun y : nat => natEqual (add x y) (add y x);

addComm : forall a : nat, forall b : nat, natEqual (add a b) (add b a)
        = 
         let eq = natEqual 
         in let s = succ  
         in let + = add
       in  fun a : nat => induction (commHyp a) 
        ( let t1 = + a 0 in let t2 = a in let t3 = + 0 a
          in let eq1 : eq t1 t2 = addZero a 
          in let eq2 : eq t2 t3 = natSymm (+ 0 a) a (addZero1 a)
          in natTrans t1 t2 t3 eq1 eq2)
       ( fun b : nat => fun p : commHyp a b => 
           let t1 = + a (s b) in let t2 = s (+ a b) in let t3 = s (+ b a) in let t4 = + (s b) a 
           in let eq1 : eq t1 t2 = addInd a b 
           in let eq2 : eq t2 t3 = leib s (+ a b) (+ b a) p
           in let eq3 : eq t3 t4 = natSymm (+ (s b) a) (s (+ b a)) (commSucc b a)
           in natTrans t1 t2 t4 eq1 (natTrans t2 t3 t4 eq2 eq3)) ;

            
