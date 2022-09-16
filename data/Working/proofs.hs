module proofs where 

import peano.nat
import peano.add
import peano.inequality

succ2 = fun x : nat => succ (succ x); 
succ3 = fun x : nat => succ (succ2 x); 

proof_step1 : natEqual (add 2 3) (succ (add 2 2))
            = addInd 2 2;
proof_step2 : natEqual (succ (add 2 2)) (succ2 (add 2 1))
            = leib succ (add 2 2) (succ (add 2 1)) (addInd 2 1);
proof_step3 : natEqual (succ2 (add 2 1)) (succ3 (add 2 0))
            = leib succ2 (add 2 1) (succ (add 2 0)) (addInd 2 0); 
proof_step4 : natEqual (succ3 (add 2 0)) 5
            = leib succ3 (add 2 0) 2 (addZero 2);
t1 = add 2 3; t2 = succ (add 2 2); t3 = succ2 (add 2 1); t4 = succ3 (add 2 0);

2_plus_3_is_5 : natEqual (add 2 3) 5 
    = natTrans t1 t2 5 proof_step1 (
      natTrans t2 t3 5 proof_step2 (
      natTrans t3 t4 5 proof_step3 (
                       proof_step4 
    )));

3_plus_2_is_5 : natEqual (add 3 2) 5
    = natTrans (add 3 2) (add 2 3) 5 (addComm 3 2) 2_plus_3_is_5;



5_gt_2 : greaterThan 5 2 
    = fun c : Prop => fun acc : (forall v : nat, forall p : natEqual (add 2 (succ v)) 5, c)
    => acc 2 (2_plus_3_is_5);
