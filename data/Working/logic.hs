module logic where 

not = fun a : Prop => forall b : a, bottom;

implies = fun a : Prop => fun b : Prop => forall x : a, b;
and = fun a : Prop => fun b : Prop => forall c : Prop, implies (implies a (implies b c)) c;
a_and_b_implies_b_and_a 
      : forall a : Prop, forall b : Prop, 
        implies (and a b) (and b a)
    = 
        fun a : Prop => fun b : Prop => 
        fun anb : and a b => 
        fun c : Prop =>  
        fun f : (forall bp : b, forall ap : a, c) => 
        anb c (fun ap : a => fun bp : b => f bp ap)
        ;

bottom = forall a : Prop, a; 

exists 
  =  fun a : Set
  => fun propGen : (forall b : a, Prop) 
  => forall c : Prop
  ,  forall proofAccepter : (forall v : a, forall p : propGen v, c)  
  , c; 

