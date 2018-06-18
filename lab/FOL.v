(** First order logic *)

Section A_declared.
 Variables (A : Set)
   (P Q : A -> Prop)
   (R : A -> A -> Prop).

 Theorem all_comm : (forall a b:A, R a b) -> forall a b:A, R b a.
 Proof.
 Admitted.

 Theorem all_imp_dist :
  (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
 Proof.
 Admitted.

 Theorem all_delta : (forall a b:A, R a b) -> forall a:A, R a a.
 Proof.
 Admitted.


 Theorem ex_or_dist : (exists x:A, P x \/ Q x)  -> (exists x: A, P x) \/ 
                                                   (exists x: A, Q x).
 Proof.
 Admitted.


 
 Theorem no_ex_forall : ~(exists x:A, P x) -> forall x:A, ~ P x.
 Proof.
 Admitted.

 
 Theorem non_empty_forall_ex : (exists x:A, x = x) ->
                               (forall x:A, P x) ->
                               exists x:A, P x.
 Proof.
 Admitted.


 Theorem singleton : (exists x:A, forall y:A, x = y) ->
                     forall z t:A, z = t.
 Proof.
 Admitted.

  
 
End A_declared.



