Lemma FirstLemma: forall A B C: Prop, (A -> B -> C) -> (A -> B) -> (A -> C).
(*intros.*)
intros A B C X Y Z.

apply X.

assumption.

apply Y.
assumption.
Qed.

Print FirstLemma.



(* In natural deduction

G, A |- B
-------------------- (-> intro) 
G |- A -> B


G |- A -> B      G |- A
-------------------------(-> elim) (application rule)
G |- B

*)