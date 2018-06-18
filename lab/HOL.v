(** This first serie of  exercises asks you to prove some derived
    inference rule. For some of them, build a small example of its application. 


First, let us look at some example : *)

Lemma P3Q : forall P Q : Prop, (((P->Q)->Q)->Q) -> P -> Q.
Proof.
 intros P Q H p; apply H. 
 intro H0;apply H0;assumption. 
Qed.

Lemma triple_neg : forall P:Prop, ~~~P -> ~P.
Proof.
 intros P ;unfold not; apply P3Q.
Qed.



Lemma not_or_1 : forall P Q : Prop, ~(P \/ Q) -> ~P.
Proof.
Admitted.
 
Section not_or_1_example.
 Variable n : nat.
 Hypothesis H : n=0 \/ n =2 -> n <> n.
 
 Lemma L1 : ~n=0.
 Proof.
 Admitted.

 End not_or_1_example.



Lemma all_perm :
 forall (A:Type) (P:A -> A -> Prop),
   (forall x y:A, P x y) -> 
   forall x y:A, P y x.
Proof.
Admitted.

Lemma resolution :
 forall (A:Type) (P Q R S:A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> 
   forall c:A, P c -> R c -> S c.
Proof.
Admitted.


Lemma not_ex_forall_not : forall (A: Type) (P: A -> Prop),
                      ~(exists x, P x) <-> forall x, ~ P x.
Proof.
Admitted.


Lemma ex_not_forall_not : forall (A: Type) (P: A -> Prop),
                       (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
Admitted.


Lemma diff_sym : forall (A:Type) (a b : A), a <> b -> b <> a.
Proof.
Admitted.


Lemma fun_diff :  forall (A B:Type) (f : A -> B) (a b : A), 
                       f a <> f b -> a <> b.
Proof.
Admitted.


(**  this exercise deals with five equivalent characterizations of 
     classical logic 

   Some  solutions may use the following patterns :
    unfold Ident [in H].
    destruct (H t1 ... t2)
    generalize t.
    exact t.

   Please look at Coq's documentation before doing these exercises *)

Definition Double_neg : Prop := forall P:Prop, ~~P -> P.

Definition Exm : Prop := forall P : Prop, P \/ ~P.

Definition Classical_impl : Prop := forall P Q:Prop, (P -> Q) -> ~P \/ Q.

Definition Peirce : Prop := forall P Q : Prop, ((P -> Q) -> P) -> P.

Definition Not_forall_not_exists : Prop :=
           forall (A:Type)(P:A->Prop), ~(forall x:A, ~P x) -> ex P.

Lemma  Exm_Double_neg : Exm -> Double_neg.
Proof.
Admitted.


Lemma Double_neg_Exm :  Double_neg -> Exm.
Proof.
 Admitted.

Lemma Peirce_Double_neg : Peirce -> Double_neg.
Proof.
Admitted.

Lemma Exm_Peirce : Exm -> Peirce.
Proof.
Admitted.


Lemma Classical_impl_Exm : Classical_impl -> Exm.
Admitted.


Lemma Exm_Classical_impl : Exm -> Classical_impl.
Proof.
Admitted.
 
 
Lemma Not_forall_not_exists_Double_neg :  Not_forall_not_exists -> Double_neg.
Proof.
Admitted.

Lemma Exm_Not_forall_not_exists: Exm -> Not_forall_not_exists.
Admitted.


(** Consider the following definitions (which could be found in the standard 
   library *)

Section On_functions.
Variables (U V W : Type).

Variable g : V -> W.
Variable f : U -> V.

 Definition injective : Prop := forall x y:U, f x = f y -> x = y.
 Definition surjective : Prop := forall v : V, exists u:U, f u = v.

Lemma injective' : injective -> forall x y:U, x <> y -> f x <> f y.
Proof.
Admitted.

 Definition compose := fun u : U => g (f u).

End On_functions.
Implicit Arguments compose [U V W].
Implicit Arguments injective [U V].
Implicit Arguments surjective [U V].

Lemma injective_comp : forall U V W (f:U->V)(g : V -> W),
                       injective (compose g f) -> injective f.
Proof.
Admitted.


Lemma surjective_comp : forall U V W (f:U->V)(g : V -> W),
                       surjective (compose g f) -> surjective g.
Proof.
Admitted.


Lemma comp_injective : forall U V W (f:U->V)(g : V -> W),
                       injective f -> injective g -> injective (compose g f).
Proof.
Admitted.


Fixpoint iterate (A:Type)(f:A->A)(n:nat) {struct n} : A -> A :=
 match n with 0 => (fun a => a)
            | S p => fun a => f (iterate _ f p a) 
 end.

 Lemma iterate_inj : forall U (f:U->U) , 
                      injective f ->
                      forall n: nat, injective   (iterate _ f n).
Proof.
 induction n;simpl.
Admitted.
 





(** Last serie of exercises : Consider the following definitions
   See "impredicatve definitions" in the book *)

Definition my_False : Prop := forall P:Prop, P.

Definition my_not (P:Prop) := P -> my_False.

Definition my_or (P Q:Prop): Prop := forall R:Prop, 
                                    (P-> R) ->(Q->R) -> R.

Definition my_and (P Q:Prop): Prop := forall R:Prop, 
                                    (P-> Q-> R) -> R.

Definition my_exists (A:Type)(P:A->Prop) : Prop :=
  forall R: Prop, 
    (forall a: A, P a -> R) -> R.

Lemma my_False_ok : False <-> my_False.
Proof.
Admitted.

Lemma my_or_intro_l : forall P Q:Prop, P -> my_or P Q.
Proof.
Admitted.

Lemma my_or_ok : forall P Q:Prop, P \/ Q <-> my_or P Q.
Proof.
Admitted.

Lemma my_and_ok :  forall P Q:Prop, P /\ Q <-> my_and P Q.
Proof.
Admitted.

Lemma my_ex_ok :  forall (A:Type)(P:A->Prop),
                   (exists x, P x) <-> (my_exists A P).
Proof.
Admitted.



 




 

 

                         
  
