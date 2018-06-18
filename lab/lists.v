Require Import List.
Import ListNotations.

(** * Preliminaries *)

(** See the definition of lists *)
Print list.

(** The raw constructors and the syntactic sugar *)
Check (cons 1 (cons 2 (cons 3 nil)) = [13;21]).

(** Note that [Check] merely checks the type, not that the thing holds! *)

Check forall A (h:A) (t:list A), h::nil = cons h t.

Section Lists_of_A.
(* We use a section and a [Variable] so that we do not have to worry about [A]
   at each definition / lemma *)
Variable A: Type.

(** ** Definition by pattern matching on lists *)

Definition tail (l : list A) : list A :=
  match l with
  | [] => []   (* functions are total in Coq ! *)
  | h::t => t
  end.

(** Proof by computation *)
Lemma tail_1 : forall a b c, tail [a;b;c] = [b;c].
  intros.
  simpl.
  trivial.
Qed.

(** ** Definition by recursion (and pattern matching) *)

(** The following definition always terminates:
    the recursive call to length is allowed for subterms of [l] only (extracted by [match]) ! *)

Fixpoint length (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

(** Proof by case analysis *)
Lemma len_tail : forall l, l = [] \/ 1 + length (tail l) = length l.
Proof.
  (* for inductively defined objects,
     we get a case for each constructor *)
  destruct l.
  + left.
    trivial.
  + right.
    simpl tail.
    simpl length.
    (* or equivalently: simpl. *)
    trivial.
Qed.

(** Another definition, by induction on the first argument *)
Fixpoint app (l m : list A): list A :=
  match l with
  | [] => m
  | a :: l1 => a :: app l1 m
  end.

(** Proof by induction on lists *)
Lemma app_length : forall l1 l2 : list A, 
  length l1 + length l2 = length (app l1 l2).
Proof.
  (* similar to (destruct l1),
     but you additionally get an induction hypothesis *)
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    intro.
    rewrite -> IHl1.  (* [->] can be skipped; try also rewrite <- *)
    reflexivity. (* trivial is also good enough *)
Qed.

(** This lemma is very easy *)
Lemma app_nil_l : forall l, app nil l = l.
Proof.
  simpl.
  trivial.
Qed.

(** What about this one? :) *)
Lemma app_nil_r : forall l, app l nil = l.
Proof.
  simpl. (* no effect :) *)
  (* exercise *)
Admitted.

(** another proof by induction *)
Lemma app_assoc : forall l1 l2 l3 : list A,
  app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  (* exercise *)
Admitted.

(** recursive predicate on lists *)
Fixpoint In (a:A) (l:list A) : Prop :=
  match l with 
  | [] => False
  | h::t => a = h \/ In a t
  end.
(* Note that we have defined a predicate [In : A -> list A -> Prop] by recursion on lists *)

(* simple proof *)
Lemma In_sing : forall a:A, In a [a].
Proof.
  intros.
  simpl.
  left.
  trivial.
Qed.

(** use the predicate by computing it *)
Lemma In_not_empty : forall (a:A) l, In a l -> l <> [].
Proof.
  intros.
  destruct l.
  + simpl in H.
    tauto.
  + congruence. (* handle simple equality or disequality *)
Qed.

Lemma not_In_empty : forall a:A, ~ In a [].
Proof.
  intros.
  intro H.
  simpl in H.
  tauto.
Restart. (* another possible proof *)
  intros.
  intro H.
  apply In_not_empty in H as H2.  (* use a lemma for forward reasonning *)
  apply In_not_empty in H. (* or simply if we don't care for the current state of H *)
  congruence.  (* handle clearly wrong disequality in hypotheses *) 
Qed.

Lemma in_app_or : forall a l1 l2, In a (app l1 l2) -> In a l1 \/ In a l2.
Proof.
  (* exercise *)
  intros a l1 l2.
  induction l1; intros; simpl.
  + right.
    simpl in H.
    assumption.
  + simpl in H.
    destruct H as [B | C].
    - intuition.
    - apply IHl1 in C.
      intuition.
Admitted.

(** ** Inductive predicate *)
Inductive contains (a:A) : list A -> Prop :=
| C_here : forall l, contains a (a::l)
| C_there : forall l b, contains a l -> contains a (b::l).

(* Corresponds to definitions by rules with \u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013

rule (C_here) \u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013
               contains a (a::l)


                   contains a l
rule (C_there) \u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013\u2013
                 contains a (b::l)


or to a Prolog definition:

contains(A, [[A|L]]).
contains(A, [[B|L]]] :- contains(A,L).

*)


(** proving an inductive predicate *)
Lemma cont_abc : forall a b c, contains b [a;b;c].
Proof.
  intros.
  apply C_there.
  apply C_here.
Restart. (* or simpler *)
  intros.
  constructor 2.
  constructor 1.
Restart. (* even simpler *)
  intros.
  constructor. (* any constructor that can be used *)
  constructor.
Restart. (* simplest *)
  repeat constructor.
Qed.

(** using an inductive predicate *)
Lemma cont_nempty : forall a l, contains a l -> l <> [].
Proof.
  intros.
  destruct H.  (* basic tactic - works well if [contains] is applied to variables *)
  + congruence.
  + congruence.
Qed.

Lemma not_cont_empty : forall a, ~ contains a [].
Proof.
  intros.
  intro H.
  destruct H.  (* if [contains] is applied to terms other than variables,
                  we can lose information *)
  (* we are stuck *)
  Undo.
  inversion H. (* this works - [contains a []] is impossible
                  and it is automatically discarded;
                  both [C_here] and [C_there] need a non-empty list *)
  (* do [Show Proof.] to see that some case analysis is really going on underneath *)
Qed.

(** [inversion H] - for a hypothesis [H : C t1 t2] :
   how could it happen that [C t1 t2] holds
*)

(* you may also try [inversion_clear] *)
Lemma cont_double : forall a b c, contains a [b;c] -> a=b \/ a=c.
Proof.
  (* exercise *)
Admitted.

(** three lemmas establishing the correspondence between contains and In *)
Lemma cont_In : forall a l, contains a l -> In a l.
Proof.
  (* exercise *)
Admitted.

Lemma In_cont : forall a l, In a l -> contains a l.
Proof.
  (* exercise *)
Admitted.

(* given the previous two lemmas, this one requires no more than three tactics *)
Lemma In_iff_cont : forall a l, In a l <-> contains a l.
Proof.
  (* exercise *)
Admitted.


(** ** Another inductive predicate *)

Inductive prefix : list A -> list A -> Prop :=
| P_nil : forall l2, prefix [] l2
| P_cons : forall a l1 l2, prefix l1 l2 -> prefix (a::l1) (a::l2).

Lemma pref_contains: forall a l, prefix [a] l -> contains a l.
Proof.
  intros.
  inversion H.
  apply C_here.
Qed.

(** a couple of simple lemmas *)
Lemma pref_reflexive: forall l, prefix l l.
Proof.
 (* exercise *)
Admitted.

(* Hint: there are two lists to do induction on,
   but only one will work. *)
Lemma pref_app : forall l1 l2, prefix l1 (l1++l2).
Proof.
  (* exercise *)
Admitted.

Lemma pref_app2 : forall l1 l2 l3,
  prefix l2 l3 -> prefix (l1++l2) (l1++l3).
Proof.
  (* exercise *)
Admitted.

(* Hint: this one needs induction + inversion *)
Lemma pref_short : forall l1 l2 l3, prefix (l1++l2) (l1++l3) -> prefix l2 l3.
Proof.
  (* exercise *)
Admitted.

(** example of proof by induction on the evidence for predicate "prefix" *)
Lemma pref_app3 : forall l1 l2 l3, prefix l1 l2 -> prefix l1 (l2++l3).
Proof.
  intros.
  induction H.
  + constructor.
  + simpl.
    constructor.
    trivial.
Qed.

(** Hint: induction on the evidence for the first occurrence of "prefix" *)
Lemma pref_antisymm: forall l1 l2,
  prefix l1 l2 -> prefix l2 l1 -> l1 = l2.
Proof.
  (* exercise *)
Admitted.

(** transitivity of prefix *)
Lemma pref_trans : forall l1 l2 l3, prefix l1 l2 -> prefix l2 l3 -> prefix l1 l3.
Proof.
  intros.
  induction H.
  + constructor.
  + (* IHprefix is useless! There are two reasons:
      1) If prefix (a::l2) l3 than it is impossible that prefix l2 l3
      2) we need to prove prefix (a :: l1) l3,
         but the conclusion of the inductive assumption only says prefix l1 l3 *)
Restart.  (* We need to strengthen our induction hypothesis
             to the more general form forall l3... *)
  intros l1 l2 l3 H.
  revert l3.  (* now our goal is forall l3... ! *)
  (* exercise *)
Admitted.

(** ** Reversing lists for the bored ones only !!! *)

(* this is the definition from the library, with quadratic time complexity *)
Fixpoint rev_slow (l: list A) :=
  match l with
  | [] => []
  | h::t => rev_slow t ++ [h]
  end.

(* reversing in linear time using an accumulator *) 
Fixpoint reva (lr l : list A) := match l with
  | [] => lr
  | h::t => reva (h::lr) t
end.

Definition rev l := reva [] l.

Lemma rev_equiv: forall l: list A, rev l = rev_slow l.
Proof.
  induction l.
  + unfold rev. simpl. trivial.
  + unfold rev in *.
    simpl.
    rewrite <- IHl.
    simpl.
    (* The inducton hypothesis is not strong enough *)
Abort.

(* This is a more general fact about the accumulator *)
(* Hint: do induction on l3,
   but make sure that the hypothesis is as general as possible! *)
Lemma reva_app: forall l1 l2 l3: list A,
  reva (l1 ++ l2) l3 = reva l1 l3 ++ l2.
Proof.
  (*Exercise*)
Admitted.

(* Hint: specialise the previous lemma *)
Lemma reva_singl: forall a l,
  reva [a] l = reva [] l ++ [a].
Proof.
  (* Exercise *)
Admitted.

Lemma rev_equiv: forall l: list A, rev l = rev_slow l.
Proof.
  induction l.
  + unfold rev. simpl. trivial.
  + unfold rev in *.
    simpl.
    rewrite <- IHl.
    simpl. apply reva_singl.
Qed.

(* another property we might want to prove is that reverse is an involution *)
Lemma rev_rev : forall l : list A, rev (rev l) = l.
Proof.
  unfold rev.
  induction l.
  + simpl.
    trivial.
  + simpl.
    (* No way! Induction hypothesis is no good. We need stronger assumptions... *)
Abort.

(* auxilary lemma 1 *)
Lemma reva_reva : forall l1 lr : list A, reva lr l1 = app (reva [] l1) lr.
Proof.
  (* exercise *)
Admitted.

(* auxilary lemma 2 *)
Lemma reva_app : forall l1 l2 lr, reva lr (app l1 l2) = app (reva [] l2) (reva lr l1).
Proof.
  (* exercise *)
Admitted.

(* Now, we can do the proof! *)
Lemma rev_rev : forall l : list A, rev (rev l) = l.
Proof.
  (* exercise *)
Admitted.



(* Hooray! *)


(** ** Final notes *)


(** NB: The official [rev] is quadratic (no problem unless you do some
   serious computations within Coq) and friendlier with proofs *)
Print List.rev.
(** NB2. [++] is [app] *)
Eval simpl in ([1;2;3] ++ [4;5;6]).

(* see below *)
Check prefix.
Check app.
Check pref_trans.

End Lists_of_A.

(** NB3. Note that after closing the section, our definitions (and also lemmas)
    get abstracted over variables from the section *)
Check prefix.
Check app.
Check pref_trans.

(** This is the end... *)