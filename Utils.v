Require Import ssreflect.
Require Import stdpp.list stdpp.relations.

(** * Tactics *)

Ltac inv H := inversion H; subst; clear H; try congruence.
Ltac econs := econstructor; eauto; try congruence.

Ltac solve_decide := try ((left + right); congruence).
Ltac eq_decide x y :=
  destruct (decide (x = y)).

(** * Logic *)

Lemma neg_exists {A} {P : A -> Prop} :
  (~ exists x, P x) -> forall x, ~ P x.
Proof.
  firstorder.
Qed.

Lemma f_unequal {A B} (f : A -> B) (x y : A) :
  f x ≠ f y -> x ≠ y.
Proof.
  intros H ?. apply H. by f_equal.
Qed.

Lemma nat_strong_lemma :
  forall (P : nat -> Prop),
  P 0 -> 
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n m, m <= n -> P m.
Proof.
  intros P H0 Hrec n. induction n; intros m Hm.
  * inversion Hm. exact H0.
  * apply le_lt_or_eq in Hm. unfold lt in Hm. destruct Hm.
    + apply IHn. apply le_S_n. assumption.
    + rewrite H. apply Hrec. exact IHn.
Qed.  

Definition nat_srec :
  forall (P : nat -> Prop),
  P 0 -> 
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n.
Proof.
  intros P H0 IH n.
  apply (nat_strong_lemma P H0 IH n n). constructor.
Qed.

(** * Lists *)

Fixpoint list_remove_none {A} (l : list (option A)) : list A :=
  match l with
  | nil => nil
  | None :: l => list_remove_none l
  | Some x :: l => x :: list_remove_none l
  end.

Fixpoint list_map_opt {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l =>
      match f x with
      | None => list_map_opt f l
      | Some v => v :: list_map_opt f l
      end
  end.

Lemma list_sum_zero {l} :
  list_sum l = 0 -> forall x, In x l -> x = 0.
Proof.
  induction l; simpl; auto.
  * done.
  * intros. destruct H0.
    - lia.
    - apply IHl; auto. lia.
Qed.

Lemma not_eq_cons {A} (l : list A) :
  (~ exists x l', l = x :: l') -> l = nil.
Proof.
  intro. assert (forall x l', l ≠ x :: l') as H0.
  { pose proof (neg_exists H) as H0. simpl in H0. intros x. specialize (H0 x).
    pose proof (neg_exists H0) as H1. simpl in H1. intros l'. apply H1. }
  case l eqn:?; auto. specialize (H0 a l0). done.
Qed.

Lemma eq_nil_dec {A} (l : list A) :
  {l = nil} + {l ≠ nil}.
Proof.
  case l; auto.
Qed.

Lemma neq_cons_itself {A} (a : A) (l : list A) :
  a :: l ≠ l.
Proof.
  induction l; congruence.
Qed.

Lemma cons_app {A} (a : A) (l : list A) :
  a :: l = [a] ++ l.
Proof.
  reflexivity.
Qed.

Definition lincl {A} (R : relation A) : relation (list A) :=
  fun l l' => Forall (fun x => exists x', In x' l' ∧ R x x') l.

Definition lequiv {A} (R : relation A) : relation (list A) :=
  fun l l' => lincl R l l' ∧ lincl R l' l.

Infix "≡ₗ@{ R }" :=
  (lequiv R) (at level 70, no associativity, only parsing).

Lemma Forall_eq_map {A B} (l : list A) (f g : A -> B) :
  (Forall (fun x => f x = g x) l) <->
  f <$> l = g <$> l.
Proof.
  split.
  * elim: l => [H |a l IHl H]; try done.
    decompose_Forall_hyps. rewrite H IHl //.
  * elim: l => [H |a l IHl H]; try done.
    rewrite [f <$> _]fmap_cons [g <$> _]fmap_cons in H.
    inv H. econs.
Qed.

Lemma map_id_ext {A} (l : list A) :
  id <$> l = l.
Proof.
  elim: l => [|a l IHl] //=.
  by f_equal.
Qed.

Lemma bind_app {A B} (f : A -> list B) : forall (l l' : list A),
  (l ++ l') ≫= f = (l ≫= f) ++ (l' ≫= f).
Proof.
  elim => [|x l IHl]; list_simplifier; try done.
  move => l'; rewrite IHl.
  elim: l' => [|x' l' IHl']; list_simplifier; try done.
Qed.