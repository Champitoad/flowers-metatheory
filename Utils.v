Require Import ssreflect.
Require Import String.
Require Import stdpp.list stdpp.relations.

(** Names *)

Definition name : Type := string.
Definition string_to_name : string -> name := fun x => x.
Coercion string_to_name : string >-> name.

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

Definition split_at {A} (i : nat) (xs : list A) : option (list A * list A) :=
  let fix aux l i xs :=
    match i, xs with
    | 0, _ => Some (reverse l, xs)
    | S n, a :: xs => aux (a :: l) n xs
    | _, _ => None
    end
  in aux [] i xs.

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

Inductive MyIn {A} : A -> list A -> Prop :=
| MyIn_head : ∀ (x : A) (l : list A), MyIn x (x :: l)
| MyIn_tail : ∀ (x y : A) (l : list A), MyIn x l -> MyIn x (y :: l).

Lemma My_In_is_in (A : Type) (x : A) (l : list A) : MyIn x l <-> In x l.
Proof.
  pose app_nil_r.
  split.
  { intros H. induction H. 
    - simpl. left; reflexivity.
    - simpl. right; assumption. }
  { intros H. induction l. inversion H.
    inversion H. rewrite H0. constructor.
    constructor. apply IHl. apply H0. }

Qed.

Lemma list_sum_zero {l} :
  list_sum l = 0 -> forall x, In x l -> x = 0.
Proof.
  Print In.

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

Lemma equiv_Forall {A} (P Q : A -> Prop) : ∀ (l : list A),
  (∀ x, P x <-> Q x) ->
  Forall P l <-> Forall Q l.
Proof.
  elim => [|x l IH H] //=.
  split; move => Hl; inv Hl; firstorder.
Qed.

#[export] Instance Forall2_Equivalence {A} (e : relation A) {_ : Equivalence e} :
  Equivalence (Forall2 e).
Proof.
  econs; repeat red.
  * elim; intros; auto. econs. apply Equivalence_Reflexive.
  * move => l l'; move: l l'; induction l, l'; move => He; try inv He; auto. econs.
    by apply Equivalence_Symmetric.
  * induction x, y, z; move => H1 H2; try (inv H1; inv H2). econs. 
    by apply (Equivalence_Transitive _ _ _ H5 H4).
Qed.

Lemma Forall_equiv_map {A B} {e : Equiv B} (l : list A) (f g : A -> B) :
  (Forall (fun x => e (f x) (g x)) l) <->
  Forall2 e (f <$> l) (g <$> l).
Proof.
  split.
  * elim: l => [H |a l IHl H]; try done;
    decompose_Forall_hyps; econs.
  * elim: l => [H |a l IHl H]; try done.
    rewrite [f <$> _]fmap_cons [g <$> _]fmap_cons in H.
    inv H. econs.
Qed.

Lemma Forall2_Forall2_Proper {A} {e : Equiv A} :
  ∀ (f : list A -> A) {Hp : Proper (Forall2 e ==> e) f} (l l' : list (list A)),
  Forall2 (Forall2 e) l l' ->
  Forall2 e (f <$> l) (f <$> l').
Proof.
  move => f Hp. induction l, l'; move => H; try inv H; econs.
Qed.

Lemma Forall2_eq_eq {A} : forall (l l' : list A),
  Forall2 eq l l' <-> l = l'.
Proof.
  induction l, l'; split; try done.
  1-3: elim; intros; f_equal; done.
  by elim.
Qed.

Lemma Forall_eq_map {A B} (l : list A) (f g : A -> B) :
  (Forall (fun x => f x = g x) l) <->
  f <$> l = g <$> l.
Proof.
  rewrite -Forall2_eq_eq.
  apply Forall_equiv_map.
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