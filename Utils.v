Require Import ssreflect.
Require Import String.
Require Import stdpp.list stdpp.relations.

(** Names *)

Definition name : Type := string.
Definition string_to_name : string -> name := fun x => x.
Coercion string_to_name : string >-> name.

(** * Tactics *)

Ltac done := try ssreflect.done; solve [auto].

Ltac inv H := inversion H; subst; clear H; try congruence.
Ltac inve H := inversion H; subst; try congruence.
Ltac econs := econstructor; eauto; try congruence.

Ltac solve_decide := try ((left + right); congruence).
Ltac eq_decide x y :=
  destruct (decide (x = y)).

(** * Logic *)

Lemma contrapose {A B : Prop} :
  (A -> B) -> (~ B -> ~ A).
Proof.
  intuition.
Qed.

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

Definition forallb (l : list bool) :=
  foldr andb true l.

Ltac solve_elem_of_list :=
  match goal with
  | |- ?x ∈ ?l ++ ?l' => apply elem_of_app; (left + right); solve_elem_of_list
  | |- ?x ∈ ?x :: ?l => apply elem_of_list_here
  | H : ?x = ?y |- ?x ∈ ?y :: ?l => rewrite H; apply elem_of_list_here
  | |- ?x ∈ ?y :: ?l => apply elem_of_list_further; solve_elem_of_list
  | |- ?x ∈ ?l => by auto
  end.

Lemma elem_of_map {A B : Type} (f : A -> B) (l : list A) (y : B) :
  y ∈ f <$> l <->
  exists x, x ∈ l /\ y = f x.
Proof.
  elim: l => [|a l IHl]; split; move => H.
  * inv H.
  * case: H => [? [H _]]. inv H.
  * inv H. exists a. split; econs.
    apply IHl in H2. case: H2 => [x [H1 H2]].
    exists x. split; auto. econs.
  * case: H => [x [H1 H2]]. subst.
    inve H1; rewrite fmap_cons.
    econs. econs. apply IHl.
    exists x. split; auto.
Qed.

Lemma subseteq_cons_nil {A} (x : A) (l : list A) :
  ~ (x :: l) ⊆ [].
Proof.
  red. move => H. red in H. red in H.
  specialize (H x (elem_of_list_here x l)).
  inv H.
Qed.

Lemma subseteq_nil {A} (l : list A) :
  l ⊆ [] -> l = [].
Proof.
  case: l => [|x l] H; auto.
  destruct (subseteq_cons_nil x l H).
Qed.

Lemma proper_app_subseteq {A} : forall (l1' l1 l2 l2' : list A),
  l1 ⊆ l1' -> l2 ⊆ l2' ->
  l1 ++ l2 ⊆ l1' ++ l2'.
Proof.
  rewrite /subseteq /list_subseteq.
  intros.
  decompose_elem_of_list;
  solve_elem_of_list.
Qed.

Lemma In_Forall {A} (P : A -> Prop) : ∀ (l : list A),
  (∀ x, In x l -> P x) <-> Forall P l.
Proof.
  elim.
  * split; move => H; easy.
  * move => a l IH. split; move => H.
    - econs.
      + apply H. econs.
      + apply IH. move => y Hy.
        apply H. simpl. by right.
    - move => x HIn. inv HIn; inv H.
      apply IH; auto.
Qed.

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

Lemma eq_map {A B} (f g : A -> B) : ∀ (l : list A),
  (∀ x, f x = g x) ->
  f <$> l = g <$> l.
Proof.
  elim => [|x l IH H] //=. rewrite H. f_equal. by apply IH.
Qed.

Lemma impl_Forall {A} (P Q : A -> Prop) : ∀ (l : list A),
  (∀ x, P x -> Q x) ->
  Forall P l -> Forall Q l.
Proof.
  elim => [|x l IH H] //=.
  move => Hl; inv Hl; firstorder.
Qed.

Lemma equiv_Forall {A B} {e : Equiv B} (f g : A -> B) : ∀ (l : list A),
  (∀ x, e (f x) (g x)) ->
  Forall (λ x, e (f x) (g x)) l.
Proof.
  elim => [|x l IH H] //=.
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

Lemma Forall2_equiv_map_bind {A B} {e : Equiv (list B)} :
  ∀ (l : list A) (f g : A -> list B),
  Forall2 e (f <$> l) (g <$> l) ->
  e (l ≫= f) (l ≫= g).
Proof.
Admitted.

Lemma list_bind_singl {A} (l : list A) :
  l ≫= (λ x, [x]) = l.
Admitted.

Lemma Forall_eq_map {A B} (l : list A) (f g : A -> B) :
  (Forall (fun x => f x = g x) l) <->
  f <$> l = g <$> l.
Proof.
  rewrite -Forall2_eq_eq.
  apply Forall_equiv_map.
Qed.

Lemma Forall_forall {A B} (l : list A) (P : A -> B -> Prop) :
  Forall (λ x, ∀ y, P x y) l <->
  ∀ y, Forall (λ x, P x y) l.
Proof.
  elim: l => [|a l IHl] //=.
  split; intro H.
  * intro y. inv H. econs; auto. by apply IHl.
  * econs.
    - intro y. specialize (H y). inv H.
    - apply IHl. intro y. specialize (H y). inv H.
Qed.

Lemma eq_fmap {A B} (f g : A -> B) : ∀ (l : list A),
  (∀ x, f x = g x) ->
  f <$> l = g <$> l.
Proof.
  elim => [|a l IHl] H //=. rewrite H.
  specialize (IHl H). rewrite /fmap in IHl. by rewrite IHl.
Qed.

Lemma map_id_ext {A} (l : list A) :
  id <$> l = l.
Proof.
  elim: l => [|a l IHl] //=.
  by f_equal.
Qed.

Lemma fmap_singl {A B} (x : A) (f : A -> B) :
  f <$> [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma map_singl {A B} (x : A) (f : A -> B) :
  map f [x] = [f x].
Proof.
  reflexivity.
Qed.

Lemma bind_app {A B} (f : A -> list B) : forall (l l' : list A),
  (l ++ l') ≫= f = (l ≫= f) ++ (l' ≫= f).
Proof.
  elim => [|x l IHl]; list_simplifier; try done.
  move => l'; rewrite IHl.
  elim: l' => [|x' l' IHl']; list_simplifier; try done.
Qed.