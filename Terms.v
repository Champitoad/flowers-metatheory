Require Import stdpp.list stdpp.list_numbers.
Require Import ssreflect.

Require Import Flowers.Utils.

(** ** Terms *)

Inductive term :=
| TVar (n : nat)
| TFun (f : name) (args : list term).

Lemma term_induction_full :
  ∀ (P : term -> Prop) (Pn : nat -> Prop)
  (IHn : ∀ n, Pn n)
  (IHvar : ∀ n, Pn n -> P (TVar n))
  (IHfun : ∀ f args, Forall P args -> P (TFun f args)),
  ∀ t, P t.
Proof.
  intros; move: t; fix IH 1; induction t.
  * apply IHvar. apply IHn.
  * apply IHfun. elim args; auto.
Qed.

Lemma term_induction :
  ∀ (P : term -> Prop)
  (IHvar : ∀ n, P (TVar n))
  (IHfun : ∀ f args, Forall P args -> P (TFun f args)),
  ∀ t, P t.
Proof.
  intros. eapply term_induction_full; eauto.
  exact (fun _ => I).
Qed.

Inductive cst : term -> Prop :=
| cst_fun f args : Forall cst args -> cst (TFun f args).

Fixpoint tclosed (c : nat) (t : term) : bool :=
  match t with
  | TVar n => n <? c
  | TFun f args => forallb (tclosed c <$> args)
  end.

Fixpoint tsubst (n : nat) (u : term) (t : term) : term :=
  match t with
  | TVar m => if n =? m then u else t
  | TFun f args => TFun f (tsubst n u <$> args)
  end.

Fixpoint tshift (n : nat) (c : nat) (t : term) : term :=
  match t with
  | TVar m => TVar (if m <? c then m else m + n)
  | TFun f args => TFun f (tshift n c <$> args)
  end.

Fixpoint tunshift (n : nat) (c : nat) (t : term) : term :=
  match t with
  | TVar m => TVar (if m <? c then m else m - n)
  | TFun f args => TFun f (tunshift n c <$> args)
  end.

Lemma tshift_zero c : ∀ t,
  tshift 0 c t = t.
Proof.
  induction t as [|?? IH] using term_induction; simpl.
  * destruct (n <? c); auto.
  * f_equal. rewrite Forall_eq_map in IH.
    by rewrite list_fmap_id in IH.
Qed.

Lemma tshift_add c n m : ∀ t,
  tshift (n + m) c t = tshift n c (tshift m c t).
Proof.
  induction t as [|?? IH] using term_induction; simpl.
  * destruct (n0 <? c) eqn:Heqb.
    by rewrite Heqb.
    assert (Hm : n0 + m <? c = false).
    { rewrite Nat.ltb_nlt in Heqb.
      apply Nat.ltb_nlt. lia. }
    rewrite Hm.
    by rewrite -Nat.add_assoc [m + n]Nat.add_comm Nat.add_assoc.
  * f_equal. rewrite Forall_eq_map in IH.
    by repeat rewrite (list_fmap_compose (tshift _ c)) in IH.
Qed.

Lemma tshift_comm c n m t :
  tshift n c (tshift m c t) = tshift m c (tshift n c t).
Proof.
  by rewrite -tshift_add Nat.add_comm tshift_add.
Qed.

Lemma tunshift_zero c : ∀ t,
  tunshift 0 c t = t.
Proof.
  induction t as [|?? IH] using term_induction; simpl.
  * destruct (n <? c); auto. by rewrite Nat.sub_0_r.
  * f_equal. rewrite Forall_eq_map in IH.
    by rewrite list_fmap_id in IH.
Qed.

Lemma tsubst_tshift c m t :
  tsubst c (TVar (c + m)) (tshift m (S c) t) = tshift m c t.
Proof.
  induction t using term_induction; simpl.
  * case n, c eqn:?; simpl; auto.
    case (S n <? S (S n0)) eqn:?.
    case (n <? n0) eqn:?; simpl.
    assert (S n <? S n0 = true).
    { Search (_ <? _ = true).
      rewrite Nat.ltb_lt in Heqb0.
      apply lt_n_S in Heqb0.
      rewrite -Nat.ltb_lt in Heqb0.
      auto. }
    rewrite H.
    assert (n0 =? n = false).
    { Search "ltb_lt".
      apply Nat.ltb_lt in Heqb0.
      apply Nat.lt_neq in Heqb0.
      apply Nat.neq_sym in Heqb0.
      by apply Nat.eqb_neq in Heqb0. }
    by rewrite H0.
    case (n0 =? n) eqn:?.
    apply Nat.eqb_eq in Heqb1.
    rewrite Heqb1.
    assert (S n <? S n = false).
    { by apply Nat.ltb_irrefl. }
    by rewrite H.
    assert (S n <? S n0 = false).
    { apply Nat.ltb_nlt.
      apply Nat.ltb_nlt in Heqb0.
      intro; destruct Heqb0.
      Search (S _ < S _ -> _ < _).
      by apply lt_S_n. }
    rewrite H.
    apply Nat.ltb_nlt in Heqb0.
    apply Nat.eqb_neq in Heqb1.
    assert (n <= n0).
    { apply Nat.ltb_lt in Heqb. lia. }
    Search (_ <= _ -> _ \/ _).
    apply le_lt_or_eq in H0.
    intuition. by symmetry in H1.
    assert (S n <? S n0 = false).
    { apply Nat.ltb_nlt in Heqb.
      pose proof (Nat.lt_lt_succ_r (S n) (S n0)).
      pose proof (contrapose H).
      apply Nat.ltb_nlt. by apply H0. }
    rewrite H.
    destruct m eqn:?; simpl.
    repeat rewrite Nat.add_0_r.
    destruct (n0 =? n) eqn:?; auto.
    apply Nat.eqb_eq in Heqb0.
    by rewrite Heqb0.
    assert (n0 =? n + (S n1) = false).
    { apply Nat.eqb_neq. intro.
      rewrite H0 in H.
      apply Nat.ltb_nlt in H.
      lia. }
    by rewrite H0.
  * apply Forall_eq_map in H. rewrite -list_fmap_compose.
    by rewrite H.
Qed.

Lemma tsubst_tshift_vacuous n u m c t :
  n < m ->
  tsubst (n + c) u (tshift m c t) = tshift m c t.
Proof.
  intros H.
  induction t as [|?? IH] using term_induction; simpl.
  * destruct (n0 <? c) eqn:Heqb.
    - assert (Hnc : n + c =? n0 = false).
      { apply Nat.eqb_neq. apply Nat.ltb_lt in Heqb. lia. }
      by rewrite Hnc.
    - assert (Hnc : n + c =? n0 + m = false).
      { apply Nat.eqb_neq. apply Nat.ltb_nlt in Heqb. lia. }
      by rewrite Hnc.
  * apply Forall_eq_map in IH. rewrite -list_fmap_compose.
    by rewrite IH.
Qed.

Lemma tsubst_tshift_vacuous2 : ∀ t m c,
  tsubst c (TVar (c + m)) (tshift m (S c) t) = tshift m c t.
Proof.
  elim/term_induction => [n |f args IH] m c /=.
  * destruct (n <? S c) eqn:Hltb.
    - destruct (c =? n) eqn:Heqb.
      + apply Nat.eqb_eq in Heqb.
        assert (H : n <? c = false).
        { apply Nat.ltb_nlt. lia. }
        by rewrite H Heqb.
      + assert (H : n <? c = true).
        { apply Nat.ltb_lt in Hltb.
          apply Nat.ltb_lt.
          apply Nat.eqb_neq in Heqb.
          lia. }
        by rewrite H.
    - destruct (c =? n + m) eqn:Heqb.
      + apply Nat.eqb_eq in Heqb.
        rewrite Heqb in Hltb.
        apply Nat.ltb_nlt in Hltb.
        lia.
      + assert (H : n <? c = false).
        { apply Nat.ltb_nlt in Hltb.
          apply Nat.ltb_nlt.
          lia. }
        by rewrite H.
  * rewrite Forall_forall in IH; specialize (IH m).
    rewrite Forall_forall in IH; specialize (IH c).
    rewrite Forall_eq_map in IH. rewrite -IH.
    by rewrite -list_fmap_compose.
Qed.

Lemma tunshift_tshift m n c t :
  tunshift (m + n) c (tshift n c t) = tunshift m c t.
Proof.
  induction t using term_induction; simpl.
  * f_equal.
    destruct (n0 <? c) eqn:?. by rewrite Heqb.
    assert (n0 + n <? c = false).
    { apply Nat.ltb_nlt.
      apply Nat.ltb_nlt in Heqb. lia. }
    rewrite H. lia.
  * apply Forall_eq_map in H. rewrite -list_fmap_compose.
    by rewrite H.
Qed.
