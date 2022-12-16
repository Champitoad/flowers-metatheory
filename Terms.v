Require Import ssreflect.
Require Import stdpp.list stdpp.list_numbers.
Require Import FunctionalExtensionality.
Require Import ZifyBool.

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

(* Fixpoint tclosed (c : nat) (t : term) : bool :=
  match t with
  | TVar n => n <? c
  | TFun f args => forallb (tclosed c <$> args)
  end. *)

Definition sbt := nat -> term.

Fixpoint tsubst (σ : sbt) (t : term) : term :=
  match t with
  | TVar m => σ m
  | TFun f args => TFun f (tsubst σ <$> args)
  end.

Definition idsubst : sbt :=
  λ n, TVar n.

Lemma tsubst_id : ∀ t,
  tsubst idsubst t = t.
Proof.
  elim/term_induction => [n |f args IH] //=.
  do 2 f_equal. apply Forall_eq_map in IH.
  by rewrite map_id_ext in IH.
Qed.

Definition has_range (n : nat) (σ : sbt) :=
  ∀ m, m >= n -> σ m = TVar m.

Lemma has_range_id : ∀ n,
  has_range n idsubst.
Proof.
  done.
Qed.

Definition mksubst (n : nat) (t : term) : sbt :=
  λ m, if n =? m then t else TVar m.

Notation "n ↦ u" := (mksubst n u) (at level 20).

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
    assert (Hm : n0 + m <? c = false) by lia.
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
  tsubst (c ↦ TVar (c + m)) (tshift m (S c) t) = tshift m c t.
Proof.
  induction t using term_induction; simpl.
  * case n, c eqn:?; simpl; auto.
    case (S n <? S (S n0)) eqn:?.
    case (n <? n0) eqn:?; simpl.
    assert (S n <? S n0 = true) by lia.
    rewrite H.
    assert (S n0 =? S n = false) by lia.
    by rewrite /mksubst H0.
    case (n0 =? n) eqn:?.
    apply Nat.eqb_eq in Heqb1.
    rewrite Heqb1.
    assert (S n <? S n = false) by lia.
    by rewrite /mksubst H Nat.eqb_refl.
    assert (S n <? S n0 = false) by lia.
    assert (S n0 =? S n = false) by lia.
    rewrite /mksubst H H0.
    apply Nat.ltb_nlt in Heqb0.
    apply Nat.eqb_neq in Heqb1.
    assert (n <= n0) by lia.
    apply le_lt_or_eq in H1.
    intuition. by symmetry in H2.
    assert (S n <? S n0 = false) by lia.
    rewrite H.
    destruct m eqn:?; simpl.
    repeat rewrite Nat.add_0_r.
    destruct (n0 =? n) eqn:?; auto.
    apply Nat.eqb_eq in Heqb0.
    by rewrite /mksubst Heqb0 Nat.eqb_refl.
    assert (S n0 =? S n = false) by lia.
    by rewrite /mksubst H0.
    assert (S n0 =? S (n + (S n1)) = false) by lia.
    by rewrite /mksubst H0.
  * apply Forall_eq_map in H. rewrite -list_fmap_compose.
    by rewrite H.
Qed.

Lemma tsubst_tshift_vacuous n u m c t :
  n < m ->
  tsubst ((n + c) ↦ u) (tshift m c t) = tshift m c t.
Proof.
  intros H.
  induction t as [|?? IH] using term_induction; simpl.
  * destruct (n0 <? c) eqn:Heqb.
    - assert (Hnc : n + c =? n0 = false) by lia.
      by rewrite /mksubst Hnc.
    - assert (Hnc : n + c =? n0 + m = false) by lia.
      by rewrite /mksubst Hnc.
  * apply Forall_eq_map in IH. rewrite -list_fmap_compose.
    by rewrite IH.
Qed.

Lemma tsubst_tshift_vacuous2 : ∀ t m c,
  tsubst (c ↦ TVar (c + m)) (tshift m (S c) t) = tshift m c t.
Proof.
  elim/term_induction => [n |f args IH] m c /=.
  * destruct (n <? S c) eqn:Hltb.
    - destruct (c =? n) eqn:Heqb.
      + apply Nat.eqb_eq in Heqb.
        assert (H : n <? c = false) by lia.
        by rewrite /mksubst H Heqb Nat.eqb_refl.
      + assert (H : n <? c = true) by lia.
        by rewrite /mksubst H Heqb.
    - destruct (c =? n + m) eqn:Heqb.
      + lia.
      + assert (H : n <? c = false) by lia.
        by rewrite /mksubst H Heqb.
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
    assert (n0 + n <? c = false) by lia.
    rewrite H. lia.
  * apply Forall_eq_map in H. rewrite -list_fmap_compose.
    by rewrite H.
Qed.

Definition sshift (n : nat) (σ : sbt) : sbt :=
  λ m, if m <? n then TVar m else tshift n 0 (σ (m - n)). 

Lemma sshift_zero σ :
  sshift 0 σ = σ.
Proof.
  apply functional_extensionality.
  intros. by rewrite /sshift nltb_zero tshift_zero Nat.sub_0_r.
Qed.

Lemma sshift_add n m σ :
  sshift (n + m) σ = sshift n (sshift m σ).
Proof.
  apply functional_extensionality.
  intros p. rewrite /sshift.
  destruct (p <? n) eqn:Hpn.
  * assert (H : p <? n + m = true) by lia.
    by rewrite H.
  * destruct (p <? m) eqn:Hpm.
    - assert (H : p <? n + m = true) by lia.
      assert (H' : p - n <? m = true) by lia.
      rewrite H H'. simpl. f_equal. lia.
    - destruct (p <? n + m) eqn:Hpnm.
      + assert (H' : p - n <? m = true) by lia.
        rewrite H'. simpl. f_equal. lia.
      + assert (H' : p - n <? m = false) by lia.
        rewrite H'. rewrite tshift_add.
        do 3 f_equal. lia.
Qed.

Lemma sshift_mksubst n m t :
  sshift n (m ↦ t) = (m + n) ↦ tshift n 0 t.
Proof.
  apply functional_extensionality. intros k.
  rewrite /sshift/mksubst. destruct (k <? n) eqn:Hkn.
  * assert (H : m + n =? k = false) by lia. by rewrite H.
  * destruct (m =? k - n) eqn:Hmkn.
    - assert (H : m + n =? k = true) by lia. by rewrite H.
    - assert (H : m + n =? k = false) by lia. rewrite H /=.
      f_equal. lia.
Qed.