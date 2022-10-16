Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Terms Flowers.Utils.

(** * Flowers *)

Inductive flower :=
| Atom (p : name) (args : list term)
| Flower (γ : nat * list flower) (Δ : list (nat * list flower)).

Definition garden : Type := nat * list flower.
Definition bouquet := list flower.

Definition ftog : flower -> garden := λ ϕ, (0, [ϕ]).
Coercion ftog : flower >-> garden.

Definition ftob : flower -> bouquet := λ ϕ, [ϕ].
Coercion ftob : flower >-> bouquet.

Definition btog : bouquet -> garden := λ Φ, (0, Φ).
Coercion btog : bouquet >-> garden.

Notation "∅" := (0, nil).
Notation "n ⋅ Φ" := (n, Φ) (format "n  ⋅  Φ", at level 63).

Notation "γ ⊢ Δ" := (Flower γ Δ) (at level 65).
Notation "γ ⊢" := (Flower γ nil) (at level 65).
Notation "⊢ Δ" := (Flower ∅ Δ) (at level 65).

(** ** Induction principles *)

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pt : term -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHt : ∀ (t : term), Pt t)
    (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⊢ Δ))
    (IHgarden : ∀ (n : nat) (Φ : bouquet),
      Forall P Φ -> Pγ (n ⋅ Φ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. move: ϕ. fix IH 1. induction ϕ.
  * apply IHatom. apply In_Forall. intros. by apply IHt.
  * apply IHflower.
    - case: γ => n Φ.
      apply IHgarden.
      elim: Φ => [|ϕ Φ IHΦ] //.
    - elim: Δ => [|δ Δ IHΔ] //.
      decompose_Forall; auto.
      case δ => n Φ. apply IHgarden; auto.
      decompose_Forall; auto.
Qed.

Definition flower_induction	:
  ∀ (P : flower -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHatom : ∀ p args, P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⊢ Δ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. eapply flower_induction_full; eauto.
  exact (λ _, I).
Qed.

(** ** Operations on De Bruijn indices *)

Fixpoint shift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tshift n c <$> args)
  | m ⋅ Φ ⊢ Δ =>
      m ⋅ shift n (c + m) <$> Φ ⊢
        ((λ '(k ⋅ Ψ), k ⋅ shift n (c + m + k) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gshift n c '(m ⋅ Φ) : garden :=
  m ⋅ shift n (c + m) <$> Φ.

Fixpoint unshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tunshift n c <$> args)
  | m ⋅ Φ ⊢ Δ =>
      m ⋅ unshift n (c + m) <$> Φ ⊢
        ((λ '(k ⋅ Ψ), k ⋅ unshift n (c + m + k) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gunshift n c '(m ⋅ Φ) : garden :=
  m ⋅ unshift n (c + m) <$> Φ.

Fixpoint subst (n : nat) (t : term) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tsubst n t <$> args)
  | m ⋅ Φ ⊢ Δ =>
      m ⋅ subst (n + m) (tshift m 0 t) <$> Φ ⊢
        ((λ '(k ⋅ Ψ), k ⋅ subst (n + m + k) (tshift (m + k) 0 t) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gsubst n t '(m ⋅ Φ) : garden :=
  m ⋅ subst (n + m) (tshift m 0 t) <$> Φ.

Lemma shift_zero : ∀ ϕ c,
  shift 0 c ϕ = ϕ.
Proof.
  elim/flower_induction => [p args |[m Φ] Δ IHγ IHΔ] c /=.

  * pose proof (H := eq_map (tshift 0 c) id args (tshift_zero c)).
    by rewrite H list_fmap_id.

  * rewrite Forall_forall in IHγ; specialize (IHγ (c + m)).
    apply Forall_eq_map in IHγ; rewrite IHγ map_id_ext.

    elim: {Δ} IHΔ => [|[n Ψ] Δ IHΨ IHΔ IH] //=; inv IH.
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + m + n)).
    apply Forall_eq_map in IHΨ; rewrite IHΨ map_id_ext.
    by repeat f_equal.
Qed.

Lemma shift_add : ∀ ϕ c n m,
  shift (n + m) c ϕ = shift n c (shift m c ϕ).
Proof.
  elim/flower_induction => [p args |[k Φ] Δ IHγ IHΔ] c n m /=.

  * pose proof (H := eq_map (tshift (n + m) c) _ args (tshift_add c n m)).
    by rewrite H list_fmap_compose.

  * rewrite Forall_forall in IHγ; specialize (IHγ (c + k));
    rewrite Forall_forall in IHγ; specialize (IHγ n);
    rewrite Forall_forall in IHγ; specialize (IHγ m).
    apply Forall_eq_map in IHγ; rewrite IHγ list_fmap_compose.

    elim: {Δ} IHΔ => [|[l Ψ] Δ IHΨ IHΔ IH]//=; inv IH.
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + k + l));
    rewrite Forall_forall in IHΨ; specialize (IHΨ n);
    rewrite Forall_forall in IHΨ; specialize (IHΨ m).
    apply Forall_eq_map in IHΨ; rewrite IHΨ.
    f_equal. f_equal.
    by rewrite list_fmap_compose.
    done.
Qed.

Lemma shift_comm c n m ϕ :
  shift n c (shift m c ϕ) = shift m c (shift n c ϕ).
Proof.
  by rewrite -shift_add Nat.add_comm shift_add.
Qed.

Lemma bshift_zero : ∀ (Φ : bouquet) c,
  shift 0 c <$> Φ = Φ.
Proof.
  intros. rewrite -{2}[Φ]map_id_ext. apply eq_map.
  intros. by apply shift_zero.
Qed.

Lemma bshift_add : ∀ (Φ : bouquet) c n m,
  shift (n + m) c <$> Φ = shift n c <$> (shift m c <$> Φ).
Proof.
  intros. rewrite -list_fmap_compose. apply eq_map.
  intros. by apply shift_add.
Qed.

Lemma bshift_comm : ∀ (Φ : bouquet) c n m,
  shift n c <$> (shift m c <$> Φ) = shift m c <$> (shift n c <$> Φ).
Proof.
  intros. do 2 rewrite -list_fmap_compose. apply eq_map.
  intros. by apply shift_comm.
Qed.

(** ** Juxtaposition of gardens *)

(* Definition juxt '(n ⋅ Φ) '(m ⋅ Ψ) :=
  (n + m) ⋅ (shift m 0 <$> Φ) ++ (shift n m <$> Ψ).

Definition Juxt : list garden -> garden :=
  foldr juxt ∅.

Infix "∪" := juxt.
Notation "⋃ Δ" := (Juxt Δ).

Lemma juxt_empty γ :
  ∅ ∪ γ = γ.
Proof.
  case γ => n Φ //=.
  pose proof (eq_map (shift 0 n) id Φ (λ ϕ, shift_zero ϕ n)).
  by rewrite H list_fmap_id.
Qed. *)

Definition juxt (Φ Ψ : bouquet) :=
  Φ ++ Ψ.

Definition Juxt : list bouquet -> bouquet :=
  foldr app [].

Infix "∪" := juxt.
Notation "⋃ Φs" := (Juxt Φs).

Lemma Juxt_Bind : ∀ (Φs : list bouquet),
  ⋃ Φs = Φ ← Φs; Φ.
Proof.
  reflexivity.
Qed.

(** * Contexts *)

Inductive ctx :=
| Hole
| Planter (Φ : bouquet) (X : ctx) (Φ' : bouquet)
| Pistil (n : nat) (X : ctx) (Δ : list garden)
| Petal (γ : garden) (Δ : list garden) (n : nat) (X : ctx) (Δ' : list garden).

Notation "□" := Hole.

(** ** De Bruijn operations *)

(** *** Compute the number of variables bound in a given context *)

Fixpoint bv (X : ctx) : nat :=
  match X with
  | Hole => 0
  | Planter _ X _ => bv X
  | Pistil n X _ => n + bv X
  | Petal (n ⋅ _) _  m X _ => n + m + bv X
  end.

(** ** Context operations *)

Reserved Notation "X ⋖ Ψ" (at level 15).

Fixpoint fill (Ψ : bouquet) (X : ctx) : bouquet :=
  match X with
  | Hole => Ψ
  | Planter Φ X Φ' => Φ ++ X ⋖ Ψ ++ Φ'
  | Pistil n X Δ => [n ⋅ X ⋖ Ψ ⊢ Δ]
  | Petal γ Δ n X Δ' => [γ ⊢ Δ ++ [n ⋅ X ⋖ Ψ] ++ Δ']
  end
where "X ⋖ Ψ" := (fill Ψ X).

Definition fillac Ψ X :=
  X ⋖ (shift (bv X) 0 <$> Ψ).

Notation "X ⋖! Ψ" := (fillac Ψ X) (at level 15).

Reserved Infix "⪡" (at level 15).

Fixpoint comp (X : ctx) (Y : ctx) : ctx :=
  match X with
  | Hole => Y
  | Planter Φ X Φ' => Planter Φ (X ⪡ Y) Φ
  | Pistil n X Δ => Pistil n (X ⪡ Y) Δ
  | Petal γ Δ n X Δ' => Petal γ Δ n (X ⪡ Y) Δ'
  end
where "X ⪡ Y" := (comp X Y).

(** ** Path operations *)

(** A path is simply a list of integers *)

Definition path := list nat.

(** Path operations may fail if the specified path has no denotation in the
    corresponding tree. Thus they live in the Option monad.

    In the setting of a pointing-based proving GUI, this becomes useless because
    the user can only select meaningful paths. *)

(** *** Compute the context and subobject associated to a path *)

Fixpoint bpath p Φ : option (ctx * bouquet) :=
  match p with
  | [] => Some (Hole, Φ)
  | i :: p =>
      lr ← split_at i Φ;
      let '(Φ, Φ') := lr in
      match Φ' with
      | ϕ :: Φ' =>
          XΨ ← fpath p ϕ;
          let '(X, Ψ) := XΨ in
          Some (Planter Φ X Φ', Ψ)
      | _ => None
      end
  end
with fpath p ϕ :=
  match p with
  | [] => Some (Hole, [ϕ])
  | i :: p =>
      match ϕ with
      | γ ⊢ Δ =>
          match i with
          | 0 =>
              let '(n ⋅ Φ) := γ in
              XΨ ← bpath p Φ;
              let '(X, Ψ) := XΨ in
              Some (Pistil n X Δ, Ψ)
          | _ =>
              lr ← split_at (i - 1) Δ;
              let '(Δ, Δ') := lr in
              match Δ' with
              | (n ⋅ Φ) :: Δ' =>
                  XΨ ← bpath p Φ;
                  let '(X, Ψ) := XΨ in
                  Some (Petal γ Δ n X Δ', Ψ)
              | _ => None
              end
          end
      | _ => None
      end
  end.

(** *** Retrieve subobjects *)

Definition bget (p : path) (Φ : bouquet) : option bouquet :=
  _Ψ ← bpath p Φ;
  let '(_, Ψ) := _Ψ in
  Some Ψ.

(** *** Modify subobjects *)

Definition bset (Ψ : bouquet) (p : path) (Φ : bouquet) : option bouquet :=
  X_ ← bpath p Φ;
  let '(X, _) := X_ in
  Some (X ⋖ Ψ).

Open Scope string_scope.
Compute λ ϕ : flower, bset [] [1] [∅ ⊢ [(0 ⋅ [ϕ; Atom "a" []]); (4 ⋅ [Atom "c" []])]].
Close Scope string_scope.

(** * Rules *)

Reserved Notation "Ψ ≺ n 'in' X" (at level 80).

Inductive pollin : bouquet -> nat -> ctx -> Prop :=
| P_self Ψ X n Φ Φ' Δ m Δ' :
  Ψ ≺ (m + bv X) in (Petal (n ⋅ Φ ++ Ψ ++ Φ') Δ m X Δ')
| P_wind_l Ψ X Φ Φ' Φ'' :
  Ψ ≺ (bv X) in (Planter Φ'' X (Φ ++ Ψ ++ Φ'))
| P_wind_r Ψ X Φ Φ' Φ'' :
  Ψ ≺ (bv X) in (Planter (Φ ++ Ψ ++ Φ') X Φ'')
where "Ψ ≺ n 'in' X" := (pollin Ψ n X).

Definition assum (Ψ : bouquet) (X : ctx) :=
  ∃ X0 n X1, Ψ ≺ n in X1 /\ X = X0 ⪡ X1.

Notation "Ψ ∈ X" := (assum Ψ X).

(** ** Local rules *)

Reserved Infix "⇀" (at level 80).

Inductive step : bouquet -> bouquet -> Prop :=

(** *** Pollination *)

| R_pol (Ψ : bouquet) n X :
  Ψ ≺ n in X ->
  X ⋖ (shift n 0 <$> Ψ) ⇀
  X ⋖ []

| R_co_pol (Ψ : bouquet) n X :
  Ψ ≺ n in X ->
  X ⋖ [] ⇀
  X ⋖ (shift n 0 <$> Ψ)

(** *** Empty pistil *)

| R_epis_pis m Ψ n Φ Φ' Δ :
  n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' ⊢ Δ ⇀
  n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ') ⊢ gshift m 0 <$> Δ

| R_epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  γ ⊢ Δ ++ [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'] ++ Δ' ⇀
  γ ⊢ Δ ++ [n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ')] ++ Δ'

| R_co_epis_pis m Ψ n Φ Φ' Δ :
  n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ') ⊢ (gshift m 0 <$> Δ) ⇀
  n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' ⊢ Δ

| R_co_epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  γ ⊢ Δ ++ [n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ')] ++ Δ' ⇀
  γ ⊢ Δ ++ [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'] ++ Δ'

(** *** Empty petal *)

| R_pet	γ Δ Δ' :
  γ ⊢ Δ ++ [∅] ++ Δ' ⇀
  []

(** *** Reproduction *)

| R_rep Δ n Φ Φ' Δ' :
  n ⋅ Φ ++ [⊢ Δ] ++ Φ' ⊢ Δ' ⇀
  n ⋅ Φ ++ Φ' ⊢ [0 ⋅ (λ '(m ⋅ Ψ), m ⋅ Ψ ⊢ gshift m 0 <$> Δ') <$> Δ]

(** *** Instantiation *)

| R_ipis i t n Φ Δ :
  0 <= i <= n ->
  S n ⋅ Φ ⊢ Δ ⇀
  [n ⋅ unshift 1 i <$> (subst i (tshift (S n) 0 t) <$> Φ) ⊢ gunshift 1 i <$> (gsubst i (tshift (S n) 0 t) <$> Δ); S n ⋅ Φ ⊢ Δ]

| R_ipet i t n Φ γ Δ Δ' :
  0 <= i <= n ->
  γ ⊢ Δ ++ [S n ⋅ Φ] ++ Δ' ⇀
  γ ⊢ Δ ++ [n ⋅ unshift 1 i <$> (subst i (tshift (S n) 0 t) <$> Φ); S n ⋅ Φ] ++ Δ'

where "Φ ⇀ Ψ" := (step Φ Ψ).

(** ** Contextual closure *)

Reserved Infix "~>" (at level 80).

Inductive cstep : bouquet -> bouquet -> Prop :=

(** *** Congruence *)

| R_ctx (X : ctx) (Φ Ψ : bouquet) :
  Φ ⇀ Ψ ->
  X ⋖ Φ ~> X ⋖ Ψ

where "Φ ~> Ψ" := (cstep Φ Ψ).

(** ** Transitive closure *)

Infix "~>*" := (rtc cstep) (at level 80).

Notation "Φ <~> Ψ" := (Φ ~>* Ψ /\ Ψ ~>* Φ) (at level 80).

(** * Basic proof search *)

(* TODO: rewrite all tactics *)

Ltac sub_at p :=
  match goal with
  | |- ?Φ ~>* _ => eval cbn in (bget p Φ)
  end.

Ltac rstep Ψ :=
  apply (rtc_l cstep _ Ψ).

Ltac rstepm p Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let Φ' := eval cbn in (bset Ψ p Φ) in
      match Φ' with
      | None => idtac
      | Some ?Φ' => rstep Φ'; list_simplifier
      end
  end.

Ltac rstepm_cons p i Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let ΦΣ := eval cbn in (bpath p Φ) in
      match ΦΣ with
      | Some (?Φ, ?n ⋅ ?Σ1 :: ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ Ψ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 :: Ψ)
          end
      end
  end.

Ltac rstepm_app p i Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let ΦΣ := eval cbn in (bpath p Φ) in
      match ΦΣ with
      | Some (?Φ, ?n ⋅ ?Σ1 ++ ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ Ψ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 ++ Ψ)
          end
      end
  end.

Ltac rtransm p Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let Φ' := eval cbn in (bset Ψ p Φ) in
      transitivity Φ'; list_simplifier
  end.

Lemma fill_hole Ψ :
  □ ⋖ Ψ = Ψ.
Proof.
  reflexivity.
Qed.

Ltac rctx X Φ Ψ :=
  apply (R_ctx X Φ Ψ).

Ltac rctxm p :=
  match goal with
  | |- ?Φ ⇀ ?Ψ =>
      let spΦ := eval cbn in (bpath p Φ) in
      let spΨ := eval cbn in (bpath p Ψ) in
      match spΦ with
      | Some (?Φ, ?Φ0) =>
          match spΨ with
          | Some (_, ?Ψ0) =>
              rctx Φ Φ0 Ψ0
          end
      end
  end.

Ltac rcstepm p Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let spΦ := eval cbn in (bpath p Φ) in
      match spΦ with
      | Some (?Φ, ?Φ0) =>
          rstepm p Ψ; [> rctx Φ Φ0 Ψ | ..]
      end
  end.

Ltac rctxmt p Ψ0 :=
  match goal with
  | |- ?Φ ~>* ?Ψ =>
      let spΦ := eval cbn in (bpath p Φ) in
      let spΨ := eval cbn in (bpath p Ψ) in
      match spΦ with
      | Some (?Φ, ?Φ0) =>
          let H := fresh "H" in
          pose proof (H := Φ Φ0 Ψ0);
          repeat rewrite fill_hole/= in H; list_simplifier;
          apply H; clear H
      end
  end.

Ltac rctxmH p H :=
  match type of H with
  | _ ~>* ?Ψ0 =>
      rtransm p Ψ0; [> rctxmt p Ψ0; exact H | ..]
  end.

Ltac rself :=
  match goal with
  | |- ?Φ ~> ?Ψ =>
      rctx □ Φ Ψ
  end.

Ltac rwpol Φ Φ :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_pol Φ Φ);
  pose proof (Hdel := R_co_pol Φ Φ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rwpolm p :=
  match goal with
  | |- ?n ⋅ ?Φ ++ ?Ψ ⇀ _ =>
      let spΨ := eval cbn in (bpath p (n ⋅ Ψ)) in
      match spΨ with
      | Some (?Φ, _) =>
          rwpol Φ (n ⋅ Φ)
      end
  end.

Ltac rspol Φ Φ Ψ Δ :=
  let Hins := fresh "Hins" in
  let Hdel := fresh "Hdel" in
  pose proof (Hins := R_pol Φ Φ Ψ Δ);
  pose proof (Hdel := R_co_pol Φ Φ Ψ Δ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rspolm p :=
  match goal with
  | |- ?Φ ⇀ _ =>
      let spΦ := eval cbn in (bpath p Φ) in
      match spΦ with
      | Some (Planter [] (Petal ?Φ' [] ?Φ ?Δ') [], ?Ψ) =>
          rspol Φ Φ' ∅ Δ'
      end
  end.

Ltac spol p :=
  match goal with
  | |- ?n ⋅ [?Φ ⊢ _] ~>* _ =>
      rstepm p Φ; [> rself; rspolm p | ..]
  end.

Ltac rrep :=
  match goal with
  | |- ?n ⋅ [?m ⋅ (∅ ⊢ ?Ψs) :: ?Φ ⊢ ?Δ] ⇀ _ =>
      let H := fresh "H" in
      pose proof (H := R_rep (?m ⋅ Φ) Ψs Δ);
      repeat rewrite fill_hole/= in H; list_simplifier;
      exact H; clear H
  end.

Ltac rpis :=
  apply R_epis_pis.

Ltac rcopis :=
  apply R_co_epis_pis.

Ltac rpism p :=
  match sub_at p with
  | Some ((⊢ [?Ψ])) =>
      rcstepm p Ψ; [> rpis | ..]
  end.

Ltac rcopism p :=
  match sub_at p with
  | Some ?Ψ => 
      rcstepm p (0 ⋅ [⊢ [Ψ]]); [> rcopis | ..]
  end.

Ltac rpet :=
  apply R_pet.

Ltac rpetm p :=
  rcstepm p ∅; [> rpet | ..].

Open Scope string_scope.

Example deriv_contraction :
  [Atom "a" []; Atom "b" []] ~>* [Atom "a" []; Atom "b" []; Atom "b" []].
Proof.
  apply rtc_once.
Admitted.