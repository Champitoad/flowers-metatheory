Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Terms Flowers.Utils.

(** * Flowers *)

Inductive flower :=
| Atom (p : name) (args : list term)
| Flower (γ : garden) (Δ : list garden)
with garden :=
| Garden (n : nat) (Φ : list flower).

Definition bouquet := list flower.

Definition ftog : flower -> garden := fun ϕ => Garden 0 [ϕ].
Coercion ftog : flower >-> garden.

Notation "∅" := (Garden 0 nil).
Notation "n ⋅ Φ" := (Garden n Φ) (format "n  ⋅  Φ", at level 63).

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
      decompose_Forall; auto.
    - elim: Δ => [|δ Δ IHΔ] //.
      decompose_Forall; auto.
      case δ => n Φ. apply IHgarden; auto.
      decompose_Forall; auto.
Qed.

Definition garden_induction_full :
  ∀ (P : garden -> Prop)
    (Pt : term -> Prop)
  (IHt : ∀ (t : term), Pt t)
  (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
  (IHflower : ∀ (γ : garden) (Δ : list garden),
    P γ -> Forall P Δ -> P (γ ⊢ Δ))
  (IHnil : ∀ n, P (n ⋅ []))
  (IHcons : ∀ (ϕ : flower) (n : nat) (Φ : bouquet),
    P ϕ -> P (n ⋅ Φ) -> P (n ⋅ ϕ :: Φ)),
  ∀ (γ : garden), P γ.
Proof.
  intros. move: γ. fix IH 1. induction γ.
  elim: Φ => [|ϕ Φ IHΦ].
  by apply: IHnil.
  apply: IHcons.
  - elim: ϕ => [p args |γ Δ].
    + apply IHatom. apply In_Forall. intros. by apply IHt.
    + apply IHflower.
        exact: IH.
        decompose_Forall.
  - exact: IHΦ.
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
  exact (fun _ => I).
Qed.

Definition garden_induction	:
  ∀ (P : garden -> Prop)
  (IHatom : ∀ p args, P (Atom p args))
  (IHflower : ∀ (γ : garden) (Δ : list garden),
    P γ -> Forall P Δ -> P (γ ⊢ Δ))
  (IHnil : ∀ n, P (n ⋅ []))
  (IHcons : ∀ (ϕ : flower) (n : nat) (Φ : bouquet),
    P ϕ -> P (n ⋅ Φ) -> P (n ⋅ ϕ :: Φ)),
  ∀ (γ : garden), P γ.
Proof.
  intros; eapply garden_induction_full; eauto.
  exact (fun _ => I).
Qed.

(** ** Operations on De Bruijn indices *)

Fixpoint fshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tshift n c <$> args)
  | m ⋅ Φ ⊢ Δ => m ⋅ fshift n (c + m) <$> Φ ⊢ gshift n (c + m) <$> Δ
  end
with gshift (n : nat) (c : nat) (γ : garden) : garden :=
  match γ with
  | m ⋅ Φ => m ⋅ fshift n (c + m) <$> Φ
  end.

Fixpoint funshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tunshift n c <$> args)
  | m ⋅ Φ ⊢ Δ => m ⋅ funshift n (c + m) <$> Φ ⊢ gunshift n (c + m) <$> Δ
  end
with gunshift (n : nat) (c : nat) (γ : garden) : garden :=
  match γ with
  | m ⋅ Φ => m ⋅ funshift n (c + m) <$> Φ
  end.

Lemma fshift_zero c : ∀ ϕ,
  fshift 0 c ϕ = ϕ.
Admitted.

Fixpoint fsubst (n : nat) (t : term) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tsubst n t <$> args)
  | m ⋅ Φ ⊢ Δ => m ⋅ fsubst (n+m) (tshift m 0 t) <$> Φ ⊢ gsubst (n+m) (tshift m 0 t) <$> Δ
  end
with gsubst (n : nat) (t : term) (γ : garden) : garden :=
  match γ with
  | m ⋅ Φ => m ⋅ fsubst (n+m) (tshift m 0 t) <$> Φ
  end.

(** ** Juxtaposition of gardens *)

Definition juxt '(n ⋅ Φ) '(m ⋅ Ψ) :=
  (n + m) ⋅ (fshift m 0 <$> Φ) ++ (fshift n m <$> Ψ).

Definition Juxt : list garden -> garden :=
  foldr juxt ∅.

Infix "∪" := juxt.
Notation "⋃ Δ" := (Juxt Δ).

Lemma juxt_empty γ :
  ∅ ∪ γ = γ.
Proof.
  case γ => n Φ //=.
  pose proof (eq_map (fshift 0 n) id Φ (fshift_zero n)).
  by rewrite H list_fmap_id.
Qed.

(** * Contexts *)

Inductive ctx :=
| Hole
| Planter (Φ : bouquet) (X : ctx) (Φ' : bouquet)
| Pistil (n : nat) (X : ctx) (Δ : list garden)
| Petal (γ : garden) (Δ : list garden) (n : nat) (X : ctx) (Δ' : list garden).

Notation "□" := Hole.

(** ** Induction principles *)

Section Induction.

Check ctx_ind.

End Induction.

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

Definition Xtob X := X ⋖ [].
Coercion Xtob : ctx >-> bouquet.

Definition fillac Ψ X :=
  X ⋖ (fshift (bv X) 0 <$> Ψ).

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

Reserved Notation "ϕ ≺ n 'in' X" (at level 80).

Inductive pollin : flower -> nat -> ctx -> Prop :=
| P_self ϕ X n Φ Φ' Δ m Δ' :
  ϕ ≺ (m + bv X) in (Petal (n ⋅ Φ ++ [ϕ] ++ Φ') Δ m X Δ')
| P_wind_l ϕ X Φ Φ' Φ'' :
  ϕ ≺ (bv X) in (Planter Φ'' X (Φ ++ [ϕ] ++ Φ'))
| P_wind_r ϕ X Φ Φ' Φ'' :
  ϕ ≺ (bv X) in (Planter (Φ ++ [ϕ] ++ Φ') X Φ'')
where "ϕ ≺ n 'in' X" := (pollin ϕ n X).

Definition assum (ϕ : flower) (X : ctx) :=
  ∃ X0 n X1, ϕ ≺ n in X1 /\ X = X0 ⪡ X1.

Notation "ϕ ∈ X" := (assum ϕ X).

(** ** Local rules *)

Reserved Infix "⇀" (at level 80).

Inductive step : bouquet -> bouquet -> Prop :=

(** *** Pollination *)

| R_pol ϕ n X :
  ϕ ≺ n in X ->
  X ⋖ [fshift n 0 ϕ] ⇀
  X ⋖ []

| R_co_pol ϕ n X :
  ϕ ≺ n in X ->
  X ⋖ [] ⇀
  X ⋖ [fshift n 0 ϕ]

(** *** Empty pistil *)

| R_epis_pis m Ψ n Φ Φ' Δ :
  [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' ⊢ Δ] ⇀
  [n + m ⋅ (fshift m 0 <$> Φ) ++ Ψ ++ (fshift m 0 <$> Φ') ⊢ (gshift m 0 <$> Δ)]

| R_epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  [γ ⊢ Δ ++ [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'] ++ Δ'] ⇀
  [γ ⊢ Δ ++ [n + m ⋅ (fshift m 0 <$> Φ) ++ Ψ ++ (fshift m 0 <$> Φ')] ++ Δ']

| R_co_epis_pis m Ψ n Φ Φ' Δ :
  [n + m ⋅ (fshift m 0 <$> Φ) ++ Ψ ++ (fshift m 0 <$> Φ') ⊢ (gshift m 0 <$> Δ)] ⇀
  [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' ⊢ Δ]

| R_co_epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  [γ ⊢ Δ ++ [n + m ⋅ (fshift m 0 <$> Φ) ++ Ψ ++ (fshift m 0 <$> Φ')] ++ Δ'] ⇀
  [γ ⊢ Δ ++ [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'] ++ Δ']

(** *** Empty petal *)

| R_pet	n γ Δ Δ' :
  [γ ⊢ Δ ++ [n ⋅ []] ++ Δ'] ⇀
  []

(** *** Reproduction *)

| R_rep Δ n Φ Φ' Δ' :
  [n ⋅ Φ ++ [⊢ Δ] ++ Φ' ⊢ Δ'] ⇀
  [n ⋅ Φ ++ Φ' ⊢ [0 ⋅ (λ δ, δ ⊢ Δ') <$> Δ]]

(** *** Instantiation *)

| R_ipis i t n Φ Δ :
  [n ⋅ Φ ⊢ Δ] ⇀
  [n-1 ⋅ funshift 1 i <$> (fsubst i (tshift n 0 t) <$> Φ) ⊢ gunshift 1 i <$> (gsubst i (tshift n 0 t) <$> Δ); n ⋅ Φ ⊢ Δ]

| R_ipet i t n Φ γ Δ Δ' :
  [γ ⊢ Δ ++ [n ⋅ Φ] ++ Δ] ⇀
  [γ ⊢ Δ ++ [n-1 ⋅ funshift 1 i <$> (fsubst i (tshift n 0 t) <$> Φ); n ⋅ Φ] ++ Δ']

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
  | |- ?γ ~>* _ => eval cbn in (bget p γ)
  end.

Ltac rstep δ :=
  apply (rtc_l cstep _ δ).

Ltac rstepm p δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γ' := eval cbn in (bset p δ γ) in
      rstep γ'; list_simplifier
  end.

Ltac rstepm_cons p i δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γΣ := eval cbn in (bpath p γ) in
      match γΣ with
      | Some (?γ, ?n ⋅ ?Σ1 :: ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ δ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 :: δ)
          end
      end
  end.

Ltac rstepm_app p i δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γΣ := eval cbn in (bpath p γ) in
      match γΣ with
      | Some (?γ, ?n ⋅ ?Σ1 ++ ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ δ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 ++ δ)
          end
      end
  end.

Ltac rtransm p δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γ' := eval cbn in (bset p δ γ) in
      transitivity γ'; list_simplifier
  end.

Lemma fill_hole Ψ :
  □ ⋖ Ψ = Ψ.
Proof.
  reflexivity.
Qed.

Ltac rctx γ γ δ :=
  let H := fresh "H" in
  pose proof (H := R_ctx γ γ δ);
  repeat rewrite fill_hole/= in H; list_simplifier;
  apply H; clear H.

Ltac rctxm p :=
  match goal with
  | |- ?γ ⇀ ?δ =>
      let spγ := eval cbn in (bpath p γ) in
      let spδ := eval cbn in (bpath p δ) in
      match spγ with
      | Some (?γ, ?γ0) =>
          match spδ with
          | Some (_, ?δ0) =>
              rctx γ γ0 δ0
          end
      end
  end.

Ltac rcstepm p δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let spγ := eval cbn in (bpath p γ) in
      match spγ with
      | Some (?γ, ?γ0) =>
          rstepm p δ; [> rctx γ γ0 δ | ..]
      end
  end.

Ltac rctxmt p δ0 :=
  match goal with
  | |- ?γ ~>* ?δ =>
      let spγ := eval cbn in (bpath p γ) in
      let spδ := eval cbn in (bpath p δ) in
      match spγ with
      | Some (?γ, ?γ0) =>
          let H := fresh "H" in
          pose proof (H := γ γ0 δ0);
          repeat rewrite fill_hole/= in H; list_simplifier;
          apply H; clear H
      end
  end.

Ltac rctxmH p H :=
  match type of H with
  | _ ~>* ?δ0 =>
      rtransm p δ0; [> rctxmt p δ0; exact H | ..]
  end.

Ltac rself :=
  match goal with
  | |- ?γ ⇀ ?δ =>
      rctx Hole γ δ
  end.

Ltac rwpol γ γ :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_pol γ γ);
  pose proof (Hdel := R_co_pol γ γ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rwpolm p :=
  match goal with
  | |- ?n ⋅ ?γ ++ ?δ ⇀ _ =>
      let spδ := eval cbn in (bpath p (n ⋅ δ)) in
      match spδ with
      | Some (?γ, _) =>
          rwpol γ (n ⋅ γ)
      end
  end.

Ltac rspol γ γ δ Δ :=
  let Hins := fresh "Hins" in
  let Hdel := fresh "Hdel" in
  pose proof (Hins := R_pol γ γ δ Δ);
  pose proof (Hdel := R_co_pol γ γ δ Δ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rspolm p :=
  match goal with
  | |- ?γ ⇀ _ =>
      let spγ := eval cbn in (bpath p γ) in
      match spγ with
      | Some (Planter [] (Petal ?γ' [] ?γ ?Δ') [], ?δ) =>
          rspol γ γ' ∅ Δ'
      end
  end.

Ltac spol p :=
  match goal with
  | |- ?n ⋅ [?γ ⊢ _] ~>* _ =>
      rstepm p γ; [> rself; rspolm p | ..]
  end.

Ltac rrep :=
  match goal with
  | |- ?n ⋅ [?m ⋅ (∅ ⊢ ?δs) :: ?γ ⊢ ?Δ] ⇀ _ =>
      let H := fresh "H" in
      pose proof (H := R_rep (?m ⋅ γ) δs Δ);
      repeat rewrite fill_hole/= in H; list_simplifier;
      exact H; clear H
  end.

Ltac rpis :=
  apply R_epis_pis.

Ltac rcopis :=
  apply R_co_epis_pis.

Ltac rpism p :=
  match sub_at p with
  | Some ((⊢ [?δ])) =>
      rcstepm p δ; [> rpis | ..]
  end.

Ltac rcopism p :=
  match sub_at p with
  | Some ?δ => 
      rcstepm p (0 ⋅ [⊢ [δ]]); [> rcopis | ..]
  end.

Ltac rpet :=
  apply R_pet.

Ltac rpetm p :=
  rcstepm p ∅; [> rpet | ..].

(** ** Generalized rewriting *)

(* Add Parametric Relation : garden itr
  reflexivity proved by (rtc_refl cstep)
  transitivity proved by rtc_transitive
  as itr_preorder.

Add Parametric Morphism : Flower with signature
  itr ==> Forall2 itr ==> itr
  as proper_itr_Flower.
Proof.
  intros γ δ Hpis Δ Δ' Hpet.
  induction Hpis, Hpet; auto.
Admitted.

Add Parametric Morphism : Garden with signature
  Forall2 (λ F G : flower, F ~>* G) ==> itr
  as proper_itr_Garden.
Proof.
Admitted. *)

(** ** Examples *)

Open Scope string_scope.

Example deriv_contraction :
  [Atom "a" []; Atom "b" []] ~>* [Atom "a" []; Atom "b" []; Atom "b" []].
Proof.
  apply rtc_once.
Admitted.