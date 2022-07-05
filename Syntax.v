Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Utils.

(** Flowers *)

Inductive flower :=
| Atom : name -> flower
| Flower : garden -> list garden -> flower
with garden :=
| Garden : list flower -> garden.

Coercion Atom : name >-> flower.

Definition fg : flower -> garden := fun f => Garden [f].
Coercion fg : flower >-> garden.

Definition gl : garden -> list flower := fun '(Garden Fs) => Fs.
Coercion gl : garden >-> list.

Notation "♯ a" := (Atom a) (format "♯ a", at level 1).
Notation "Γ ⊢ Π" := (Flower Γ Π) (at level 65).
Notation "Γ ⊢" := (Flower Γ nil) (at level 65).
Notation "⊢ Π" := (Flower (Garden nil) Π) (at level 65).

Notation "⋅ Fs" := (Garden Fs) (format "⋅ Fs", at level 63).
Notation "∅" := (Garden nil).

(** * Induction principles *)

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pi : nat -> Prop) (Pa : name -> Prop),
  let PΓ : garden -> Prop := Forall P in
  (∀ (a : name), Pa a) ->
  (∀ (a : name), Pa a -> P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    PΓ Γ -> Forall PΓ Π -> P (Γ ⊢ Π)) ->
  (∀ (Fs : list flower),
    Forall P Fs -> PΓ (⋅ Fs)) ->
  ∀ (f : flower), P f.
Proof.
  move => P Pi Pa PΓ Ha IHa IHF IHΓ.
  fix IH 1.
  elim => [a |Γ Π].
  * apply IHa. by apply Ha.
  * apply IHF.
    - case: Γ => Fs.
      apply IHΓ.
      elim: Fs => [|F Fs IHFs] //.
      decompose_Forall; auto.
    - elim: Π => [|Δ Π IHΠ] //.
      decompose_Forall; auto.
      case Δ => Fs. apply IHΓ.
      decompose_Forall; auto.
Qed.

Definition garden_induction_full :
  ∀ (P : garden -> Prop)
    (Pi : nat -> Prop) (Pa : name -> Prop),
  (∀ (a : name), Pa a) ->
  (∀ (a : name), Pa a -> P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    P Γ -> Forall P Π -> P (Γ ⊢ Π)) ->
  P ∅ ->
  (∀ (F : flower) (Fs : list flower),
    P F -> P (⋅ Fs) -> P (⋅ F :: Fs)) ->
  ∀ (Γ : garden), P Γ.
Proof.
  move => P Pi Pa Ha IHa IHF IHnil IHcons.
  fix IH 1.
  case => Fs.
  elim: Fs => [|F Fs IHFs].
  by apply: IHnil.
  apply: IHcons.
  - elim: F => [a |Γ Π].
    + apply IHa. by apply Ha.
    + apply IHF.
        exact: IH.
        decompose_Forall.
  - exact: IHFs.
Qed.

Definition flower_induction	:
  ∀ (P : flower -> Prop),
  let PΓ : garden -> Prop := Forall P in
  (∀ (a : name), P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    PΓ Γ -> Forall PΓ Π -> P (Γ ⊢ Π)) ->
  ∀ (F : flower), P F.
Proof.
  move => P PΓ IHa IHΓ.
  eapply flower_induction_full; eauto.
  Unshelve.
  1: { exact (fun _ => True). }
  2: { exact (fun _ => True). }
  all: done.
Qed.

Definition garden_induction	:
  ∀ (P : garden -> Prop),
  (∀ (a : name), P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    P Γ -> Forall P Π -> P (Γ ⊢ Π)) ->
  P ∅ ->
  (∀ (F : flower) (Fs : list flower),
    P F -> P (⋅ Fs) -> P (⋅ F :: Fs)) ->
  ∀ (Γ : garden), P Γ.
Proof.
  move => P IHa IHF IHnil IHcons.
  eapply garden_induction_full; eauto.
  Unshelve.
  1: { exact (fun _ => True). }
  2: { exact (fun _ => True). }
  all: done.
Qed.

(** * Contexts *)

Definition juxt '(⋅ Fs) '(⋅ Gs) :=
  ⋅ (Fs ++ Gs).

Infix "∪" := juxt.

Inductive fctx :=
| Hole
| Pistil (γ : gctx) (Π : list garden)
| Petal (Γ : garden) (Π : list garden) (γ : gctx) (Π' : list garden)
with gctx :=
| Planter (Fs : list flower) (ϕ : fctx) (Gs : list flower).

Notation "□" := Hole.

Definition fctx_to_gctx ϕ := Planter [] ϕ [].
Coercion fctx_to_gctx : fctx >-> gctx.

Definition gctx_induction :
  ∀ (P : gctx -> Prop),
  P □ ->
  (∀ γ : gctx, P γ -> ∀ Π, P (Pistil γ Π)) ->
  (∀ γ : gctx, P γ -> ∀ Γ Π Π', P (Petal Γ Π γ Π')) ->
  (∀ ϕ : fctx, P ϕ -> ∀ Fs Gs, P (Planter Fs ϕ Gs)) ->
  ∀ γ, P γ.
Proof.
  move => P HHole HPistil HPetal HPlanter.
  fix IH 1.
  case => Fs ϕ Gs. apply HPlanter.
  case: ϕ => [|γ Π |Γ Π γ Π'].
  * apply HHole.
  * apply HPistil. apply IH.
  * apply HPetal. apply IH.
Qed.

Fixpoint ffill (Δ : garden) (ϕ : fctx) : garden :=
  match ϕ with
  | □ => Δ
  | Pistil γ Π => gfill Δ γ ⊢ Π
  | Petal Γ Π γ Π' => Γ ⊢ Π ++ [gfill Δ γ] ++ Π'
  end
with gfill (Δ : garden) (γ : gctx) : garden :=
  match γ with
  | Planter Fs ϕ Gs => ⋅(Fs ++ (ffill Δ ϕ) ++ Gs)
  end.

Notation "γ ! Δ" := (gfill Δ γ) (at level 30).

(** * Rules *)

Reserved Infix "⇀" (at level 80).

Inductive step : garden -> garden -> Prop :=

(** ** Pollination *)

| R_wpol (γ : gctx) (Γ : garden) :
  Γ ∪ γ ! ∅ ⇀
  Γ ∪ γ ! Γ

| R_co_wpol (γ : gctx) (Γ : garden) :
  Γ ∪ γ ! Γ ⇀
  Γ ∪ γ ! ∅

| R_spol (γ : gctx) (Γ Δ : garden) (Π : list garden) :
  Γ ∪ Δ ⊢ γ ! ∅ :: Π ⇀
  Γ ∪ Δ ⊢ γ ! Γ :: Π

| R_co_spol (γ : gctx) (Γ Δ : garden) (Π : list garden) :
  Γ ∪ Δ ⊢ γ ! Γ :: Π ⇀
  Γ ∪ Δ ⊢ γ ! ∅ :: Π

(** ** Reproduction *)

| R_rep (Γ : garden) (Δs Π : list garden) :
  (⊢ Δs) ∪ Γ ⊢ Π ⇀
  Γ ⊢ [⋅ (λ Δ, Δ ⊢ Π) <$> Δs]

(** ** Decomposition *)

| R_pis	(Δ : garden) :
  ⊢ [Δ] ⇀ Δ

| R_co_pis (Δ : garden) :
  Δ ⇀ ⊢ [Δ]

| R_pet	(Γ : garden) (Π : list garden) :
  Γ ⊢ ∅ :: Π ⇀ ∅

(** ** Permutation *)

| R_perm_g (Fs Fs' : list flower) :
  Fs ≡ₚ Fs' ->
  ⋅ Fs ⇀ ⋅ Fs'

| R_perm_f (Π Π' : list garden) (Γ : garden) :
  Π ≡ₚ Π' ->
  Γ ⊢ Π ⇀ Γ ⊢ Π'

where "Γ ⇀ Δ" := (step Γ Δ).

(** ** Contextual closure *)

Reserved Infix "~>" (at level 80).

Inductive cstep : garden -> garden -> Prop :=
| R_ctx (γ : gctx) (Γ Δ : garden) :
  Γ ⇀ Δ ->
  γ ! Γ ~> γ ! Δ

where "Γ ~> Δ" := (cstep Γ Δ).

(** ** Transitive closure *)

Infix "~>*" := (rtc cstep) (at level 80).

Notation "Γ <~> Δ" := (Γ ~>* Δ /\ Δ ~>* Γ) (at level 80).

(** ** Examples *)

Open Scope string_scope.

Example deriv_contraction :
  ⋅ [♯"a"; ♯"b"] ~>* ⋅ [♯"a"; ♯"b"; ♯"b"].
Proof.
  apply rtc_once.
  apply (R_ctx (Planter [♯"a"] □ []) ♯"b" (⋅[♯"b"; ♯"b"])).
  apply (R_wpol (Planter [] □ []) ♯"b").
Qed.

(** Basic proof search *)

Ltac rstep Δ :=
  apply (rtc_l cstep _ Δ).

Ltac rctx γ :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      apply (R_ctx γ Γ Δ)
  end.

Lemma fill_hole Γ :
  □ ! Γ = Γ.
Proof.
  case Γ => Fs /=. list_simplifier. reflexivity.
Qed.

Ltac rwpol γ Γ :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_wpol γ Γ);
  pose proof (Hdel := R_co_wpol γ Γ);
  repeat rewrite fill_hole in Hins, Hdel; (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rspol γ Γ Δ Π :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_spol γ Γ Δ Π);
  pose proof (Hdel := R_co_spol γ Γ Δ Π);
  repeat rewrite fill_hole in Hins, Hdel; (exact Hins || exact Hdel);
  clear Hins Hdel.