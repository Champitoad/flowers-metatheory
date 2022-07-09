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

Definition Juxt : list garden -> garden :=
  foldr juxt ∅.

Infix "∪" := juxt.
Notation "⋃ Π" := (Juxt Π).

Lemma juxt_empty Γ :
  Γ ∪ ∅ = Γ.
Proof.
  case Γ => Fs //=. list_simplifier. reflexivity.
Qed.

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

Fixpoint fcomp (δ : gctx) (ϕ : fctx) : gctx :=
  match ϕ with
  | □ => δ
  | Pistil γ Π => Pistil (gcomp δ γ) Π
  | Petal Γ Π γ Π' => Petal Γ Π (gcomp δ γ) Π'
  end
with gcomp (δ : gctx) (γ : gctx) : gctx :=
  match γ with
  | Planter Fs ϕ Gs =>
      match fcomp δ ϕ with
      | Planter Fs' γ' Gs' => Planter (Fs ++ Fs') γ' (Gs' ++ Gs)
      end
  end.

Notation "γ !∘ δ" := (gcomp δ γ) (at level 10).

Lemma gcomp_gfill : ∀ γ δ Γ,
  γ ! (δ ! Γ) = γ !∘ δ ! Γ.
Proof.
  elim/gctx_induction; intros; simpl; list_simplifier.
  * case δ; intros; list_simplifier; auto.
  * by rewrite H.
  * by rewrite H.
  * specialize (H δ Γ). destruct (fcomp δ ϕ); intros; list_simplifier.
    rewrite H. by list_simplifier.
Qed.

Definition split_at {A} (i : nat) (xs : list A) : option (list A * list A) :=
  let fix aux l i xs :=
    match i, xs with
    | 0, _ => Some (reverse l, xs)
    | S n, a :: xs => aux (a :: l) n xs
    | _, _ => None
    end
  in aux [] i xs.

Fixpoint fpath (p : list nat) (F : flower) : option (fctx * garden) :=
  match p with
  | [] => Some (□, fg F)
  | i :: p => match F with
      | Γ ⊢ Π => match i with
          | 0 =>
              γΣ ← gpath p Γ;
              let '(γ, Σ) := γΣ in
              Some (Pistil γ Π, Σ)
          | _ =>
              lr ← split_at (i - 1) Π;
              let '(Π, Π') := lr in
              match Π' with
              | Δ :: Π' =>
                  γΣ ← gpath p Δ;
                  let '(γ, Σ) := γΣ in
                  Some (Petal Γ Π γ Π', Σ)
              | _ => None
              end
          end
      | _ => None
      end
  end
with gpath (p : list nat) (Γ : garden) : option (gctx * garden) :=
  match p with
  | [] => Some (Planter [] □ [], Γ)
  | i :: p => match Γ with
      | ⋅Fs =>
          lr ← split_at i Fs;
          let '(Fs, Gs) := lr in
          match Gs with
          | G :: Gs =>
              γΣ ← fpath p G;
              let '(γ, Σ) := γΣ in
              Some (Planter Fs γ Gs, Σ)
          | _ => None
          end
      end
  end.

Definition get_at (p : list nat) (Γ : garden) : option garden :=
  match gpath p Γ with
  | Some (_, Σ) => Some Σ
  | _ => None
  end.

Definition modify_at (p : list nat) (Δ : garden) (Γ : garden) : garden :=
  match gpath p Γ with
  | Some (γ, _) => γ ! Δ
  | None => Γ
  end.

Open Scope string_scope.
Compute λ F : flower, modify_at [1; 1; 0] (♯"a") (⋅[♯"a"; (⊢ [⋅[F]]); ♯"c"]).
Close Scope string_scope.

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

Lemma rtc_cstep_ctx γ Γ Δ :
  Γ ~>* Δ ->
  γ ! Γ ~>* γ ! Δ.
Proof.
  elim; clear Γ Δ.
  * move => Γ. reflexivity.
  * move => Γ Δ Σ.
    elim => γ' Γ' Δ' H1 H2 IH.
    apply (R_ctx (γ !∘ γ')) in H1.
    rewrite gcomp_gfill.
    eapply rtc_l; eauto.
    rewrite -gcomp_gfill.
    apply IH.
Qed.

(** * Basic proof search *)

Ltac sub_at p :=
  match goal with
  | |- ?Γ ~>* _ => eval cbn in (get_at p Γ)
  end.

Ltac rstep Δ :=
  apply (rtc_l cstep _ Δ).

Ltac rstepm p Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let Γ' := eval cbn in (modify_at p Δ Γ) in
      rstep Γ'; list_simplifier
  end.

Ltac rstepm_cons p i Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let γΣ := eval cbn in (gpath p Γ) in
      match γΣ with
      | Some (?γ, ⋅?Σ1 :: ?Σ2) =>
          match i with
          | 0 => rstepm p (⋅Δ ++ Σ2)
          | 1 => rstepm p (⋅Σ1 :: Δ)
          end
      end
  end.

Ltac rstepm_app p i Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let γΣ := eval cbn in (gpath p Γ) in
      match γΣ with
      | Some (?γ, ⋅?Σ1 ++ ?Σ2) =>
          match i with
          | 0 => rstepm p (⋅Δ ++ Σ2)
          | 1 => rstepm p (⋅Σ1 ++ Δ)
          end
      end
  end.

Ltac rtransm p Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let Γ' := eval cbn in (modify_at p Δ Γ) in
      transitivity Γ'; list_simplifier
  end.

Lemma fill_hole Γ :
  □ ! Γ = Γ.
Proof.
  case Γ => Fs /=. list_simplifier. reflexivity.
Qed.

Ltac rctx γ Γ Δ :=
  let H := fresh "H" in
  pose proof (H := R_ctx γ Γ Δ);
  repeat rewrite fill_hole/= in H; list_simplifier;
  apply H; clear H.

Ltac rctxm p :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      let spΓ := eval cbn in (gpath p Γ) in
      let spΔ := eval cbn in (gpath p Δ) in
      match spΓ with
      | Some (?γ, ?Γ0) =>
          match spΔ with
          | Some (_, ?Δ0) =>
              rctx γ Γ0 Δ0
          end
      end
  end.

Ltac rcstepm p Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let spΓ := eval cbn in (gpath p Γ) in
      match spΓ with
      | Some (?γ, ?Γ0) =>
          rstepm p Δ; [> rctx γ Γ0 Δ | ..]
      end
  end.

Ltac rctxm_cons p i :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      let spΓ := eval cbn in (gpath p Γ) in
      let spΔ := eval cbn in (gpath p Δ) in
      match spΓ with
      | Some (?γ, ⋅?Γ1 :: ?Γ2) =>
          match spΔ with
          | Some (_, ⋅?Δ1 ++ ?Δ2) =>
              match i with
              | 0 => 
                  let δ := eval cbn in (γ !∘ Planter [] □ Γ2) in
                  rctx δ (⋅[Γ1]) (⋅Δ1)
              | 1 => 
                  let δ := eval cbn in (γ !∘ Planter [Γ1] □ []) in
                  rctx δ (⋅Γ2) (⋅Δ2)
              end
          | Some (_, ⋅?Δ1 :: ?Δ2) =>
              match i with
              | 0 =>
                  let δ := eval cbn in (γ !∘ (Planter [] □ Γ2)) in
                  rctx δ (⋅[Γ1]) (⋅[Δ1])
              | 1 => 
                  let δ := eval cbn in (γ !∘ (Planter [Γ1] □ [])) in
                  rctx δ (⋅Γ2) (⋅Δ2)
              end
          end
      end
  end.

Ltac rctxm_app p i :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      let spΓ := eval cbn in (gpath p Γ) in
      let spΔ := eval cbn in (gpath p Δ) in
      match spΓ with
      | Some (?γ, ⋅?Γ1 ++ ?Γ2) =>
          match spΔ with
          | Some (_, ⋅?Δ1 ++ ?Δ2) =>
              match i with
              | 0 => 
                  let δ := eval cbn in (γ !∘ Planter [] □ Γ2) in
                  rctx δ (⋅Γ1) (⋅Δ1)
              | 1 => 
                  let δ := eval cbn in (γ !∘ Planter Γ1 □ []) in
                  rctx δ (⋅Γ2) (⋅Δ2)
              end
          | Some (_, ⋅?Δ1 :: ?Δ2) =>
              match i with
              | 0 =>
                  let δ := eval cbn in (γ !∘ (Planter [] □ Γ2)) in
                  rctx δ (⋅Γ1) (⋅[Δ1])
              | 1 => 
                  let δ := eval cbn in (γ !∘ (Planter Γ1 □ [])) in
                  rctx δ (⋅Γ2) (⋅Δ2)
              end
          end
      end
  end.

Ltac rctxmt p Δ0 :=
  match goal with
  | |- ?Γ ~>* ?Δ =>
      let spΓ := eval cbn in (gpath p Γ) in
      let spΔ := eval cbn in (gpath p Δ) in
      match spΓ with
      | Some (?γ, ?Γ0) =>
          let H := fresh "H" in
          pose proof (H := rtc_cstep_ctx γ Γ0 Δ0);
          repeat rewrite fill_hole/= in H; list_simplifier;
          apply H; clear H
      end
  end.

Ltac rctxmH p H :=
  match type of H with
  | _ ~>* ?Δ0 =>
      rtransm p Δ0; [> rctxmt p Δ0; exact H | ..]
  end.

Ltac rself :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      rctx □ Γ Δ
  end.

Ltac rwpol γ Γ :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_wpol γ Γ);
  pose proof (Hdel := R_co_wpol γ Γ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rwpolm p :=
  match goal with
  | |- ⋅?Γ ++ ?Δ ⇀ _ =>
      let spΔ := eval cbn in (gpath p (⋅Δ)) in
      match spΔ with
      | Some (?γ, _) =>
          rwpol γ (⋅Γ)
      end
  end.

Ltac rspol γ Γ Δ Π :=
  let Hins := fresh "Hins" in
  let Hdel := fresh "Hdel" in
  pose proof (Hins := R_spol γ Γ Δ Π);
  pose proof (Hdel := R_co_spol γ Γ Δ Π);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rspolm p :=
  match goal with
  | |- ?Γ ⇀ _ =>
      let spΓ := eval cbn in (gpath p Γ) in
      match spΓ with
      | Some (Planter [] (Petal ?Γ' [] ?γ ?Π') [], ?Δ) =>
          rspol γ Γ' ∅ Π'
      end
  end.

Ltac spol p :=
  match goal with
  | |- ⋅[?Γ ⊢ _] ~>* _ =>
      rstepm p Γ; [> rself; rspolm p | ..]
  end.

Ltac rrep :=
  match goal with
  | |- ⋅[⋅(∅ ⊢ ?Δs) :: ?Γ ⊢ ?Π] ⇀ _ =>
      let H := fresh "H" in
      pose proof (H := R_rep (⋅Γ) Δs Π);
      repeat rewrite fill_hole/= in H; list_simplifier;
      exact H; clear H
  end.

Ltac rpis :=
  apply R_pis.

Ltac rcopis :=
  apply R_co_pis.

Ltac rpism p :=
  match sub_at p with
  | Some (fg (⊢ [?Δ])) =>
      rcstepm p Δ; [> rpis | ..]
  end.

Ltac rcopism p :=
  match sub_at p with
  | Some ?Δ => 
      rcstepm p (⋅[⊢ [Δ]]); [> rcopis | ..]
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
  intros Γ Δ Hpis Π Π' Hpet.
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
  ⋅ [♯"a"; ♯"b"] ~>* ⋅ [♯"a"; ♯"b"; ♯"b"].
Proof.
  apply rtc_once.
  apply (R_ctx (Planter [♯"a"] □ []) ♯"b" (⋅[♯"b"; ♯"b"])).
  apply (R_wpol (Planter [] □ []) ♯"b").
Qed.