Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String PeanoNat.
Open Scope string_scope.

Require Import Flowers.Utils.

(** Names *)

Definition name : Type := string.
Definition string_to_name : string -> name := fun x => x.
Coercion string_to_name : string >-> name.

(** Flowers *)

Inductive flower :=
| Hole : nat -> flower
| Atom : name -> flower
| Flower : garden -> list garden -> flower
with garden :=
| Garden : list flower -> garden.

Definition fg : flower -> garden := fun f => Garden [f].
Coercion fg : flower >-> garden.

Notation "□ i" := (Hole i) (format "□ i", at level 1).
Notation "♯ a" := (Atom a) (format "♯ a", at level 1).

Notation "Γ ⊢ Π" := (Flower Γ Π) (at level 65).
Notation "Γ ⊢" := (Flower Γ nil) (at level 65).
Notation "⊢ Π" := (Flower (Garden nil) Π) (at level 65).

Notation "· Fs" := (Garden Fs) (at level 63).
Notation "∅" := (Garden nil).

(** * Induction principles *)

Definition lift_flower_pred	(P : flower -> Prop) : garden -> Prop :=
  fun '(· Fs) => Forall P Fs.

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pi : nat -> Prop) (Pa : name -> Prop),
  let PΓ : garden -> Prop := lift_flower_pred P in
  (∀ (i : nat), Pi i) ->
  (∀ (a : name), Pa a) ->
  (∀ (i : nat), Pi i -> P □i) ->
  (∀ (a : name), Pa a -> P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    PΓ Γ -> Forall PΓ Π -> P (Γ ⊢ Π)) ->
  (∀ (Fs : list flower),
    Forall P Fs -> PΓ (· Fs)) ->
  ∀ (f : flower), P f.
Proof.
  move => P Pi Pa PΓ Hi Ha IHi IHa IHF IHΓ.
  fix IH 1.
  elim => [i |a |Γ Π].
  * apply IHi. by apply Hi.
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
  (∀ (i : nat), Pi i) ->
  (∀ (a : name), Pa a) ->
  (∀ (i : nat), Pi i -> P □i) ->
  (∀ (a : name), Pa a -> P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    P Γ -> Forall P Π -> P (Γ ⊢ Π)) ->
  P ∅ ->
  (∀ (F : flower) (Fs : list flower),
    P F -> P (· Fs) -> P (· F :: Fs)) ->
  ∀ (Γ : garden), P Γ.
Proof.
  move => P Pi Pa Hi Ha IHi IHa IHF IHnil IHcons.
  fix IH 1.
  case => Fs.
  elim: Fs => [|F Fs IHFs].
  by apply: IHnil.
  apply: IHcons.
  - elim: F => [i |a |Γ Π].
    + apply IHi. by apply Hi.
    + apply IHa. by apply Ha.
    + apply IHF.
        exact: IH.
        decompose_Forall.
  - exact: IHFs.
Qed.

Definition flower_induction	:
  ∀ (P : flower -> Prop),
  let PΓ : garden -> Prop := lift_flower_pred P in
  (∀ (i : nat), P □i) ->
  (∀ (a : name), P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    PΓ Γ -> Forall PΓ Π -> P (Γ ⊢ Π)) ->
  ∀ (F : flower), P F.
Proof.
  move => P PΓ IHi IHa IHΓ.
  eapply flower_induction_full; eauto.
  Unshelve.
  3: { exact (fun _ => True). }
  3: { exact (fun _ => True). }
  all: done.
Qed.

Definition garden_induction	:
  ∀ (P : garden -> Prop),
  (∀ (i : nat), P □i) ->
  (∀ (a : name), P ♯a) ->
  (∀ (Γ : garden) (Π : list garden),
    P Γ -> Forall P Π -> P (Γ ⊢ Π)) ->
  P ∅ ->
  (∀ (F : flower) (Fs : list flower),
    P F -> P (· Fs) -> P (· F :: Fs)) ->
  ∀ (Γ : garden), P Γ.
Proof.
  move => P IHi IHa IHF IHnil IHcons.
  eapply garden_induction_full; eauto.
  Unshelve.
  3: { exact (fun _ => True). }
  3: { exact (fun _ => True). }
  all: done.
Qed.

(** * Contexts *)

Definition subst := nat -> list flower.

Fixpoint ffill (s : subst) (F : flower) : list flower :=
  match F with
  | □i => s i
  | ♯_ => [F]
  | Γ ⊢ Π => [· gfill s Γ ⊢ (fun Δ => · gfill s Δ) <$> Π]
  end
with gfill (s : subst) (Γ : garden) : list flower :=
  match Γ with
  | · Fs => F ← Fs; ffill s F
  end.

Definition fill (s : subst) (Γ : garden) : garden :=
  · gfill s Γ.

Notation "s 'in' Γ" := (fill s Γ) (at level 30).

Definition id_subst	: subst := fun i => [□i].

Definition comp_subst (s1 : subst) (s2 : subst) : subst :=
  fun i => F ← ffill s2 □i; ffill s1 F.

Infix "∘" := comp_subst.

Fixpoint build_subst (l : list (nat * list flower)) : subst :=
  match l with
  | [] => id_subst
  | (j, Fs) :: l => fun i => if (i =? j)%nat then Fs else (build_subst l) i
  end.

Notation "{| l |}" := (build_subst l).

Definition unisubst (i : nat) '(Garden Fs) : subst :=
  build_subst [(i, Fs)].

Notation "i ≔ Θ" := (unisubst i Θ) (at level 10).

Compute 0 ≔ ♯"a" in · [□0; □1].
Compute {|[ (1, [♯"a"]) ; (0, [♯"b"]) ]|} in · [□0; □1].

Lemma fill_id_subst : ∀ Γ,
  id_subst in Γ = Γ.
Proof.
  unfold fill.
  elim/garden_induction => [i |a |Γ Π IHΓ IHΠ | |F Fs H IH] //=.
  - apply Forall_eq_map in IHΠ.
    by rewrite IHΓ IHΠ map_id_ext.
  - simpl in *. list_simplifier. injection H. move => H'. rewrite H'.
    list_simplifier. rewrite IH. done.
Qed.

Lemma fill_comp_subst : ∀ Γ s1 s2,
  (s2 ∘ s1) in Γ = s2 in (s1 in Γ).
Proof.
  move => Γ s1 s2.
  rewrite /fill/comp_subst//=.
  elim/garden_induction: Γ => [i |a |Γ Π IHΓ IHΠ | |F Fs IHF IHFs] //.
  all: list_simplifier; auto.
  * rewrite IHΓ.
    rewrite Forall_eq_map in IHΠ.
    rewrite IHΠ.
    set Γ' := · gfill s2 (· gfill s1 Γ).
    rewrite -list_fmap_compose.
    set u := ((Garden ∘ (gfill s2)) ∘ (Garden ∘ (gfill s1)))%stdpp.
    set u' := fun x => Garden (gfill s2 (Garden (gfill s1 x))).
    have H : u = u'; done.
  * by rewrite IHF IHFs bind_app.
Qed.

Definition sub Γ Δ :=
  exists s, s in Γ = Δ.

Local Instance sub_po: PreOrder sub.
Proof.
  econs.
  * repeat red. move => Γ.
    exists id_subst.
    by apply fill_id_subst.
  * repeat red. move => Γ Δ Σ [s1 H1] [s2 H2].
    exists (s2 ∘ s1).
    rewrite -H1 in H2.
    rewrite -H2.
    by apply fill_comp_subst.
Qed.

(** * Rules *)

Definition juxt '(· Fs) '(· Fs') :=
  Garden (Fs ++ Fs').

Infix "∪" := juxt.

Reserved Infix "~>" (at level 80).

Inductive step : garden -> garden -> Prop :=

(** ** Pollination *)

| R_wpol (F G : flower) (i : nat) :
  · [F; G] ~>
  F ∪ i ≔ F in G

| R_co_wpol (F G : flower) (i : nat) :
  F ∪ i ≔ F in G ~>
  · [F; G]

| R_spol (F : flower) (Γ Δ : garden) (Π : list garden) (i : nat) :
  F ∪ Γ ⊢ Δ :: Π ~>
  F ∪ Γ ⊢ i ≔ F in Δ :: Π

| R_co_spol (F : flower) (Γ Δ : garden) (Π : list garden) (i : nat) :
  F ∪ Γ ⊢ i ≔ F in Δ :: Π ~>
  F ∪ Γ ⊢ Δ :: Π

(** ** Reproduction *)

| R_rep (Γ : garden) (Δs Π : list garden) :
  (⊢ Δs) ∪ Γ ⊢ Π ~>
  Γ ⊢ (fun Δ => · [Δ ⊢ Π]) <$> Δs

(** ** Decomposition *)

| R_pis	(Δ : garden) :
  ⊢ [Δ] ~> Δ

| R_pet	(Γ : garden) (Π : list garden) :
  Γ ⊢ ∅ :: Π ~> ∅

(** ** Permutation *)

| R_perm_g (Fs Fs' : list flower) :
  Fs ≡ₚ Fs' ->
  · Fs ~> · Fs'

| R_perm_f (Π Π' : list garden) (Γ : garden) :
  Π ≡ₚ Π' ->
  Γ ⊢ Π ~> Γ ⊢ Π'

(** ** Hole insertion *)

| R_hole (i : nat) :
  ∅ ~> □i

(** ** Contextual closure *)

| R_ctx (Γ Δ X : garden) (i : nat) :
  Γ ~> Δ ->
  i ≔ Γ in X ~> i ≔ Δ in X

where "Γ ~> Δ" := (step Γ Δ).

Infix "~>*" := (rtc step) (at level 80).

Example deriv_contraction :
  · [♯"a"; ♯"b"] ~>* · [♯"a"; ♯"b"; ♯"b"].
Proof.
  transitivity (· [♯"a"; ♯"b"; □0]).
  * apply rtc_once.
    refine (R_ctx ∅ □0 (·[♯"a"; ♯"b"; □1]) 1 _).
    refine (R_hole 0).
  * apply rtc_once.
    refine (R_ctx (·[♯"b"; □0]) (·[♯"b"; ♯"b"]) (·[♯"a"; □0]) 0 _).
    refine (R_wpol _ _ 0).
Qed.