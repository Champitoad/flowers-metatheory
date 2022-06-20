Require Import String Setoid.
Require Import stdpp.list.
Require Import ssreflect.

Require Import Flowers.Utils.

(** Our semantics will be the sequent calculus LJ *)

(** * Formulas *)

Inductive form :=
| FAtom : name -> form
| FTrue : form
| FFalse : form
| FAnd : form -> form -> form
| FOr : form -> form -> form
| FImp : form -> form -> form.

Coercion FAtom : name >-> form.

Notation "# a" := (FAtom a) (format "# a", at level 1).
Notation "⊤" := FTrue.
Notation "⊥" := FFalse.
Infix "∧" := FAnd.
Infix "∨" := FOr.
Infix "⊃" := FImp (at level 85, right associativity).

Definition And :=
  foldr FAnd ⊤.

Definition Or :=
  foldr FOr ⊥.

Notation "⋀ As" := (And As) (at level 5).
Notation "⋁ As" := (Or As) (at level 5).

(** * Rules *)

Reserved Infix "⟹" (at level 90).

Inductive deriv : list form -> form -> Prop :=

(** ** Identity *)

| S_ax A Γ :
  A :: Γ ⟹ A

| S_cut A Γ Δ C :
  Γ ⟹ A -> A :: Δ ⟹ C ->
  Γ ++ Δ ⟹ C

(** ** Right rules *)

| S_R_true Γ :
  Γ ⟹ ⊤

| S_R_and A B Γ :
  Γ ⟹ A -> Γ ⟹ B ->
  Γ ⟹ A ∧ B

| S_R_or_l A B Γ :
  Γ ⟹ A ->
  Γ ⟹ A ∨ B

| S_R_or_r A B Γ :
  Γ ⟹ B ->
  Γ ⟹ A ∨ B

| S_R_imp A B Γ :
  A :: Γ ⟹ B ->
  Γ ⟹ A ⊃ B

(** ** Left rules *)

| S_L_true Γ C :
  Γ ⟹ C ->
  ⊤ :: Γ ⟹ C

| S_L_false Γ C :
  ⊥ :: Γ ⟹ C

| S_L_and A B Γ C :
  A :: B :: Γ ⟹ C ->
  (A ∧ B) :: Γ ⟹ C

| S_L_or A B Γ C :
  A :: Γ ⟹ C -> B :: Γ ⟹ C ->
  (A ∨ B) :: Γ ⟹ C

| S_L_imp A B Γ C :
  Γ ⟹ A -> B :: Γ ⟹ C ->
  (A ⊃ B) :: Γ ⟹ C

(** ** Permutation *)

| S_perm Γ Γ' C :
  Γ ≡ₚ Γ' ->
  Γ ⟹ C ->
  Γ' ⟹ C

where "Γ ⟹ C" := (deriv Γ C).

Ltac permute A :=
  match goal with
  | |- _ ⟹ _ => eapply (S_perm (A :: _) _ _); [> econs; try solve_Permutation | ..]
  end.

Ltac permuti i :=
  match goal with
  | |- ?Γ ⟹ _ =>
      let X := eval simpl in (nth i Γ ⊤) in
      permute X
  end.

(** * Basic proof search *)

Ltac passum :=
  match goal with
  | |- ?Γ ⟹ ?C =>
      let rec aux Δ n :=
        match Δ with
        | ?C :: ?Δ => apply S_ax
        | _ :: ?Δ =>
            let i := constr:(S n) in
            permuti i; aux Δ i
        end
      in 
      aux Γ 0
  end.

Ltac pintroL i :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval simpl in (nth i Γ ⊤) in
      let rule :=
        match X with
        | ⊤ => S_L_true
        | ⊥ => S_L_false
        | _ ∧ _ => S_L_and
        | _ ∨ _ => S_L_or
        end
      in permute X; apply rule
  end.

Ltac pimpL i :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval simpl in (nth i Γ ⊤) in
      let rule :=
        match X with
        | _ ⊃ _ => S_L_imp
        end
      in permute X; apply rule
  end.

Ltac pintroR :=
  match goal with
  | |- _ ⟹ ?C =>
      let rule :=
        match C with
        | ⊤ => S_R_true
        | _ ∧ _ => S_R_and
        | _ ⊃ _ => S_R_imp
        end
      in apply rule
  end.

Ltac isearch :=
  match goal with
  | |- ?Γ ⟹ _ =>
      done || passum ||
      tryif pintroR then isearch else
      let rec introΓ n :=
        match n with
        | 0 => idtac
        | S ?m => tryif pintroL m then isearch else introΓ m
        end
      in let n := eval compute in (length Γ) in
      introΓ n
  end.

Lemma weakening A Γ C :
  Γ ⟹ C ->
  A :: Γ ⟹ C.
Proof.
  elim.
  * move => B Γ'. isearch.
  * move: C => _ B Γ' Δ C Hr Hr' Hl Hl'.
    have Hl'' : B :: A :: Δ ⟹ C. { by permute A. }
    pose proof (H := S_cut B _ _ _ Hr Hl'').
    apply (S_perm (Γ' ++ A :: Δ)); auto. solve_Permutation.
  * move => Γ'. isearch.
  * move => D B Γ' *. isearch.
  * move => D B Γ' *. by apply S_R_or_l.
  * move => D B Γ' *. by apply S_R_or_r.
  * move => D B Γ' *. pintroR. by permute A.
  * move => D B Γ' *. by pintroL 1.
  * move => Γ' D. by pintroL 1.
  * move => D B Γ' E *. pintroL 1.
    apply (S_perm (A :: D :: B :: Γ')); auto. solve_Permutation.
  * move => D B Γ' E *. pintroL 1; by permuti 1.
  * move => D B Γ' E *. pimpL 1; auto. by permuti 1.
  * move => Δ Δ' D *. apply (S_perm (A :: Δ)); auto.
Qed.

Ltac pweak i :=
  permuti i; apply weakening.

Lemma contraction A Γ C :
  A :: A :: Γ ⟹ C ->
  A :: Γ ⟹ C.
Proof.
Admitted.

Lemma additive_cut : ∀ (A : form) (Γ : list form) (C : form),
  Γ ⟹ A → A :: Γ ⟹ C → Γ ⟹ C.
Admitted.

Ltac pcut A := apply (additive_cut A).

(** * Generalized rewriting of equiderivable formulas *)

Definition eqderiv (A B : form) : Prop :=
  ([A] ⟹ B) /\ ([B] ⟹ A).

Infix "⟺" := eqderiv (at level 95).

#[export] Instance equiv_eqderiv : Equivalence eqderiv.
Proof.
  econs; repeat red.
  * move => A. split; apply S_ax.
  * move => A B [HAB HBA]; done.
  * move => A B C [HAB HBA] [HBC HCB]. split.
    - apply (S_cut _ _ _ _ HAB HBC).
    - apply (S_cut _ _ _ _ HCB HBA).
Qed.

#[export] Instance : Equiv form := eqderiv.

Add Morphism FAnd with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_and.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isearch. by pweak 1. by pweak 0.
  * isearch. by pweak 1. by pweak 0. 
Qed.

Add Morphism FOr with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_or.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isearch.
    by apply S_R_or_l.
    by apply S_R_or_r.
  * isearch.
    by apply S_R_or_l.
    by apply S_R_or_r.
Qed.

Add Morphism FImp with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_imp.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isearch. pimpL 1. exact. by pweak 1.
  * isearch. pimpL 1. exact. by pweak 1.
Qed.

Add Morphism And with signature
  Forall2 eqderiv ==> eqderiv
  as proper_And.
Proof.
  elim => [|A As IHA] //=.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isearch.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isearch.
    - pweak 1. apply H.
    - pweak 0. by apply IHA.
    - pweak 1. apply H.
    - pweak 0. by apply IHA.
Qed.

Add Morphism Or with signature
  Forall2 eqderiv ==> eqderiv
  as proper_Or.
Proof.
  elim => [|A As IHA] //=.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isearch.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isearch.
    - apply S_R_or_l. apply H.
    - apply S_R_or_r. by apply IHA.
    - apply S_R_or_l. apply H.
    - apply S_R_or_r. by apply IHA.
Qed.

Add Parametric Morphism Γ C : (λ A, deriv (A :: Γ) C) with signature
  eqderiv ==> iff
  as proper_deriv_hyp.
Admitted.

Add Parametric Morphism : deriv with signature
  Forall2 eqderiv ==> eqderiv ==> iff
  as proper_deriv_concl.
Admitted.

Lemma eqderiv_Forall {A} (f g : A -> form):
  (∀ x, f x ⟺ g x) ->
  ∀ l, Forall (λ x, f x ⟺ g x) l.
Admitted.

Lemma eqderiv_map {A} (f g : A -> form) :
  (∀ x, f x ⟺ g x) ->
  ∀ l, Forall2 eqderiv (f <$> l) (g <$> l).
Admitted.

(** * Some useful tautologies *)

Lemma and_comm A B :
  A ∧ B ⟺ B ∧ A.
Proof.
  split; isearch.
Qed.

Lemma and_assoc A B C :
  A ∧ B ∧ C ⟺ (A ∧ B) ∧ C.
Proof.
  split; isearch.
Qed.

Lemma And_app Γ Δ :
  ⋀ (Γ ++ Δ) ⟺ ⋀ Γ ∧ ⋀ Δ.
Proof.
  rewrite /And foldr_app -/And.
  elim: Γ => [|A Γ IH] //=. split; isearch.
  rewrite IH. split; isearch.
Qed.