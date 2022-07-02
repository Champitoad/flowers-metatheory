Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.
Open Scope string_scope.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.

Declare Scope flower_scope.
Delimit Scope flower_scope with flower.
Bind Scope flower_scope with flower.

Declare Scope garden_scope.
Delimit Scope garden_scope with garden.
Bind Scope garden_scope with garden.

Open Scope flower_scope.
Open Scope garden_scope.

(** * Soundness *)

Section Soundness.

Fixpoint flower_to_form (F : flower) : form :=
  match F with
  | □i => ⊤
  | ♯a => #a
  | Γ ⊢ Π => (garden_to_form Γ) ⊃ ⋁ (garden_to_form <$> Π)
  end
with garden_to_form (Γ : garden) : form :=
  ⋀ (flower_to_form <$> (gl Γ)).

Definition fmf := @fmap list list_fmap flower form.
Definition fmg := @fmap list list_fmap garden form.

Definition flowers_to_form := fmf garden_to_form.
Definition gardens_to_form := fmg garden_to_form.

Notation "⌊ F ⌋" := (flower_to_form F) (format "⌊ F ⌋") : flower_scope.
Notation "⌊ Γ ⌋" := (garden_to_form Γ) (format "⌊ Γ ⌋") : garden_scope.

Lemma flower_garden F :
  ⌊F⌋%flower ⟺ ⌊F⌋%garden.
Proof.
  simpl. rewrite true_and. reflexivity.
Qed.

Lemma flower_flowers Fs :
  Forall2 eqderiv (flower_to_form <$> Fs) (flowers_to_form Fs).
Proof.
  apply Forall_equiv_map. apply eqderiv_Forall.
  move => F. rewrite flower_garden. reflexivity.
Qed.

Lemma garden_gardens Π :
  Forall2 eqderiv (garden_to_form <$> Π) (gardens_to_form Π).
Proof.
  apply Forall_equiv_map. apply eqderiv_Forall.
  move => Δ. reflexivity.
Qed.

Lemma gardens_flowers : ∀ (Π : list garden),
  Forall2 eqderiv
  (gardens_to_form Π)
  (fmg (λ Δ, ⋀ (flowers_to_form Δ)) Π).
Proof.
  elim => [|Γ Π IH] //=.
  econs. case Γ => [Fs] //=.
  rewrite flower_flowers.
  reflexivity.
Qed.

Lemma garden_flowers Γ : 
  ⌊Γ⌋ ⟺ ⋀ (flowers_to_form Γ).
Proof.
  rewrite -flower_flowers.
  case Γ => *; reflexivity.
Qed.

Lemma interp_flower Γ Π :
  ⌊Γ ⊢ Π⌋ ⟺
  (⌊Γ⌋ ⊃ ⋁ (gardens_to_form Π)).
Proof.
  case: Γ => Fs //=.
  rewrite true_and. reflexivity.
Qed.

Lemma interp_flower_flowers Γ Π :
  ⌊Γ ⊢ Π⌋ ⟺
  (⋀ (flowers_to_form Γ) ⊃ ⋁ (fmg (λ Δ, ⋀ (flowers_to_form Δ)) Π)).
Proof.
  rewrite interp_flower garden_flowers gardens_flowers.
  reflexivity.
Qed.

Lemma fill_flower s Γ Π :
  s @ (Γ ⊢ Π) = s @ Γ ⊢ (λ Δ, s @ Δ) <$> Π.
Proof.
  reflexivity.
Qed.

Lemma fill_cons s F Fs :
  s @ (⋅F :: Fs) = s @ F ∪ s @ ⋅Fs.
Proof.
  simpl. list_simplifier. reflexivity.
Qed.

Lemma flowers_juxt Γ Δ :
  (flowers_to_form (Γ ∪ Δ)) =
  (flowers_to_form Γ ++ flowers_to_form Δ)%list.
Proof.
  elim: Γ Δ => [Fs] [Gs].
  rewrite /juxt//=/flowers_to_form/fmf fmap_app. reflexivity.
Qed.

Lemma interp_juxt Γ Δ :
  ⌊Γ ∪ Δ⌋ ⟺ ⌊Γ⌋ ∧ ⌊Δ⌋.
Proof.
  rewrite garden_flowers flowers_juxt And_app -garden_flowers -garden_flowers.
  reflexivity.
Qed.

Lemma interp_cons F Fs :
  ⌊⋅F :: Fs⌋ ⟺ ⌊F⌋ ∧ ⌊⋅Fs⌋.
Proof.
  rewrite /=; eqd.
Qed. 

Lemma wind_pollination i (Σ Δ : garden) :
  ⌊Σ ∪ i ≔ Σ @ Δ⌋ ⟺ ⌊Σ ∪ Δ⌋.
Proof.
  rewrite interp_juxt interp_juxt.
  elim/garden_induction: Δ => [j |a |Γ Π IHΓ IHΠ ||F Fs IHF IHFs].
  - rewrite /=/unisubst; list_simplifier.
    case Σ => Fs. case (j =? i)%nat; eqd. 
  - rewrite /=; eqd.
  - rewrite fill_flower interp_flower.
    rewrite wpol_imp_l wpol_imp_r wpol_Or.
    rewrite -list_fmap_compose /compose.
    rewrite Forall_equiv_map in IHΠ.
    rewrite IHΓ IHΠ.
    rewrite -wpol_Or -wpol_imp_r -wpol_imp_l.
    rewrite -interp_flower.
    by reflexivity.
  - rewrite /=; eqd.
  - rewrite fill_cons interp_juxt.
    have H : ∀ A B C, A ∧ B ∧ C ⟺ (A ∧ B) ∧ (A ∧ C).
    { eqd. pweak 0. pweak 0. isrch. }
    rewrite H IHF IHFs.
    rewrite -H. rewrite interp_cons.
    by reflexivity.
Qed.

Lemma self_pollination i (Σ Γ Δ : garden) (Π : list garden) :
  ⌊Σ ∪ Γ ⊢ Δ :: Π⌋ ⟺ ⌊Σ ∪ Γ ⊢ i ≔ Σ @ Δ :: Π⌋.
Proof.
  rewrite interp_flower interp_juxt and_comm currying.
  rewrite /gardens_to_form/fmg fmap_cons.
  rewrite cons_app Or_app Or_singl.
  rewrite (spol_r ⌊Σ⌋) and_or_distr.

  rewrite -interp_juxt -(wind_pollination i Σ) interp_juxt.

  rewrite -and_or_distr -spol_r.
  rewrite -[⌊_ @ Δ⌋]Or_singl -Or_app -cons_app.
  rewrite -fmap_cons -/fmg -/gardens_to_form.
  rewrite -currying -and_comm -interp_juxt -interp_flower.

  by reflexivity.
Qed.

Lemma reproduction Δs Γ Π :
  ⌊Γ ⊢ [⋅(λ Δ, Δ ⊢ Π) <$> Δs]⌋ ⟺ ⌊(⊢ Δs) ∪ Γ ⊢ Π⌋.
Proof.
  rewrite interp_flower_flowers -garden_flowers.
  rewrite [fmg _ _]/= Or_singl.
  rewrite /flowers_to_form /fmf -list_fmap_compose /compose.
  rewrite (eqderiv_map (λ Δ, ⌊Δ ⊢ Π⌋) (λ Δ, ⌊Δ⌋ ⊃ ⋁ (gardens_to_form Π))).
  { intros. simpl. rewrite true_and. reflexivity. }

  rewrite interp_flower_flowers -garden_flowers.
  rewrite interp_juxt interp_flower_flowers -garden_flowers.
  rewrite [⌊∅⌋]/= true_imp_l.
  pose proof (H := garden_flowers). symmetry in H.
  repeat rewrite /fmg (eqderiv_map (λ Δ : garden, ⋀ (flowers_to_form Δ)) garden_to_form); auto.

  rewrite and_comm.
  apply or_intro_l_nary.
Qed.

Lemma permutation_garden Fs Fs' :
  Fs ≡ₚ Fs' ->
  ⌊⋅Fs⌋ ⟺ ⌊⋅Fs'⌋.
Proof.
  elim; clear Fs Fs'.
  * reflexivity.
  * move => F Fs Fs' Hperm IH.
    rewrite (cons_app _ Fs') (cons_app _ Fs).
    repeat rewrite -/(juxt (⋅[F]) (⋅Fs)) -/(juxt (⋅[F]) (⋅Fs')) interp_juxt.
    rewrite IH. reflexivity.
  * move => F G Fs. simpl. rewrite and_comm. eqd.
  * move => Fs1 Fs2 Fs3 Hperm1 H1 Hperm2 H2.
    rewrite H1 H2. reflexivity.
Qed.

Lemma permutation_flower (Π Π' : list garden) (Γ : garden) :
  Π ≡ₚ Π' ->
  ⌊Γ ⊢ Π⌋ ⟺ ⌊Γ ⊢ Π'⌋.
Proof.
  elim; clear Π Π'.
  * reflexivity.
  * move => Δ Fs Fs' Hperm IH.
    simpl in *.
    repeat rewrite true_and in IH.
    repeat rewrite true_and.
    by apply proper_concl.
  * move => Δ Σ Π. simpl.
    repeat rewrite true_and.
    rewrite or_assoc [⌊Σ⌋ ∨ _]or_comm -or_assoc.
    reflexivity.
  * move => Π1 Π2 Π3 Hperm1 H1 Hperm2 H2.
    rewrite H1 H2. reflexivity.
Qed.

Lemma local_soundness : ∀ (Γ Δ : garden),
  Γ ⇀ Δ -> ⌊Γ⌋ ⟺ ⌊Δ⌋.
Proof.
  move => x y.
  elim; clear x y; intros.

  (* Pollination *)

  * symmetry. by apply wind_pollination.
  * by apply wind_pollination.
  * by apply self_pollination.
  * symmetry. by apply self_pollination.

  (* Reproduction *)

  * symmetry. by apply reproduction.

  (* Decomposition *)

  * rewrite //=; eqd. pimpL 0; isrch. pleft.
  * rewrite //=; eqd. pleft.

  (* Permutation *)

  * by apply permutation_garden.
  * by apply permutation_flower.

  (* Holes *)

  * rewrite //=; eqd.
  * rewrite //=; eqd.
Qed.

Lemma grounding : ∀ X Γ Δ i,
  ⌊Γ⌋ ⟺ ⌊Δ⌋ ->
  ⌊i ≔ Γ @ X⌋ ⟺ ⌊i ≔ Δ @ X⌋.
Proof.
  elim/garden_induction.
  * move => j Γ Δ i. case Γ => Fs; case Δ => Gs. move => H.
    rewrite //=. case (Nat.eqb j i); list_simplifier; auto. reflexivity.
  * move => a Γ Δ i H. rewrite //=; reflexivity.
  * move => Γ Π IHΓ IHΠ Σ Δ i H.
    specialize (IHΓ Σ Δ i H).
    repeat rewrite fill_flower interp_flower.
    rewrite IHΓ.
    elim: IHΠ => [|Δ' Π' HΔ' HΠ' IH]; [> reflexivity | ..].
    repeat rewrite fmap_cons gardens_flowers /fmg fmap_cons cons_app Or_app Or_singl.
    repeat rewrite -garden_flowers. rewrite (HΔ' _ _ _ H).
    rewrite gardens_flowers /fmg in IH.
    rewrite (proper_concl ⌊i ≔ Δ @ Δ'⌋).
    apply IH.
    rewrite gardens_flowers /fmg.
    reflexivity.
  * intros; eqd.
  * move => F Fs HF HFs Γ Δ i H.
    rewrite fill_cons fill_cons. repeat rewrite interp_juxt.
    rewrite (HF _ _ _ H) (HFs _ _ _ H).
    reflexivity.
Qed.

Theorem soundness : ∀ Γ Δ,
  Γ ~>* Δ -> ⌊Γ⌋ ⟺ ⌊Δ⌋.
Proof.
  move => x y.
  elim => [Γ |Γ Δ Σ Hstep H IH] //.
  clear x y.
  * reflexivity.
  * rewrite -IH. elim: Hstep => Γ' Δ' X i H'.
    apply grounding. by apply local_soundness.
Qed.

End Soundness.

(** * Completeness *)

Section Completeness.

Reserved Notation "⌈ A ⌉" (format "⌈ A ⌉", at level 0).

Fixpoint interp (A : form) : garden :=
  match A with
  | #a => ♯a
  | ⊤ => ∅
  | ⊥ => ∅ ⊢
  | A ∧ B => ⌈A⌉ ∪ ⌈B⌉
  | A ∨ B => ⊢ [⌈A⌉; ⌈B⌉]
  | A ⊃ B => ⌈A⌉ ⊢ [⌈B⌉]
  end

where "⌈ A ⌉" := (interp A).

Notation "⌈[ Γ ]⌉" := (interp <$> Γ).

Reserved Notation "F ⋲ Γ" (at level 70).

Inductive occurs (F : flower) : garden -> Prop :=

| occ_in (Γ : garden) :
  In F Γ ->
  F ⋲ Γ

| occ_pistil Γ Π :
  F ⋲ Γ ->
  F ⋲ (Γ ⊢ Π)

| occ_petal Γ Δ Π :
  F ⋲ Δ -> In Δ Π ->
  F ⋲ (Γ ⊢ Π)

| occ_garden (G : flower) (Γ : garden) :
  F ⋲ G -> In G Γ ->
  F ⋲ Γ

where "F ⋲ Γ" := (occurs F Γ).

Reserved Notation "Δ ∈ X ! i" (at level 70).

Inductive irrigates (Δ : garden) (i : nat) : garden -> Prop :=

| irr_vacuous X :
  ~ (□i ⋲ X) ->
  Δ ∈ X ! i

| irr_wpol (Γ : garden) :
  Forall (λ F, In F Γ) Δ ->
  Δ ∈ Γ ! i

| irr_spol (Γ : garden) Π :
  Forall (λ F, In F Γ) Δ ->
  Δ ∈ (Γ ⊢ Π) ! i

| irr_flower Γ Π :
  Δ ∈ Γ ! i -> Forall (λ Σ, Δ ∈ Σ ! i) Π ->
  Δ ∈ (Γ ⊢ Π) ! i 

| irr_garden (Γ : garden) :
  Forall (λ F : flower, Δ ∈ F ! i) Γ ->
  Δ ∈ Γ ! i

where "Δ ∈ X ! i" := (irrigates Δ i X).

Definition firrigates (Γ : list form) (i : nat) (X : garden) : Prop :=
  Forall (λ A, ⌈A⌉ ∈ X ! i) Γ.

Notation "Γ ⊆ X ! i" := (firrigates Γ i X) (at level 70).

Lemma not_occurs_neq i j :
  ¬ □i ⋲ □j -> Nat.eqb i j = false.
Proof.
  move => H. apply Nat.eqb_neq. move => Hij.
  have HIn : In □i □j. { econs. }
  apply H. econs.
Qed.

Lemma pollination Γ C :
  Γ ⟹ C -> ∀ X i, Γ ⊆ X ! i ->
  X <~> (i ≔ ⌈C⌉) @ X.
Proof.  
  elim; clear Γ C.
  * move => A Γ X i H. inv H. clear H3; move: X H2.
    elim/garden_induction.
    - case ⌈A⌉ => Fs j H.
      inv H.
      + apply not_occurs_neq in H0. rewrite Nat.eqb_sym in H0.
        rewrite /fill/=. list_simplifier.
        rewrite H0. split; by reflexivity.
      + inv H0. have H' : Fs = []. { auto. }
        rewrite H'. rewrite /fill//=; list_simplifier. case (Nat.eqb j i).
        split.
        apply rtc_once; apply (R_ctx □0 □j ∅ 0); apply R_hole_del.
        apply rtc_once; apply (R_ctx □0 ∅ □j 0); apply R_hole_ins.
        split; reflexivity.
Admitted.

Theorem completeness Γ C :
  Γ ⟹ C ->
  ⌈⋀ Γ⌉ ⊢ [⌈C⌉] ~>* ∅.
Proof.
  elim; clear Γ C; intros; simpl.
  * admit.
Admitted.

End Completeness.