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

Lemma wpol_flower (A : form) (f : flower -> form) (Γ : garden) (Π : list garden) :
  A ∧ (⋀ (fmf f Γ) ⊃ ⋁ (fmg (λ Δ, ⋀ (fmf f Δ)) Π)) ⟺
  A ∧ (⋀ (fmf (λ x, A ∧ f x) Γ) ⊃ ⋁ (fmg (λ Δ, ⋀ (fmf (λ x, A ∧ f x) Δ)) Π)).
Proof.
  rewrite wpol_imp_l wpol_imp_r wpol_And wpol_Or.
  rewrite /fmf/fmg -list_fmap_compose /compose.
  rewrite (eqderiv_map _ (λ Δ : garden, A ∧ ⋀ ((λ x : flower, A ∧ f x) <$> (gl Δ))) _ Π).
  { move => Δ. rewrite wpol_And -list_fmap_compose /compose. reflexivity. }
  rewrite -wpol_Or -wpol_imp_r -wpol_imp_l.
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

Lemma flowers_fill s : ∀ Γ,
  ⋀ (flowers_to_form (s @ Γ)) ⟺
  ⋀ (fmf (λ G, ⌊s @ G⌋) Γ).
Proof.
  case => Fs. elim: Fs => [|F Fs IH] //. split; simpl; isrch.
  rewrite fill_cons flowers_juxt /fmf fmap_cons -/fmf.
  rewrite cons_app And_app And_app IH.
  rewrite [⋀ [⌊s @ F⌋]]/foldr true_and.
  have H : ⌊s @ F⌋ ⟺ ⋀ (flowers_to_form (s @ F)).
  { simpl. list_simplifier. rewrite flower_flowers. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma interp_juxt Γ Δ :
  ⌊Γ ∪ Δ⌋ ⟺ ⌊Γ⌋ ∧ ⌊Δ⌋.
Proof.
  rewrite garden_flowers flowers_juxt And_app -garden_flowers -garden_flowers.
  reflexivity.
Qed.

Lemma wind_pollination (F : flower) i (G : flower) :
  ⌊F ∪ i ≔ F @ G⌋ ⟺ ⌊F ∪ G⌋.
Proof.
  rewrite interp_juxt interp_juxt.
  elim/flower_induction: G => [j |a |Γ Π IHΓ IHΠ].
  - move =>/=. case (j =? i)%nat =>/=; eqd. 
  - move =>/=. eqd.
  - have IH : ⌊F⌋ ∧
             (⋀ (fmf (λ G : flower, ⌊F⌋ ∧ ⌊i ≔ F @ G⌋) (gl Γ))
                ⊃ ⋁ (fmg (λ Δ, ⋀ (fmf (λ G, ⌊F⌋ ∧ ⌊i ≔ F @ G⌋) (gl Δ))) Π))
             ⟺
             ⌊F⌋ ∧
             (⋀ (fmf (λ G : flower, ⌊F⌋ ∧ ⌊G⌋) (gl Γ))
                ⊃ ⋁ (fmg (λ Δ, ⋀ (fmf (λ G, ⌊F⌋ ∧ ⌊G⌋) (gl Δ))) Π)).
    { unfold fmf, fmg.
      rewrite Forall_equiv_map in IHΓ. rewrite IHΓ.
      move: IHΠ.
      set P := (λ Δ : garden, Forall (λ H : flower, ⌊F⌋ ∧ ⌊i ≔ F @ H⌋ ⟺ ⌊F⌋ ∧ ⌊H⌋) Δ) => IHΠ.
      set Q := (λ Δ : garden, Forall2 eqderiv ((λ H : flower, ⌊F⌋ ∧ ⌊i ≔ F @ H⌋) <$> gl Δ) ((λ H : flower, ⌊F⌋ ∧ ⌊H⌋) <$> gl Δ)).
      apply equiv_Forall with (P := P) (Q := Q) in IHΠ.
      * unfold Q in IHΠ.
        rewrite Forall_equiv_map in IHΠ.
        apply (Forall2_Forall2_Proper And) in IHΠ.
        rewrite -list_fmap_compose in IHΠ.
        rewrite IHΠ.
        rewrite -[And <$> _]list_fmap_compose.
        reflexivity.
      * move => Δ; split; by apply Forall_equiv_map. }
    rewrite fill_flower. rewrite interp_flower_flowers.
    rewrite flowers_fill.
    rewrite /fmg -list_fmap_compose /compose.
    rewrite (eqderiv_map
              (λ Δ, ⋀ (flowers_to_form (i ≔ F @ Δ)))
              (λ Δ, ⋀ (fmf (λ G, ⌊i ≔ F @ G⌋) Δ))).
    { move => Δ. rewrite flowers_fill. reflexivity. }
    rewrite -/fmg. 
    rewrite interp_flower_flowers /flowers_to_form.
    rewrite (wpol_flower _ (λ G, ⌊G⌋)) wpol_flower.
    exact IH.
Qed.

Lemma split_petal Γ Δ₁ Δ₂ Π :
  ⌊Γ ⊢ Δ₁ ∪ Δ₂ :: Π⌋ ⟺ ⌊Γ ⊢ Δ₁ :: Π⌋ ∧ ⌊Γ ⊢ Δ₂ :: Π⌋.
Proof.
  repeat rewrite interp_flower_flowers -garden_flowers.
  repeat rewrite /fmg fmap_cons.
  repeat rewrite flowers_juxt And_app.
  repeat rewrite -garden_flowers.
  rewrite (cons_app (⌊Δ₁⌋ ∧ ⌊Δ₂⌋)) (cons_app ⌊Δ₁⌋) (cons_app ⌊Δ₂⌋).
  repeat rewrite Or_app Or_singl.
  by apply and_intro_r_msucc.
Qed.

Lemma self_pollination (F : flower) i (Γ Δ : garden) (Π : list garden) :
  ⌊F ∪ Γ ⊢ Δ :: Π⌋ ⟺ ⌊F ∪ Γ ⊢ i ≔ F @ Δ :: Π⌋.
Proof.
  elim/garden_induction: Δ.
  - move => j //=. list_simplifier.
    case (j =? i)%nat =>/=; eqd; elim Γ => Fs; apply S_R_or_l; isrch.
  - move => a //=. eqd.
  - move => Δ Π' H IH.
    repeat rewrite interp_flower_flowers flowers_juxt And_app.
    repeat rewrite -garden_flowers.
    repeat rewrite /fmg fmap_cons.
    rewrite cons_app; symmetry; rewrite cons_app; symmetry.
    repeat rewrite Or_app.
    repeat rewrite -garden_flowers Or_singl.
    rewrite [⌊F⌋ ∧ _]and_comm currying currying.
    rewrite [⌊F⌋ ⊃ _]spol_r [_ ⊃ ⌊_ @ _⌋ ∨ _]spol_r.
    repeat rewrite and_or_distr -interp_juxt.
    rewrite wind_pollination.
    by reflexivity.
  - eqd.
  - move => G Gs H IH.
    rewrite (cons_app G) fill_cons -/(juxt (⋅[G]) (⋅Gs)).
    rewrite split_petal.
    rewrite H IH.
    rewrite -split_petal.
    reflexivity.
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

  (* Hole insertion *)

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

Reserved Notation "⌈ A ⌉" (format "⌈ A ⌉", at level 10).

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

Lemma pollination :
  Γ ⟹ C ->
  ∀ X, 

Theorem completeness Γ C :
  Γ ⟹ C ->
  ⌈⋀ Γ⌉ ⊢ [⌈C⌉] ~>* ∅.
Proof.
Admitted.

End Completeness.