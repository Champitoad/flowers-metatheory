Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.
Open Scope string_scope.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.

Axiom TODO : forall A : Type, A.

(** * Translations *)

Notation "⋀ As" := (And As) (at level 5).
Notation "⋁ As" := (Or As) (at level 5).

Fixpoint flower_to_form (F : flower) : form :=
  match F with
  | □i => ⊤
  | ♯a => #a
  | Γ ⊢ Π => (garden_to_form Γ) ⊃ ⋁ (garden_to_form <$> Π)
  end
with garden_to_form (Γ : garden) : form :=
  ⋀ (flower_to_form <$> (gl Γ)).

Declare Scope flower_scope.
Delimit Scope flower_scope with flower.
Bind Scope flower_scope with flower.

Declare Scope garden_scope.
Delimit Scope garden_scope with garden.
Bind Scope garden_scope with garden.

Notation "⌊ F ⌋" := (flower_to_form F) (format "⌊ F ⌋") : flower_scope.
Notation "⌊ Γ ⌋" := (garden_to_form Γ) (format "⌊ Γ ⌋") : garden_scope.

Open Scope flower_scope.
Open Scope garden_scope.

(** * Soundness *)

Lemma true_unit A :
  A ∧ ⊤ ⟺ A.
Proof.
  split; isearch.
Qed.

Lemma interp_flower Γ Π :
  ⌊Γ ⊢ Π⌋ ⟺
  (⋀ (flower_to_form <$> (gl Γ)) ⊃ ⋁ (garden_to_form <$> Π)).
Proof.
  case: Γ => Fs. simpl. rewrite true_unit. reflexivity.
Qed.

Lemma iteration_imp_l A B C :
  A ∧ (B ⊃ C) ⟺ A ∧ (A ∧ B ⊃ C).
Proof.
  split; isearch.
  pimpL 1; isearch.
  pimpL 1; isearch.
Qed.

Lemma iteration_imp_r A B C :
  A ∧ (B ⊃ C) ⟺ A ∧ (B ⊃ A ∧ C).
Proof.
  split; isearch.
  pimpL 1; isearch.
  pimpL 1; isearch.
Qed.

Lemma iteration_And A : ∀ Γ,
  A ∧ ⋀ Γ ⟺ A ∧ ⋀ ((λ B, A ∧ B) <$> Γ).
Proof.
  elim => [|C Γ [IHl IHr]] //=.
  * split; isearch.
  * rewrite [A ∧ _]and_assoc [A ∧ _]and_comm -[_ ∧ ⋀ Γ]and_assoc.
    rewrite [A ∧ (C ∧ _) ∧ _]and_assoc [A ∧ C ∧ _]and_assoc -[((A ∧ C) ∧ _) ∧ _]and_assoc.
    split.
    - pintroR. isearch.
      pintroL 0. by pweak 0.
    - pintroR. pintroL 0. pintroL 0. pweak 0. passum.
      pintroL 0. by pweak 0.
Qed.

Lemma iteration_Or A : ∀ Γ,
  A ∧ ⋁ Γ ⟺ A ∧ ⋁ ((λ B, A ∧ B) <$> Γ).
Proof.
  elim => [|C Γ [IHl IHr]] //=; split; isearch.
  * apply S_R_or_l; isearch.
  * apply S_R_or_r.
    pcut (A ∧ ⋁ Γ). isearch.
    pcut (A ∧ ⋁ ((λ B : form, A ∧ B) <$> Γ)). pweak 1. by pweak 1.
    pintroL 0. cbv; passum.
  * apply S_R_or_l; isearch.
  * apply S_R_or_r.
    pcut (A ∧ ⋁ ((λ B : form, A ∧ B) <$> Γ)). cbv; isearch.
    pweak 1. pweak 1.
    pcut (A ∧ ⋁ Γ). assumption.
    pweak 1. isearch.
Qed.

Lemma wind_pollination (F : flower) i : ∀ (G : flower),
  ⌊F⌋ ∧ ⌊i ≔ F @ G⌋ ⟺ ⌊F⌋ ∧ ⌊G⌋.
Proof.
  elim/flower_induction => [j |a |Γ Π IHΓ IHΠ].
  - move =>/=. case (j =? i)%nat =>/=; split; isearch. 
  - move =>/=. split; isearch.
  - set fmf := @fmap list list_fmap flower form.
    set fmg := @fmap list list_fmap garden form.
    have H : ⌊F⌋ ∧
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
    rewrite interp_flower.
    rewrite interp_flower.
Admitted.

Lemma local_soundness : ∀ (Γ Δ : garden),
  Γ ~> Δ -> [⌊Δ⌋] ⟹ ⌊Γ⌋.
Proof.
  move => x y.
  elim; clear x y.

  (* Pollination *)

  * move => F G i.
    pose H := wind_pollination F i G.
    have Heq : (⌊F ∪ i ≔ F @ G⌋) ⟺ (⌊F⌋ ∧ ⌊i ≔ F @ G⌋). { admit. }
  
  (* Reproduction *)
  (* Decomposition *)
  (* Permutation *)
  (* Hole insertion *)
  (* Contextual closure *)

Admitted.

Theorem soundness : ∀ Γ Δ,
  Γ ~>* Δ -> [⌊Δ⌋] ⟹ ⌊Γ⌋.
Proof.
  move => x y.
  elim => [Γ |Γ Δ Σ Hstep H IH] //.
  clear x y.
  * apply S_ax.
  * apply local_soundness in Hstep.
    pose Hcut := (S_cut _ _ _ _ IH Hstep).
    done.
Qed.