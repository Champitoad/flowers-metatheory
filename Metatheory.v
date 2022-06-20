Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.
Open Scope string_scope.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.

Axiom TODO : forall A : Type, A.

(** * Translations *)

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

Lemma flower_garden F :
  ⌊F⌋%flower ⟺ ⌊F⌋%garden.
Proof.
  simpl. rewrite true_unit. reflexivity.
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

Lemma interp_flower_flowers Γ Π :
  ⌊Γ ⊢ Π⌋ ⟺
  (⋀ (flowers_to_form Γ) ⊃ ⋁ (fmg (λ Δ, ⋀ (flowers_to_form Δ)) Π)).
Proof.
  case: Γ => Fs //=.
  rewrite flower_flowers garden_gardens gardens_flowers.
  rewrite true_unit. reflexivity.
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

Lemma iteration_Or {T} A (f : T -> form) : ∀ Γ,
  A ∧ ⋁ (f <$> Γ) ⟺ A ∧ ⋁ ((λ B, A ∧ f B) <$> Γ).
Proof.
  elim => [|C Γ [IHl IHr]]; split; list_simplifier; isearch.
  * apply S_R_or_l; isearch.
  * apply S_R_or_r.
    pcut (A ∧ ⋁ (f <$> Γ)). isearch.
    pcut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)). pweak 1. by pweak 1.
    pintroL 0. cbv; passum.
  * apply S_R_or_l; isearch.
  * apply S_R_or_r.
    pcut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)). cbv; isearch.
    pweak 1. pweak 1.
    pcut (A ∧ ⋁ (f <$> Γ)). assumption.
    pweak 1. isearch.
Qed.

Lemma iteration_wind_flower (A : form) (f : flower -> form) (Γ : garden) (Π : list garden) :
  A ∧ (⋀ (fmf f Γ) ⊃ ⋁ (fmg (λ Δ, ⋀ (fmf f Δ)) Π)) ⟺
  A ∧ (⋀ (fmf (λ x, A ∧ f x) Γ) ⊃ ⋁ (fmg (λ Δ, ⋀ (fmf (λ x, A ∧ f x) Δ)) Π)).
Proof.
  rewrite iteration_imp_l iteration_imp_r iteration_And iteration_Or.
  rewrite /fmf/fmg -list_fmap_compose /compose.
  rewrite (eqderiv_map _ (λ Δ : garden, A ∧ ⋀ ((λ x : flower, A ∧ f x) <$> (gl Δ))) _ Π).
  { move => Δ. rewrite iteration_And -list_fmap_compose /compose. reflexivity. }
  rewrite -iteration_Or -iteration_imp_r -iteration_imp_l.
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
  case => Fs. elim: Fs => [|F Fs IH] //. split; simpl; isearch.
  rewrite fill_cons flowers_juxt /fmf fmap_cons -/fmf.
  rewrite cons_app And_app And_app IH.
  rewrite [⋀ [⌊s @ F⌋]]/foldr true_unit.
  have H : ⌊s @ F⌋ ⟺ ⋀ (flowers_to_form (s @ F)).
  { simpl. list_simplifier. rewrite flower_flowers. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma wind_pollination (F : flower) i : ∀ (G : flower),
  ⌊F⌋ ∧ ⌊i ≔ F @ G⌋ ⟺ ⌊F⌋ ∧ ⌊G⌋.
Proof.
  elim/flower_induction => [j |a |Γ Π IHΓ IHΠ].
  - move =>/=. case (j =? i)%nat =>/=; split; isearch. 
  - move =>/=. split; isearch.
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
    rewrite (iteration_wind_flower _ (λ G, ⌊G⌋)) iteration_wind_flower.
    exact IH.
Qed.

Lemma interp_juxt Γ Δ :
  ⌊Γ ∪ Δ⌋ ⟺ ⌊Γ⌋ ∧ ⌊Δ⌋.
Proof.
  rewrite garden_flowers flowers_juxt And_app -garden_flowers -garden_flowers.
  reflexivity.
Qed.

Lemma local_soundness : ∀ (Γ Δ : garden),
  Γ ~> Δ -> [⌊Δ⌋] ⟹ ⌊Γ⌋.
Proof.
  move => x y.
  elim; clear x y.

  (* Pollination *)

  * move => F G i. rewrite interp_juxt interp_juxt. by apply wind_pollination.
  * move => F G i. rewrite interp_juxt interp_juxt. by apply wind_pollination.

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
    pcut ⌊Δ⌋; auto. by pweak 1.
Qed.