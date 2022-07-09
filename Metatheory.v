Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.
Close Scope string_scope.

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

Lemma ffill_gfill Γ ϕ :
  ffill Γ ϕ = gfill Γ ϕ.
Proof.
  rewrite /=. case (ffill Γ ϕ) => Fs. list_simplifier. reflexivity.
Qed.

Lemma wind_pollination γ Γ :
  ⌊Γ ∪ γ ! Γ⌋ ⟺ ⌊Γ ∪ γ ! ∅⌋.
Proof.
  rewrite interp_juxt interp_juxt.
  elim/gctx_induction: γ => [|γ IH Π |γ IH Δ Π Π' |ϕ IH Fs Gs].
  - rewrite /=. list_simplifier. rewrite flower_flowers -garden_flowers. eqd.
  - rewrite /= true_and true_and.
    rewrite wpol_imp_l IH -wpol_imp_l.
    reflexivity.
  - rewrite /= true_and true_and.
    rewrite wpol_imp_r wpol_Or fmap_app fmap_cons IH
            -fmap_cons -fmap_app -wpol_Or -wpol_imp_r.
    reflexivity.
  - rewrite /=.
    rewrite [_ <$> Fs ++ _]fmap_app [_ <$> ffill Γ ϕ ++ _]fmap_app.
    rewrite And_app And_app.
    rewrite [_ <$> gl _]flower_flowers -garden_flowers.
    rewrite and_assoc [⌊Γ⌋ ∧ _]and_comm -and_assoc [⌊Γ⌋ ∧ _]and_assoc.
    rewrite ffill_gfill IH -ffill_gfill.
    rewrite -and_assoc and_assoc -[_ ∧ ⌊Γ⌋]and_comm -and_assoc.
    rewrite [⌊ffill _ _⌋]garden_flowers -flower_flowers.
    rewrite -And_app -And_app.
    rewrite -fmap_app -fmap_app.
    reflexivity.
Qed.

Lemma self_pollination (γ : gctx) (Γ Δ : garden) (Π : list garden) :
  ⌊Γ ∪ Δ ⊢ γ ! ∅ :: Π⌋ ⟺ ⌊Γ ∪ Δ ⊢ γ ! Γ :: Π⌋.
Proof.
  rewrite interp_flower interp_juxt and_comm currying.
  rewrite /gardens_to_form/fmg fmap_cons.
  rewrite cons_app Or_app Or_singl.
  rewrite (spol_r ⌊Γ⌋) and_or_distr.

  rewrite -interp_juxt -(wind_pollination γ Γ) interp_juxt.

  rewrite -and_or_distr -spol_r.
  rewrite -[⌊_ ! _⌋]Or_singl -Or_app -cons_app.
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
  * rewrite //=; eqd. pleft. pimpL 0; isrch.
  * rewrite //=; eqd. pleft.

  (* Permutation *)

  * by apply permutation_garden.
  * by apply permutation_flower.
Qed.

Lemma grounding : ∀ γ Γ Δ,
  ⌊Γ⌋ ⟺ ⌊Δ⌋ ->
  ⌊γ ! Γ⌋ ⟺ ⌊γ ! Δ⌋.
Proof.
  elim/gctx_induction => [Γ Δ H |γ H Π Γ Δ IH |γ H Γ Π Π' Σ Δ IH |ϕ H Fs Gs Γ Δ IH];
  rewrite /=; list_simplifier.
  * repeat rewrite flower_flowers -garden_flowers. exact.
  * repeat rewrite true_and. rewrite (H _ _ IH). reflexivity.
  * repeat rewrite true_and. rewrite (H _ _ IH). reflexivity.
  * rewrite And_app And_app. rewrite -[gl _]app_nil_r. rewrite (H _ _ IH).
    rewrite app_nil_r -And_app -And_app. reflexivity.
Qed.

Theorem soundness : ∀ Γ Δ,
  Γ ~>* Δ -> ⌊Γ⌋ ⟺ ⌊Δ⌋.
Proof.
  move => x y.
  elim => [Γ |Γ Δ Σ Hstep H IH] //.
  clear x y.
  * reflexivity.
  * rewrite -IH. elim: Hstep => γ Γ' Δ' H'.
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

Lemma interp_And : ∀ (Γ : list form),
  ⌈⋀ Γ⌉ = ⋃ ⌈[Γ]⌉.
Proof.
  elim => [|A Γ IH] //=. by rewrite IH.
Qed.

Lemma Juxt_Bind : ∀ (Π : list garden),
  ⋃ Π = ⋅(Δ ← Π; gl Δ).
Proof.
  elim => [|Δ Π IH] //=. case Δ => Fs. rewrite IH //=.
Qed.

Global Instance Juxt_Permutation : Proper ((≡ₚ) ==> (≡ₚ)) Juxt.
Proof.
  repeat red. move => Π Π' H.
  repeat rewrite Juxt_Bind. apply (bind_Permutation gl Π Π' H).
Qed.

Theorem completeness Γ C :
  Γ c⟹ C ->
  ⌈⋀ Γ⌉ ⊢ [⌈C⌉] ~>* ∅.
Proof.
  elim =>/=; clear Γ C.

  (* Axiom *)
  * move => A Γ.
    case ⌈A⌉ => As; case ⌈⋀ Γ⌉ => Γs; simpl.

    rstepm [0;1] ∅. rself.
    rspol □ (⋅As) (⋅Γs) (@nil garden).
    rstep ∅. rself. apply R_pet.
    reflexivity.
  
  (* Right ⊤ *)
  * move => Γ.
  
    rpetm (@nil nat). reflexivity.

  (* Right ∧ *)
  * move => A B Γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ Γ⌉ => Γs. simpl.
    move => Hp1 IH1 Hp2 IH2.

    rstepm_app [0;1] 0 (⋅[⊢ [⋅As]]).
    rctxm_app [0;1] 0.
    rcopis.

    rstepm_cons [0;1] 1 (⋅[⊢ [⋅Bs]]).
    rctxm_cons [0;1] 1.
    rcopis.

    spol [0;1;0;0].
    spol [0;1;1;0].

    rctxmH [0;1;0] IH1.
    rctxmH [0;1;0] IH2.

    rpetm (@nil nat).
    reflexivity.

  (* R∨₁ *)
  * move => A B Γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1.

    rcopism [0;1;0;1].
    spol [0;1;0;1;0;0].
    rctxmH [0;1;0;1;0] IH1.
    rpetm [0;1].
    rpetm (@nil nat).
    reflexivity.

  (* R∨₂ *)
  * move => A B Γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1.

    rcopism [0;1;0;2].
    spol [0;1;0;2;0;0].
    rctxmH [0;1;0;2;0] IH1.

    rcstepm [0;1;0] (⊢ [∅; ⋅As]).
    apply R_perm_f; solve_Permutation.

    rpetm [0;1].
    rpetm (@nil nat).
    reflexivity.

  (* R⊃ *)
  * move => A B Γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1.

    rstepm [0;1;0;0] (⋅As ++ Γs). rself.
    rspol (Planter [] (Pistil (Planter As □ []) [⋅Bs]) []) (⋅Γs) ∅ (@nil garden).

    rctxmH [0;1;0] IH1.
    rpetm (@nil nat).
    reflexivity.

  (* L⊤ *)
  * move => Γ C.
    case ⌈C⌉ => Cs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1.

    exact.

  (* L⊥ *)
  * move => Γ C.
    case ⌈C⌉ => Cs; case ⌈⋀ Γ⌉ => Γs.

    rstep (⋅Γs ⊢ [∅]). rself.
    rewrite /fg. rrep.
    rpetm (@nil nat). reflexivity.

  (* L∧ *)
  * move => A B Γ C.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈C⌉ => Cs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1.

    simpl in *. by rewrite -app_assoc.

  (* L∨ *)
  * move => A B Γ C.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈C⌉ => Cs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1 Hp2 IH2.
    
    rstep (⋅(⋅Γs ⊢ [⋅[⋅As ⊢ [⋅Cs]; ⋅Bs ⊢ [⋅Cs]]])). rself.
    rewrite /fg. rrep.

    rstepm [0;1;0;0] (⋅As ++ Γs). rself.
    rspol (Planter [] (Pistil (Planter As □ []) [⋅Cs]) [⋅Bs ⊢ [⋅Cs]]) (⋅Γs) ∅ (@nil garden).
    rstepm [0;1;1;0] (⋅Bs ++ Γs). rself.
    rspol (Planter [⋅As ++ Γs ⊢ [⋅Cs]] (Pistil (Planter Bs □ []) [⋅Cs]) []) (⋅Γs) ∅ (@nil garden).

    rctxmH [0;1;0] IH1.
    rctxmH [0;1;0] IH2.

    rpetm (@nil nat). reflexivity.

  (* L⊃ *)
  * move => A B Γ C.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈C⌉ => Cs; case ⌈⋀ Γ⌉ => Γs.
    move => Hp1 IH1 Hp2 IH2.

    rcopism [0;0;0;0].

    rcstepm [0;0] (⋅Γs ++ [⋅[⊢ [⋅As]] ⊢ [⋅Bs]]).
    apply R_perm_g; solve_Permutation.

    rcstepm [0;0] (⋅Γs ++ [⋅[⋅Γs ⊢ [⋅As]] ⊢ [⋅Bs]]).
    rwpolm [0;0;0;0].

    rcstepm [0;0] (⋅(⋅[⋅Γs ⊢ [⋅As]] ⊢ [⋅Bs]) :: Γs).
    apply R_perm_g; solve_Permutation.

    rctxmH [0;0;0;0] IH1.

    rpism [0;0;0].
    exact.

  (* Permutation *)
  * move => Γ Γ' C.
    move => Hperm Ip1 IH1.

    have H : ⌈⋀ Γ⌉ ≡ₚ ⌈⋀ Γ'⌉.
    { clear C Ip1 IH1.
      repeat rewrite interp_And.
      apply Juxt_Permutation.
      by apply fmap_Permutation. }

    destruct ⌈⋀ Γ⌉ as [Γs]. destruct ⌈⋀ Γ'⌉ as [Γs'].
    rstepm [0;0] (⋅Γs).
    rctxm [0;0]. apply R_perm_g; by symmetry.

    exact.
Qed.

End Completeness.

(** * Deduction *)

Definition entails Γ Δ := Γ ⊢ [Δ] ~>* ∅.

Infix "===>" := entails (at level 90).

Theorem deduction Γ Δ :
  Γ ===> Δ <-> ∅ ===> (Γ ⊢ [Δ]).
Proof.
  split; rewrite /entails; move => H.
  * rstep (Γ ⊢ [Δ]). rself. apply R_pis. exact.
  * rstep (⊢ [fg (Γ ⊢ [Δ])]). rself. apply R_co_pis. exact.
Qed.