Require Import String stdpp.list stdpp.relations.
Require Import ssreflect.

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

Import Flowers.Syntax.

Fixpoint flower_to_form (ϕ : flower) : form :=
  match ϕ with
  | Atom p args => FAtom p args
  | n ⋅ Φ ⊢ δ => n#∀ (⋀ (flower_to_form <$> Φ) ⊃ ⋁ (garden_to_form <$> δ))
  end
with garden_to_form (γ : garden) : form :=
  let '(n ⋅ Φ) := γ in
  n#∃ (⋀ (flower_to_form <$> Φ)).

Definition fmf := @fmap list list_fmap flower form.
Definition fmg := @fmap list list_fmap garden form.

Definition flowers_to_form := fmf garden_to_form.
Definition gardens_to_form := fmg garden_to_form.

Notation "⌊ ϕ ⌋" := (flower_to_form ϕ) (format "⌊ ϕ ⌋") : flower_scope.
Notation "⌊ γ ⌋" := (garden_to_form γ) (format "⌊ γ ⌋") : garden_scope.

Lemma flower_garden ϕ :
  ⌊ϕ⌋%flower ⟺ ⌊ϕ⌋%garden.
Proof.
  simpl. rewrite true_and. reflexivity.
Qed.

Lemma flower_flowers Φ :
  Forall2 eqderiv (flower_to_form <$> Φ) (flowers_to_form Φ).
Proof.
  apply Forall_equiv_map. apply eqderiv_Forall.
  move => F. rewrite flower_garden. reflexivity.
Qed.

Lemma garden_gardens Δ :
  Forall2 eqderiv (garden_to_form <$> Δ) (gardens_to_form Δ).
Proof.
  apply Forall_equiv_map. apply eqderiv_Forall.
  move => δ. reflexivity.
Qed.

Lemma gardens_flowers : ∀ (Δ : list garden),
  Forall2 eqderiv
  (gardens_to_form Δ)
  (fmg (λ '(n ⋅ Φ), n#∃ (⋀ (flowers_to_form Φ))) Δ).
Proof.
  elim => [|γ Δ IH] //=.
  econs. case γ => [n Ψ] //=.
  rewrite flower_flowers.
  reflexivity.
Qed.

Lemma garden_flowers n Φ : 
  ⌊n ⋅ Φ⌋ ⟺ n#∃ ⋀ (flowers_to_form Φ).
Proof.
  rewrite -flower_flowers.
  case Φ => *; reflexivity.
Qed.

Lemma interp_flower n Φ Δ :
  ⌊n ⋅ Φ ⊢ Δ⌋ ⟺
  (n#∀ (⋀ (flowers_to_form Φ) ⊃ ⋁ (gardens_to_form Δ))).
Proof.
  simpl. rewrite flower_flowers garden_gardens.
  rewrite true_and. reflexivity.
Qed.

Lemma interp_flower_flowers n Φ Δ :
  ⌊n ⋅ Φ ⊢ Δ⌋ ⟺
  (n#∀ (⋀ (flowers_to_form Φ) ⊃ ⋁ (fmg (λ '(m ⋅ Ψ), m#∃ ⋀ (flowers_to_form Ψ)) Δ))).
Proof.
  rewrite interp_flower gardens_flowers. reflexivity.
Qed.

Lemma interp_cons ϕ Φ :
  ⌊0 ⋅ ϕ :: Φ⌋ ⟺ ⌊ϕ⌋ ∧ ⌊0 ⋅ Φ⌋.
Proof.
  rewrite /=; eqd.
Qed.

Lemma ffill_gfill (F : fctx) (Ψ : list flower) :
  0 ⋅ F ⋖f Ψ = F ⋖ Ψ.
Proof.
  rewrite /=. by list_simplifier.
Qed.

Lemma assumed_Planter {ϕ n Φ F Φ'} :
  ϕ ∈ Planter n Φ F Φ' ->
  In ϕ Φ \/ ϕ ∈ F \/ In ϕ Φ'.
Admitted.

Open Scope list_scope.

Lemma In_app {A} {x : A} {l : list A} :
  In x l -> exists ll lr, l = ll ++ [x] ++ lr.
Admitted.

Lemma pollination G : ∀ ϕ,
  ϕ ∈ G ->
  ⌊G ⋖ [fshift (gbv G) 0 ϕ]⌋ ⟺
  ⌊G ⋖ []⌋.
Proof.
  elim/gctx_induction: G => [|F IH n Φ Φ' ϕ H] //=.
  list_simplifier.
  apply proper_nexists; auto.
  repeat rewrite And_app.

  elim (assumed_Planter H) => [HΦ |[HF |HΦ']].
  * elim (In_app HΦ) => [Φl [Φr Hsplit]].
    rewrite Hsplit.
    repeat rewrite fmap_app And_app.
    repeat rewrite map_singl And_singl.
    repeat rewrite and_assoc; apply proper_and; try reflexivity.
    repeat rewrite -and_assoc; apply proper_and; try reflexivity.
    rewrite and_assoc [⌊ϕ⌋%flower ∧ _]and_comm -and_assoc.
    rewrite [⌊ϕ⌋%flower ∧ _ ∧ _]and_assoc
            [⌊ϕ⌋%flower ∧ ⋀ (flower_to_form <$> Φr)]and_comm
            -and_assoc.
    apply proper_and; try reflexivity.
    rewrite wpol_And -list_fmap_compose.
    rewrite /Pflower in IH.
    destruct F; simpl.
Restart.
  elim/gctx_induction: G => [|F IH n Φ Φ' ϕ H] //=.
  list_simplifier.
  apply proper_nexists; auto.
  repeat rewrite And_app.

  rewrite /Pflower in IH.
  induction F using fctx_induction.
  * simpl. repeat rewrite true_and.
Admitted.

Lemma self_pollination (γ : gctx) (γ δ : garden) (Δ : list garden) :
  ⌊γ ∪ δ ⊢ γ ! ∅ :: Δ⌋ ⟺ ⌊γ ∪ δ ⊢ γ ! γ :: Δ⌋.
Proof.
  rewrite interp_flower interp_juxt and_comm currying.
  rewrite /gardens_to_form/fmg fmap_cons.
  rewrite cons_app Or_app Or_singl.
  rewrite (spol_r ⌊γ⌋) and_or_distr.

  rewrite -interp_juxt -(wind_pollination γ γ) interp_juxt.

  rewrite -and_or_distr -spol_r.
  rewrite -[⌊_ ! _⌋]Or_singl -Or_app -cons_app.
  rewrite -fmap_cons -/fmg -/gardens_to_form.
  rewrite -currying -and_comm -interp_juxt -interp_flower.

  by reflexivity.
Qed.

Lemma reproduction δs γ Δ :
  ⌊γ ⊢ [⋅(λ δ, δ ⊢ Δ) <$> δs]⌋ ⟺ ⌊(⊢ δs) ∪ γ ⊢ Δ⌋.
Proof.
  rewrite interp_flower_flowers -garden_flowers.
  rewrite [fmg _ _]/= Or_singl.
  rewrite /flowers_to_form /fmf -list_fmap_compose /compose.
  rewrite (eqderiv_map (λ δ, ⌊δ ⊢ Δ⌋) (λ δ, ⌊δ⌋ ⊃ ⋁ (gardens_to_form Δ))).
  { intros. simpl. rewrite true_and. reflexivity. }

  rewrite interp_flower_flowers -garden_flowers.
  rewrite interp_juxt interp_flower_flowers -garden_flowers.
  rewrite [⌊∅⌋]/= true_imp_l.
  pose proof (H := garden_flowers). symmetry in H.
  repeat rewrite /fmg (eqderiv_map (λ δ : garden, ⋀ (flowers_to_form δ)) garden_to_form); auto.

  rewrite and_comm.
  apply or_intro_l_nary.
Qed.

Lemma permutation_garden Φ Φ' :
  Φ ≡ₚ Φ' ->
  ⌊⋅Φ⌋ ⟺ ⌊⋅Φ'⌋.
Proof.
  elim; clear Φ Φ'.
  * reflexivity.
  * move => F Φ Φ' Hperm IH.
    rewrite (cons_app _ Φ') (cons_app _ Φ).
    repeat rewrite -/(juxt (⋅[F]) (⋅Φ)) -/(juxt (⋅[F]) (⋅Φ')) interp_juxt.
    rewrite IH. reflexivity.
  * move => F G Φ. simpl. rewrite and_comm. eqd.
  * move => Φ1 Φ2 Φ3 Hperm1 H1 Hperm2 H2.
    rewrite H1 H2. reflexivity.
Qed.

Lemma permutation_flower (Δ Δ' : list garden) (γ : garden) :
  Δ ≡ₚ Δ' ->
  ⌊γ ⊢ Δ⌋ ⟺ ⌊γ ⊢ Δ'⌋.
Proof.
  elim; clear Δ Δ'.
  * reflexivity.
  * move => δ Φ Φ' Hperm IH.
    simpl in *.
    repeat rewrite true_and in IH.
    repeat rewrite true_and.
    by apply proper_concl.
  * move => δ Σ Δ. simpl.
    repeat rewrite true_and.
    rewrite or_assoc [⌊Σ⌋ ∨ _]or_comm -or_assoc.
    reflexivity.
  * move => Δ1 Δ2 Δ3 Hperm1 H1 Hperm2 H2.
    rewrite H1 H2. reflexivity.
Qed.

Lemma local_soundness : ∀ (γ δ : garden),
  γ ⇀ δ -> ⌊γ⌋ ⟺ ⌊δ⌋.
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

Lemma grounding : ∀ γ γ δ,
  ⌊γ⌋ ⟺ ⌊δ⌋ ->
  ⌊γ ! γ⌋ ⟺ ⌊γ ! δ⌋.
Proof.
  elim/gctx_induction => [γ δ H |γ H Δ γ δ IH |γ H γ Δ Δ' Σ δ IH |ϕ H Φ Gs γ δ IH];
  rewrite /=; list_simplifier.
  * repeat rewrite flower_flowers -garden_flowers. exact.
  * repeat rewrite true_and. rewrite (H _ _ IH). reflexivity.
  * repeat rewrite true_and. rewrite (H _ _ IH). reflexivity.
  * rewrite And_app And_app. rewrite -[gl _]app_nil_r. rewrite (H _ _ IH).
    rewrite app_nil_r -And_app -And_app. reflexivity.
Qed.

Theorem soundness : ∀ γ δ,
  γ ~>* δ -> ⌊γ⌋ ⟺ ⌊δ⌋.
Proof.
  move => x y.
  elim => [γ |γ δ Σ Hstep H IH] //.
  clear x y.
  * reflexivity.
  * rewrite -IH. elim: Hstep => γ γ' δ' H'.
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

Notation "⌈[ γ ]⌉" := (interp <$> γ).

Lemma interp_And : ∀ (γ : list form),
  ⌈⋀ γ⌉ = ⋃ ⌈[γ]⌉.
Proof.
  elim => [|A γ IH] //=. by rewrite IH.
Qed.

Lemma Juxt_Bind : ∀ (Δ : list garden),
  ⋃ Δ = ⋅(δ ← Δ; gl δ).
Proof.
  elim => [|δ Δ IH] //=. case δ => Φ. rewrite IH //=.
Qed.

Global Instance Juxt_Permutation : Proper ((≡ₚ) ==> (≡ₚ)) Juxt.
Proof.
  repeat red. move => Δ Δ' H.
  repeat rewrite Juxt_Bind. apply (bind_Permutation gl Δ Δ' H).
Qed.

Theorem completeness Γ C :
  Γ c⟹ C ->
  ⌈⋀ Γ⌉ ⊢ [⌈C⌉] ~>* ∅.
Proof.
  elim =>/=; clear γ C.

  (* Axiom *)
  * move => A γ.
    case ⌈A⌉ => As; case ⌈⋀ γ⌉ => γs; simpl.

    rstepm [0;1] ∅. rself.
    rspol □ (⋅As) (⋅γs) (@nil garden).
    rstep ∅. rself. apply R_pet.
    reflexivity.
  
  (* R⊤ *)
  * move => γ.
  
    rpetm (@nil nat). reflexivity.

  (* R∧ *)
  * move => A B γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ γ⌉ => γs. simpl.
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
  * move => A B γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ γ⌉ => γs.
    move => Hp1 IH1.

    rcopism [0;1;0;1].
    spol [0;1;0;1;0;0].
    rctxmH [0;1;0;1;0] IH1.
    rpetm [0;1].
    rpetm (@nil nat).
    reflexivity.

  (* R∨₂ *)
  * move => A B γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ γ⌉ => γs.
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
  * move => A B γ.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈⋀ γ⌉ => γs.
    move => Hp1 IH1.

    rstepm [0;1;0;0] (⋅As ++ γs). rself.
    rspol (Planter [] (Pistil (Planter As □ []) [⋅Bs]) []) (⋅γs) ∅ (@nil garden).

    rctxmH [0;1;0] IH1.
    rpetm (@nil nat).
    reflexivity.

  (* L⊤ *)
  * move => γ C.
    case ⌈C⌉ => Cs; case ⌈⋀ γ⌉ => γs.
    move => Hp1 IH1.

    exact.

  (* L⊥ *)
  * move => γ C.
    case ⌈C⌉ => Cs; case ⌈⋀ γ⌉ => γs.

    rstep (⋅γs ⊢ [∅]). rself.
    rewrite /fg. rrep.
    rpetm (@nil nat). reflexivity.

  (* L∧ *)
  * move => A B γ C.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈C⌉ => Cs; case ⌈⋀ γ⌉ => γs.
    move => Hp1 IH1.

    simpl in *. by rewrite -app_assoc.

  (* L∨ *)
  * move => A B γ C.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈C⌉ => Cs; case ⌈⋀ γ⌉ => γs.
    move => Hp1 IH1 Hp2 IH2.
    
    rstep (⋅(⋅γs ⊢ [⋅[⋅As ⊢ [⋅Cs]; ⋅Bs ⊢ [⋅Cs]]])). rself.
    rewrite /fg. rrep.

    rstepm [0;1;0;0] (⋅As ++ γs). rself.
    rspol (Planter [] (Pistil (Planter As □ []) [⋅Cs]) [⋅Bs ⊢ [⋅Cs]]) (⋅γs) ∅ (@nil garden).
    rstepm [0;1;1;0] (⋅Bs ++ γs). rself.
    rspol (Planter [⋅As ++ γs ⊢ [⋅Cs]] (Pistil (Planter Bs □ []) [⋅Cs]) []) (⋅γs) ∅ (@nil garden).

    rctxmH [0;1;0] IH1.
    rctxmH [0;1;0] IH2.

    rpetm (@nil nat). reflexivity.

  (* L⊃ *)
  * move => A B γ C.
    case ⌈A⌉ => As; case ⌈B⌉ => Bs; case ⌈C⌉ => Cs; case ⌈⋀ γ⌉ => γs.
    move => Hp1 IH1 Hp2 IH2.

    rcopism [0;0;0;0].

    rcstepm [0;0] (⋅γs ++ [⋅[⊢ [⋅As]] ⊢ [⋅Bs]]).
    apply R_perm_g; solve_Permutation.

    rcstepm [0;0] (⋅γs ++ [⋅[⋅γs ⊢ [⋅As]] ⊢ [⋅Bs]]).
    rwpolm [0;0;0;0].

    rcstepm [0;0] (⋅(⋅[⋅γs ⊢ [⋅As]] ⊢ [⋅Bs]) :: γs).
    apply R_perm_g; solve_Permutation.

    rctxmH [0;0;0;0] IH1.

    rpism [0;0;0].
    exact.

  (* Contraction *)
  * move => A γ C.
    case ⌈A⌉ => As; case ⌈C⌉ => Cs; case ⌈⋀ γ⌉ => γs; simpl.
    move => Hp1 IH1.

    rstepm_app [0;0] 0 (⋅As ++ As).
    rctx (Planter [] (Pistil (Planter [] □ γs) [⋅Cs]) []) (⋅As) (⋅As ++ As).
    rwpol □ (⋅As).

    exact.

  (* Permutation *)
  * move => γ γ' C.
    move => Hperm Ip1 IH1.

    have H : ⌈⋀ γ⌉ ≡ₚ ⌈⋀ γ'⌉.
    { clear C Ip1 IH1.
      repeat rewrite interp_And.
      apply Juxt_Permutation.
      by apply fmap_Permutation. }

    destruct ⌈⋀ γ⌉ as [γs]. destruct ⌈⋀ γ'⌉ as [γs'].
    rstepm [0;0] (⋅γs).
    rctxm [0;0]. apply R_perm_g; by symmetry.

    exact.
Qed.

End Completeness.

(** * Deduction *)

Definition entails γ δ := γ ⊢ [δ] ~>* ∅.

Infix "===>" := entails (at level 90).

Theorem deduction γ δ :
  γ ===> δ <-> ∅ ===> (γ ⊢ [δ]).
Proof.
  split; rewrite /entails; move => H.
  * rstep (γ ⊢ [δ]). rself. apply R_pis. exact.
  * rstep (⊢ [fg (γ ⊢ [δ])]). rself. apply R_co_pis. exact.
Qed.