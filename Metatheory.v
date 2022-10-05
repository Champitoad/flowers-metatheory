Require Import String stdpp.list stdpp.relations.
Require Import ssreflect.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.
Close Scope string_scope.

(** * Soundness *)

Section Soundness.

Import Flowers.Syntax.

Reserved Notation "⌊ ϕ ⌋" (format "⌊ ϕ ⌋").
Reserved Notation "⌊⌊ ϕ ⌋⌋" (format "⌊⌊ ϕ ⌋⌋").

Fixpoint flower_to_form (ϕ : flower) : form :=
  match ϕ with
  | Atom p args => FAtom p args
  | n ⋅ Φ ⊢ Δ => n#∀ (⋀ ⌊⌊Φ⌋⌋ ⊃ ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊⌊Ψ⌋⌋) <$> Δ))
  end
where "⌊ ϕ ⌋" := (flower_to_form ϕ)
  and "⌊⌊ Φ ⌋⌋" := (flower_to_form <$> Φ).

Definition interp (Φ : bouquet) :=
  ⋀ ⌊⌊Φ⌋⌋.

Notation "⟦ Φ ⟧" := (interp Φ) (format "⟦ Φ ⟧").

Lemma interp_flower (ϕ : flower) :
  ⟦ϕ⟧ ⟺ ⌊ϕ⌋.
Proof.
  rewrite /interp/=. by rewrite true_and.
Qed.

Lemma fshift_shift (ϕ : flower) : ∀ n c,
  fshift n c ⌊ϕ⌋ ⟺ ⌊shift n c ϕ⌋.
Proof.
  elim/flower_induction: ϕ => [p args n c |γ Δ IHγ IHΔ n c]//=.
  move: Δ IHγ IHΔ; case γ => [m Φ]; move => Δ IHγ IHΔ.
  rewrite /interp/=.
  rewrite fshift_nforall/= fshift_And fshift_Or.
  rewrite Forall_forall in IHγ; specialize (IHγ n).
  rewrite Forall_forall in IHγ; specialize (IHγ (c + m)).
  rewrite Forall_equiv_map in IHγ.
  rewrite IHγ.
  rewrite -list_fmap_compose list_fmap_compose.
  set f := λ δ : garden, fshift n (c + m) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋.
  set h := λ δ : garden, let 'k ⋅ Ψ := δ in k ⋅ (shift n (c + m + k)) <$> Ψ.
  assert (H : Forall2 eqderiv (f <$> Δ) (g ∘ h <$> Δ)).
  (* { induction Δ; inv IHΔ; econs. *)
  { elim: {Δ} IHΔ => [|[k Ψ] Δ IHΨ IHΔ ?]//=; econs.
    rewrite /f/g/h//=.
    rewrite fshift_nexists fshift_And.
    apply proper_nexists; auto; apply proper_And; auto.
    rewrite list_fmap_compose -list_fmap_compose -list_fmap_compose.
    apply Forall_equiv_map. rewrite /=.
    rewrite Forall_forall in IHΨ; specialize (IHΨ n).
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + m + k)).
    done. }
  by rewrite H list_fmap_compose.
Qed.

Lemma wpol X : ∀ (ϕ : flower),
  ⟦ϕ⟧ ∧ ⟦X ⋖ shift (bv X) 0 ϕ⟧ ⟺
  ⟦ϕ⟧ ∧ ⟦X ⋖ []⟧.
Proof.
  induction X; intro;
  rewrite /interp//=;
  repeat rewrite true_and.
  * rewrite shift_zero. eqd.
  * repeat rewrite fmap_app And_app.
    rewrite and_assoc [(⌊ϕ⌋) ∧ _]and_comm and_assoc -[(_ ∧ ⌊ϕ⌋) ∧ _]and_assoc.
    pose proof (IH := IHX ϕ); rewrite /interp/= true_and in IH.
    rewrite IH; eqd.
  * repeat rewrite wpol_nforall; apply proper_nforall; auto.
    repeat rewrite [_ ∧ (⋀ _ ⊃ _)]wpol_imp_l; apply proper_and; auto.
    apply proper_imp; auto.
    pose proof (IH := IHX (shift n 0 ϕ)).
    repeat rewrite interp_flower in IH.
    rewrite -fshift_shift shift_comm -shift_add /interp/= in IH.
    by rewrite IH.
  * case γ => [k Φ].
    repeat rewrite wpol_nforall; apply proper_nforall; auto.
    repeat rewrite [_ ∧ (_ ⊃ ⋁ _)]wpol_imp_r ; apply proper_and; auto.
    apply proper_imp; auto.
    repeat rewrite [_ :: Δ']cons_app.
    repeat rewrite fmap_app Or_app.
    do 4 rewrite and_or_distr.
    apply proper_or; auto.
    apply proper_or; auto.
    repeat rewrite Or_singl.
    repeat rewrite wpol_nexists; apply proper_nexists; auto.
    pose proof (IH := IHX (shift n 0 (shift k 0 ϕ))).
    repeat rewrite interp_flower in IH.
    repeat rewrite -shift_add in IH.
    rewrite -fshift_shift in IH.
    repeat rewrite fshift_add in IH.
    repeat rewrite /interp/= true_and in IH.
    assert (Hcomm : bv X + (n + k) = k + n + bv X). { lia. }
    rewrite Hcomm in IH.
    by rewrite IH.
Qed.

Lemma pollination (X : ctx) : ∀ (ϕ : flower) (n : nat),
  ϕ ≺ n in X ->
  ⟦X ⋖ [shift n 0 ϕ]⟧ ⟺
  ⟦X ⋖ []⟧.
Proof.
  intros ?? H. inv H; list_simplifier.
  * rewrite /interp/=.
    repeat rewrite fmap_app fmap_cons.
    repeat rewrite true_and.
    apply proper_nforall; auto.
    rewrite cons_app. repeat rewrite And_app. rewrite And_singl.
    rewrite [⌊ϕ⌋ ∧ _]and_comm.
    repeat rewrite [⋀ ⌊⌊Φ⌋⌋ ∧ _]and_assoc.
    repeat rewrite [_ ∧ ⌊ϕ⌋ ⊃ _]currying.
    apply proper_imp; auto.
    repeat rewrite [m#∃ _ :: (_ <$> _)]cons_app.
    repeat rewrite Or_app.
    apply proper_concl.
    repeat rewrite [⋁ [_] ∨ _]or_comm.
    apply proper_concl.
    repeat rewrite Or_singl.
    repeat rewrite [_ ⊃ m#∃ _]spol_r.
    apply proper_imp; auto.
    repeat rewrite wpol_nexists.
    apply proper_nexists; auto.
    rewrite fshift_shift.
    rewrite shift_add shift_comm.
    by rewrite -interp_flower wpol.
  * rewrite /interp [ϕ :: Φ']cons_app.
    repeat rewrite fmap_app And_app. rewrite And_singl.
    apply proper_and; auto.
    rewrite [⋀ ⌊⌊Φ⌋⌋ ∧ _]and_comm.
    rewrite -[_ ∧ ⋀ ⌊⌊Φ⌋⌋]and_assoc.
    repeat rewrite [_ ∧ ⌊ϕ⌋ ∧ _]and_assoc.
    apply proper_and; auto.
    repeat rewrite [_ ∧ ⌊ϕ⌋]and_comm.
    by rewrite -interp_flower wpol.
  * rewrite /interp. repeat rewrite [ϕ :: _ ++ _]cons_app.
    repeat rewrite fmap_app And_app. rewrite And_singl.
    apply proper_and; auto.
    repeat rewrite and_assoc.
    apply proper_and; auto.
    rewrite [_ ∧ ⋀ ⌊⌊Φ'⌋⌋]and_comm.
    rewrite -and_assoc -and_assoc.
    apply proper_and; auto.
    by rewrite -interp_flower wpol.
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