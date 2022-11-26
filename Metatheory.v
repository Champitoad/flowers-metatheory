Require Import stdpp.list stdpp.relations.
Require Import ssreflect.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.

(** * Soundness *)

Import Flowers.Syntax.

Reserved Notation "⌊ ϕ ⌋" (format "⌊ ϕ ⌋").
Reserved Notation "⌊[ ϕ ]⌋" (format "⌊[ ϕ ]⌋").

Fixpoint flower_to_form (ϕ : flower) : form :=
  match ϕ with
  | Atom p args => FAtom p args
  | n ⋅ Φ ⫐ Δ => n#∀ (⋀ ⌊[Φ]⌋ ⊃ ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊[Ψ]⌋) <$> Δ))
  end
where "⌊ ϕ ⌋" := (flower_to_form ϕ)
  and "⌊[ Φ ]⌋" := (flower_to_form <$> Φ).

Definition interp (Φ : bouquet) :=
  ⋀ ⌊[Φ]⌋.

Notation "⟦ Φ ⟧" := (interp Φ) (format "⟦ Φ ⟧").

Lemma interp_flower (ϕ : flower) :
  ⟦ϕ⟧ ⟺ ⌊ϕ⌋.
Proof.
  rewrite /interp/=. by rewrite true_and.
Qed.

Lemma fshift_shift (ϕ : flower) : ∀ n c,
  fshift n c ⌊ϕ⌋ = ⌊shift n c ϕ⌋.
Proof.
  elim/flower_induction: ϕ => [p args |γ Δ IHγ IHΔ] n c //=.
  move: Δ IHγ IHΔ; case γ => [m Φ]; move => Δ IHγ IHΔ.
  rewrite /interp/=.
  rewrite fshift_nforall/= fshift_And fshift_Or.
  rewrite Forall_forall in IHγ; specialize (IHγ n).
  rewrite Forall_forall in IHγ; specialize (IHγ (c + m)).
  rewrite Forall_equiv_map in IHγ.
  rewrite IHγ.
  rewrite -list_fmap_compose list_fmap_compose.
  set f := λ δ : garden, fshift n (c + m) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊[Ψ]⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊[Ψ]⌋.
  set h := λ δ : garden, let 'k ⋅ Ψ := δ in k ⋅ (shift n (c + m + k)) <$> Ψ.
  assert (H : Forall2 eq (f <$> Δ) (g ∘ h <$> Δ)).
  { elim: {Δ} IHΔ => [|[k Ψ] Δ IHΨ _ IH]//=; econs.
    rewrite /f/g/h//=.
    rewrite fshift_nexists fshift_And.
    do 2 f_equal.
    rewrite list_fmap_compose -list_fmap_compose -list_fmap_compose.
    apply Forall_eq_map. rewrite /=.
    rewrite Forall_forall in IHΨ; specialize (IHΨ n).
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + m + k)).
    done. }
  by rewrite H list_fmap_compose.
Qed.

Lemma fshift_bshift (Ψ : bouquet) : ∀ n c,
  fshift n c ⟦Ψ⟧ = ⟦shift n c <$> Ψ⟧.
Proof.
  elim: Ψ => [|ϕ Φ IH] n c //=.
  rewrite IH /interp fshift_shift //.
Qed.

Lemma funshift_unshift : ∀ (ϕ : flower) n c,
  funshift n c ⌊ϕ⌋ = ⌊unshift n c ϕ⌋.
Proof.
  elim/flower_induction => [p args |γ Δ IHγ IHΔ] n c //=.
  move: Δ IHγ IHΔ; case γ => [m Φ]; move => Δ IHγ IHΔ.
  rewrite /interp/=.
  rewrite funshift_nforall/= funshift_And funshift_Or.
  rewrite Forall_forall in IHγ; specialize (IHγ n).
  rewrite Forall_forall in IHγ; specialize (IHγ (c + m)).
  rewrite Forall_equiv_map in IHγ.
  rewrite IHγ.
  rewrite -list_fmap_compose list_fmap_compose.
  set f := λ δ : garden, funshift n (c + m) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊[Ψ]⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊[Ψ]⌋.
  set h := λ δ : garden, let 'k ⋅ Ψ := δ in k ⋅ (unshift n (c + m + k)) <$> Ψ.
  assert (H : Forall2 eq (f <$> Δ) (g ∘ h <$> Δ)).
  { elim: {Δ} IHΔ => [|[k Ψ] Δ IHΨ _ IH]//=; econs.
    rewrite /f/g/h//=.
    rewrite funshift_nexists funshift_And.
    do 2 f_equal.
    rewrite list_fmap_compose -list_fmap_compose -list_fmap_compose.
    apply Forall_eq_map. rewrite /=.
    rewrite Forall_forall in IHΨ; specialize (IHΨ n).
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + m + k)).
    done. }
  by rewrite H list_fmap_compose.
Qed.

Lemma funshift_bunshift (Ψ : bouquet) : ∀ n c,
  funshift n c ⟦Ψ⟧ = ⟦unshift n c <$> Ψ⟧.
Proof.
  elim: Ψ => [|ϕ Φ IH] n c //=.
  rewrite IH /interp funshift_unshift //.
Qed.

Lemma fsubst_subst : ∀ (ϕ : flower) n t,
  fsubst n t ⌊ϕ⌋ = ⌊subst n t ϕ⌋.
Proof.
  elim/flower_induction => [p args |γ Δ IHγ IHΔ] n t //=.
  move: Δ IHγ IHΔ; case γ => [m Φ]; move => Δ IHγ IHΔ.
  rewrite /interp/=.
  rewrite fsubst_nforall/= fsubst_And fsubst_Or.
  rewrite Forall_forall in IHγ; specialize (IHγ (n + m)).
  rewrite Forall_forall in IHγ; specialize (IHγ (Terms.tshift m 0 t)).
  rewrite Forall_equiv_map in IHγ.
  rewrite IHγ.
  rewrite -list_fmap_compose list_fmap_compose.
  set f := λ δ : garden, fsubst (n + m) (Terms.tshift m 0 t) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊[Ψ]⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊[Ψ]⌋.
  set h := λ δ : garden, let 'k ⋅ Ψ := δ in k ⋅ (subst (n + m + k) (Terms.tshift (m + k) 0 t)) <$> Ψ.
  assert (H : Forall2 eq (f <$> Δ) (g ∘ h <$> Δ)).
  { elim: {Δ} IHΔ => [|[k Ψ] Δ IHΨ _ IH]//=; econs.
    rewrite /f/g/h//=.
    rewrite fsubst_nexists fsubst_And.
    do 2 f_equal.
    rewrite list_fmap_compose -list_fmap_compose -list_fmap_compose.
    apply Forall_eq_map. rewrite /=.
    rewrite Forall_forall in IHΨ; specialize (IHΨ (n + m + k)).
    rewrite Forall_forall in IHΨ; specialize (IHΨ (Terms.tshift (m + k) 0 t)).
    rewrite -Terms.tshift_add [k + m]Nat.add_comm.
    done. }
  by rewrite H list_fmap_compose.
Qed.

Lemma fsubst_bsubst (Ψ : bouquet) : ∀ n c,
  fsubst n c ⟦Ψ⟧ = ⟦subst n c <$> Ψ⟧.
Proof.
  elim: Ψ => [|ϕ Φ IH] n c //=.
  rewrite IH /interp fsubst_subst //.
Qed.

Lemma grounding : ∀ X Φ Ψ,
  ⟦Φ⟧ ⟺ ⟦Ψ⟧ ->
  ⟦X ⋖ Φ⟧ ⟺ ⟦X ⋖ Ψ⟧.
Proof.
  elim => [Φ Ψ |Φ1 X IHX Φ2 Φ Ψ |n X IHX Δ Φ Ψ |γ Δ n X IHX Δ' Φ Ψ] H //=;
  rewrite /interp/= in H IHX |- *.
  * repeat rewrite fmap_app And_app.
    rewrite (IHX Φ Ψ) //.
  * rewrite (IHX Φ Ψ) //.
  * case: γ => [m Θ].
    do 2 rewrite [_ :: Δ']cons_app.
    repeat rewrite fmap_app; do 2 rewrite fmap_singl.
    repeat rewrite Or_app; do 2 rewrite Or_singl.
    rewrite (IHX Φ Ψ) //.
Qed.

Lemma wpol X : ∀ (Ψ : bouquet),
  ⟦Ψ⟧ ∧ ⟦X ⋖ (shift (bv X) 0 <$> Ψ)⟧ ⟺
  ⟦Ψ⟧ ∧ ⟦X ⋖ []⟧.
Proof.
  induction X; intro;
  rewrite /interp//=;
  repeat rewrite true_and.
  * rewrite bshift_zero. eqd.
  * repeat rewrite fmap_app And_app.
    rewrite and_assoc [(⋀ ⌊[Ψ]⌋) ∧ _]and_comm and_assoc -[(_ ∧ ⋀ ⌊[Ψ]⌋) ∧ _]and_assoc.
    pose proof (IH := IHX Ψ); rewrite /interp/= in IH.
    rewrite IH; eqd.
  * repeat rewrite wpol_nforall; apply proper_nforall; auto.
    repeat rewrite [_ ∧ (⋀ _ ⊃ _)]wpol_imp_l; apply proper_and; auto.
    apply proper_imp; auto.
    pose proof (IH := IHX (shift n 0 <$> Ψ)).
    repeat rewrite interp_flower in IH.
    rewrite -fshift_bshift bshift_comm -bshift_add /interp/= in IH.
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
    pose proof (IH := IHX (shift n 0 <$> (shift k 0 <$> Ψ))).
    repeat rewrite -bshift_add in IH.
    rewrite -fshift_bshift in IH.
    repeat rewrite fshift_add in IH.
    repeat rewrite /interp/= true_and in IH.
    assert (Hcomm : bv X + (n + k) = k + n + bv X). { lia. }
    rewrite Hcomm in IH.
    by rewrite IH.
Qed.

Lemma pollination (X : ctx) : ∀ (Ψ : bouquet) (n : nat),
  Ψ ≺ n in X ->
  ⟦X ⋖ (shift n 0 <$> Ψ)⟧ ⟺
  ⟦X ⋖ []⟧.
Proof.
  intros ?? H. inv H; list_simplifier.
  * rewrite /interp/=.
    repeat rewrite fmap_app.
    repeat rewrite true_and.
    apply proper_nforall; auto.
    rewrite cons_app fmap_app. repeat rewrite And_app.
    rewrite [⋀ ⌊[Ψ]⌋ ∧ _]and_comm.
    repeat rewrite [⋀ ⌊[Φ]⌋ ∧ _]and_assoc.
    repeat rewrite [_ ∧ ⋀ ⌊[Ψ]⌋ ⊃ _]currying.
    apply proper_imp; auto.
    rewrite [_ :: Δ']cons_app fmap_app.
    repeat rewrite Or_app.
    apply proper_concl.
    repeat rewrite [⋁ [_] ∨ _]or_comm.
    apply proper_concl.
    repeat rewrite Or_singl.
    repeat rewrite [_ ⊃ m#∃ _]spol_r.
    apply proper_imp; auto.
    repeat rewrite wpol_nexists.
    apply proper_nexists; auto.
    do 2 rewrite -/(interp (_ ⋖ _)).
    rewrite fshift_bshift.
    rewrite bshift_add bshift_comm.
    by rewrite wpol.
  * rewrite /interp. list_simplifier.
    repeat rewrite And_app.
    apply proper_and; auto.
    rewrite [⋀ ⌊[Φ]⌋ ∧ _]and_comm.
    rewrite -[_ ∧ ⋀ ⌊[Φ]⌋]and_assoc.
    repeat rewrite [_ ∧ ⋀ ⌊[Ψ]⌋ ∧ _]and_assoc.
    apply proper_and; auto.
    repeat rewrite [_ ∧ ⋀ ⌊[Ψ]⌋]and_comm.
    by rewrite wpol.
  * rewrite /interp. list_simplifier.
    repeat rewrite And_app.
    apply proper_and; auto.
    repeat rewrite and_assoc.
    apply proper_and; auto.
    rewrite [_ ∧ ⋀ ⌊[Φ']⌋]and_comm.
    rewrite -and_assoc -and_assoc.
    apply proper_and; auto.
    by rewrite wpol.
Qed.

Lemma reproduction (Δ : list garden) n (Φ Φ' : bouquet) (Δ' : list garden) :
  ⟦n ⋅ Φ ++ [⫐ Δ] ++ Φ' ⫐ Δ'⟧ ⟺
  ⟦n ⋅ Φ ++ Φ' ⫐ [0 ⋅ (λ '(m ⋅ Ψ), m ⋅ Ψ ⫐ gshift m 0 <$> Δ') <$> Δ]⟧.
Proof.
  rewrite /interp/=.
  repeat rewrite true_and; repeat rewrite false_or.
  rewrite -list_fmap_compose /compose.
  under [_ <$> Δ]eqderiv_map => δ do simpl.

  rewrite cons_app; repeat rewrite fmap_app And_app.
  rewrite /=. rewrite true_imp_l true_and.
  rewrite [_ ∧ ⋀ _]and_comm and_assoc.
  rewrite -or_intro_l_nary.

  apply proper_nforall; auto.
  apply proper_imp; auto.
  apply proper_And; auto.
  apply Forall_equiv_map.
  apply equiv_Forall. move => [k Θ] /=.
  assert (H :
    fshift k 0 ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊[Ψ]⌋) <$> Δ') ⟺
    ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊[Ψ]⌋) <$> (gshift k 0 <$> Δ'))).
  { rewrite fshift_Or.
    apply proper_Or.
    rewrite -list_fmap_compose.
    apply Forall_equiv_map; apply equiv_Forall; move => [m Ψ] /=.
    rewrite fshift_nexists fshift_And /=.
    apply proper_nexists; auto; apply proper_And; auto.
    rewrite -list_fmap_compose.
    apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=.
    by rewrite -fshift_shift. }
  rewrite -H.
  apply nexists_intro_l.
Qed.

Lemma epis_pis m Ψ n Φ Φ' Δ :
  ⟦n ⋅ Φ ++ [⫐ [m ⋅ Ψ]] ++ Φ' ⫐ Δ⟧ ⟺
  ⟦n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ') ⫐ gshift m 0 <$> Δ⟧.
Proof.
  rewrite /interp/= true_and true_and.
  rewrite -nforall_add.
  apply proper_nforall; auto.
  rewrite cons_app; repeat rewrite fmap_app.
  repeat rewrite And_app.
  rewrite fmap_singl And_singl /= true_imp_l false_or.
  rewrite [m#∃ _ ∧ _]and_comm and_assoc currying.
  rewrite nexists_intro_l.
  rewrite [⋀ ⌊[Ψ]⌋ ∧ _]and_comm and_assoc [_ ∧ ⋀ ⌊[Ψ]⌋ ⊃ _]currying.
  assert (H :
    ⋀ ⌊[shift m 0 <$> Φ]⌋ ∧ ⋀ ⌊[shift m 0 <$> Φ']⌋ ⟺
    fshift m 0 (⋀ ⌊[Φ]⌋ ∧ ⋀ ⌊[Φ']⌋)).
  { rewrite /= fshift_And fshift_And.
    apply proper_and;
    apply proper_And; rewrite -list_fmap_compose;
    apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=;
    by rewrite fshift_shift. }
  rewrite H.
  rewrite nforall_imp_switch_r.
  apply proper_imp; auto; apply proper_nforall; auto; apply proper_imp; auto.
  rewrite fshift_Or. apply proper_Or; auto.
  rewrite -list_fmap_compose.
  apply Forall_equiv_map; apply equiv_Forall; move => [k Θ] /=.
  rewrite fshift_nexists fshift_And /=.
  apply proper_nexists; auto; apply proper_And; auto.
  rewrite -list_fmap_compose.
  apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=.
  by rewrite fshift_shift.
Qed.

Lemma epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  ⟦γ ⫐ Δ ++ [n ⋅ Φ ++ [⫐ [m ⋅ Ψ]] ++ Φ'] ++ Δ'⟧ ⟺
  ⟦γ ⫐ Δ ++ [n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ')] ++ Δ'⟧.
Proof.
  rewrite /interp/= true_and true_and. case γ => [k Θ].
  apply proper_nforall; auto; apply proper_imp; auto.
  rewrite cons_app; repeat rewrite fmap_app.
  repeat rewrite Or_app.
  apply proper_or; auto; apply proper_or; auto.
  rewrite cons_app; repeat rewrite fmap_app /=.
  rewrite true_imp_l. repeat rewrite false_or.
  rewrite cons_app; repeat rewrite fmap_app /=.
  repeat rewrite And_app. rewrite And_singl.
  rewrite -nexists_add.
  apply proper_nexists; auto.
  rewrite [⋀ ⌊[Ψ]⌋ ∧ _]and_comm [⋀ ⌊[shift m 0 <$> Φ]⌋ ∧ _]and_assoc.
  assert (H :
    ⋀ ⌊[shift m 0 <$> Φ]⌋ ∧ ⋀ ⌊[shift m 0 <$> Φ']⌋ ⟺
    fshift m 0 (⋀ ⌊[Φ]⌋ ∧ ⋀ ⌊[Φ']⌋)).
  { rewrite /= fshift_And fshift_And.
    apply proper_and;
    apply proper_And; rewrite -list_fmap_compose;
    apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=;
    by rewrite fshift_shift. }
  rewrite H.
  rewrite nexists_and_switch_r.
  eqd.
Qed.

Lemma coepis Φ :
  ⟦Φ⟧ ⟺
  ⟦⫐ [0 ⋅ Φ]⟧.
Proof.
  by rewrite /interp/= true_imp_l true_and false_or.
Qed.

Lemma pet γ Δ Δ' :
  ⟦γ ⫐ Δ ++ [∅] ++ Δ'⟧ ⟺
  ⟦[]⟧.
Proof.
  rewrite /interp/=. case γ => [m Ψ].
  rewrite cons_app; repeat rewrite fmap_app. rewrite fmap_singl.
  repeat rewrite Or_app /=.
  rewrite or_assoc true_or or_comm true_or true_imp_r true_nforall.
  eqd.
Qed.

Lemma ipis i t n Φ Δ :
  0 <= i <= n ->
  ⟦S n ⋅ Φ ⫐ Δ⟧ ⟺
  ⟦[(n ⋅ unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ) ⫐
    gunshift 1 i <$> (gsubst i (Terms.tshift (S n) 0 t) <$> Δ)); S n ⋅ Φ ⫐ Δ]⟧.
Proof.
  intros Hi.
  rewrite /interp/= true_and.
  eqd.
  * rewrite nforall_one nforall_add.
    assert (H : 1 + n = S n); first lia; rewrite H; clear H.
    set A := ⋀ ⌊[Φ]⌋ ⊃ ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊[Ψ]⌋) <$> Δ).
    assert (H :
      funshift 1 i (fsubst i (Terms.tshift (S n) 0 t) A) ⟺
      ⋀ ⌊[unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ)]⌋
       ⊃ ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊[Ψ]⌋) <$>
            (gunshift 1 i <$> (gsubst i (Terms.tshift (S n) 0 t) <$> Δ)))).
    { rewrite /A/=.
      rewrite fsubst_And funshift_And.
      rewrite fsubst_Or funshift_Or.
      apply proper_imp.
      * apply proper_And.
        do 2 rewrite -list_fmap_compose.
        apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=.
        by rewrite fsubst_subst funshift_unshift.
      * apply proper_Or.
        do 2 rewrite -list_fmap_compose.
        apply Forall_equiv_map; apply equiv_Forall; move => [k Ψ] /=.
        rewrite fsubst_nexists funshift_nexists.
        rewrite fsubst_And funshift_And.
        apply proper_nexists; auto; apply proper_And.
        do 2 rewrite -list_fmap_compose.
        apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=.
        by rewrite fsubst_subst funshift_unshift. }
    rewrite -H.
    by apply nforall_elim.
  * pweak 0. rewrite /=.
    pfaL 0 (Terms.TVar 0).
    rewrite fsubst_fshift funshift_fshift.
    passum.
Qed.

Lemma ipet i t n Φ γ Δ Δ' :
  0 <= i <= n ->
  ⟦γ ⫐ Δ ++ [S n ⋅ Φ] ++ Δ'⟧ ⟺
  ⟦γ ⫐ Δ ++ [n ⋅ unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ); S n ⋅ Φ] ++ Δ'⟧.
Proof.
  intros Hi.
  rewrite /interp/= true_and true_and. case: γ => [m Ψ].
  apply proper_nforall; auto; apply proper_imp; auto.
  rewrite cons_app [(n ⋅ _) :: _]cons_app. repeat rewrite fmap_app.
  repeat rewrite Or_app.
  apply proper_or; auto.
  rewrite or_assoc.
  apply proper_or; auto.
  split. pright. isrch. rewrite false_or.
  rewrite nexists_one nexists_add -[1 + n]/(S n).
  assert (H :
    funshift 1 i (fsubst i (Terms.tshift (S n) 0 t) ⋀ ⌊[Φ]⌋) ⟺
    ⋀ ⌊[unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ)]⌋).
  { rewrite fsubst_And funshift_And.
    apply proper_And.
    do 2 rewrite -list_fmap_compose.
    apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=.
    by rewrite fsubst_subst funshift_unshift. }
  rewrite -H.
  by apply nexists_intro.
Qed.

Lemma local_soundness : ∀ (Φ Ψ : bouquet),
  Φ ⇀ Ψ -> ⟦Φ⟧ ⟺ ⟦Ψ⟧.
Proof.
  move => x y.
  elim; clear x y; intros.

  (* Pollination *)

  * by apply pollination.
  * symmetry. by apply pollination.

  (* Empty pistil *)

  * by apply epis_pis.
  * by apply epis_pet.
  * by apply coepis.

  (* Empty petal *)

  * by apply pet.

  (* Reproduction *)

  * by apply reproduction.

  (* Instantiation *)

  * by apply ipis.
  * by apply ipet.
Qed.

Theorem soundness Φ Ψ :
  Φ ~>* Ψ -> ⟦Φ⟧ ⟺ ⟦Ψ⟧.
Proof.
  elim => {Φ Ψ} [Φ |Φ1 Φ2 Φ3 Hstep H IH] //.
  rewrite -IH. elim: Hstep => X Φ Ψ Hstep.
  apply grounding. by apply local_soundness.
Qed.

(** Soundness of structural rules *)

Lemma grow : ∀ (P : pctx) Φ,
  [⟦P ⋖ Φ⟧] ⟹ ⟦P ⋖ []⟧.
Admitted.

Theorem ssoundness Φ Ψ :
  Φ ≈>* Ψ -> [⟦Ψ⟧] ⟹ ⟦Φ⟧.
Admitted.

(** * Completeness *)

Reserved Notation "⌈ A ⌉" (format "⌈ A ⌉", at level 0).

Fixpoint finterp (A : form) : bouquet :=
  match A with
  | FAtom p args => Atom p args
  | ⊤ => []
  | ⊥ => ∅ ⫐
  | A ∧ B => ⌈A⌉ ++ ⌈B⌉
  | A ∨ B => ⫐ [0 ⋅ ⌈A⌉; 0 ⋅ ⌈B⌉]
  | A ⊃ B => 0 ⋅ ⌈A⌉ ⫐ [0 ⋅ ⌈B⌉]
  | #∀ A => 1 ⋅ [] ⫐ [0 ⋅ ⌈A⌉]
  | #∃ A => ⫐ [1 ⋅ ⌈A⌉]
  end
where "⌈ A ⌉" := (finterp A).

Definition cinterp Γ := A ← Γ; ⌈A⌉.

Notation "⌈[ Γ ]⌉" := (cinterp Γ).

Lemma finterp_And : ∀ (Γ : list form),
  ⌈⋀ Γ⌉ = ⌈[Γ]⌉.
Proof.
  elim => [|A Γ IH] //=. by rewrite IH.
Qed.

Lemma shift_fshift : forall C n c,
  shift n c <$> ⌈C⌉ = ⌈fshift n c C⌉.
Proof.
  elim/form_induction =>
    [|||A B IHA IHB |A B IHA IHB |A B IHA IHB |A IHA |A IHA] n c //=;
  try repeat rewrite Nat.add_0_r;
  try rewrite fmap_app;
  try by rewrite IHA IHB /=.
  by rewrite IHA.
  by rewrite IHA.
Qed.

Lemma bshift_fshift : forall Γ n c,
  shift n c <$> ⌈[Γ]⌉ = ⌈[fshift n c <$> Γ]⌉.
Proof.
  elim => [|A Γ IH] n c //.
  rewrite /cinterp bind_cons fmap_cons fmap_app bind_cons.
  by rewrite shift_fshift IH.
Qed.

Lemma unshift_funshift : forall C n c,
  unshift n c <$> ⌈C⌉ = ⌈funshift n c C⌉.
Proof.
  elim/form_induction =>
    [|||A B IHA IHB |A B IHA IHB |A B IHA IHB |A IHA |A IHA] n c //=;
  try repeat rewrite Nat.add_0_r;
  try rewrite fmap_app;
  try by rewrite IHA IHB /=.
  by rewrite IHA.
  by rewrite IHA.
Qed.

Lemma bunshift_funshift : forall Γ n c,
  unshift n c <$> ⌈[Γ]⌉ = ⌈[funshift n c <$> Γ]⌉.
Proof.
  elim => [|A Γ IH] n c //.
  rewrite /cinterp bind_cons fmap_cons fmap_app bind_cons.
  by rewrite unshift_funshift IH.
Qed.

Lemma subst_fsubst : forall C i t,
  subst i t <$> ⌈C⌉ = ⌈fsubst i t C⌉.
Proof.
  elim/form_induction =>
    [|||A B IHA IHB |A B IHA IHB |A B IHA IHB |A IHA |A IHA] n c //=;
  try repeat rewrite Nat.add_0_r;
  try repeat rewrite Terms.tshift_zero;
  try rewrite fmap_app;
  try by rewrite IHA IHB //=.
  by rewrite IHA.
  by rewrite IHA.
Qed.

Lemma bsubst_fsubst : forall Γ i t,
  subst i t <$> ⌈[Γ]⌉ = ⌈[fsubst i t <$> Γ]⌉.
Proof.
  elim => [|A Γ IH] n c //.
  rewrite /cinterp bind_cons fmap_cons fmap_app bind_cons.
  by rewrite subst_fsubst IH.
Qed.

Definition is_shifted (n : nat) (A : form) : Prop :=
  exists B, A = fshift n 0 B.

Lemma is_shifted_zero A :
  is_shifted 0 A.
Proof.
  exists A. by rewrite fshift_zero.
Qed.

Lemma is_shifted_bshift_unshift n A :
  is_shifted n A ->
  shift n 0 <$> (unshift n 0 <$> ⌈A⌉) = ⌈A⌉.
Proof.
  move => H.
  rewrite unshift_funshift shift_fshift.
  case: H => [B H]; by rewrite H funshift_fshift.
Qed.

Definition subctx (Γ : list form) (X : ctx) : Prop :=
  forall D, D ∈ Γ -> exists n, is_shifted n D /\ nassum n ⌈D⌉ X.

Infix "⪽" := subctx (at level 70).

Lemma subctx_nil X :
  [] ⪽ X.
Proof.
  red. move => D HD. inv HD.
Qed.

Lemma subctx_comp_out Γ X Y :
  Γ ⪽ X ->
  (fshift (bv Y) 0 <$> Γ) ⪽ X ⪡ Y.
Proof.
  rewrite /subctx.
  move => H D HD.
  apply elem_of_map in HD.
  case: HD => [E [HE1 HE2]].
  case (H E HE1) => m [Hshift Hassum].
  exists (m + bv Y). split.
  { red. case: Hshift => F ?; subst.
    exists F. by rewrite -fshift_add Nat.add_comm. }
  pose proof (Hass := nassum_comp_out _ _ X Y Hassum).
  rewrite HE2 -shift_fshift.
  by rewrite /= in Hass.
Qed.

Ltac subctxout H :=
  match goal with
  | |- _ ⪽ _ ⪡ ?Y =>
      let Hsub := fresh "Hsub" in
      pose proof (Hsub := subctx_comp_out _ _ Y H);
      rewrite /= in Hsub;
      repeat rewrite fmap_app in Hsub;
      repeat rewrite cshift_zero in Hsub;
      done
  end.

Lemma subctx_comp_in Γ X Y :
  Γ ⪽ Y ->
  Γ ⪽ X ⪡ Y.
Proof.
  rewrite /subctx.
  move => H D HD.
  case (H D HD) => n [Hs Ha].
  exists n. split; auto.
  by apply nassum_comp_in.
Qed.

Lemma subctx_subset Γ Γ' X :
  Γ ⊆ Γ' -> Γ' ⪽ X -> Γ ⪽ X.
Proof.
  rewrite /subctx.
  move => Hsubset H D HD.
  case (H D (Hsubset D HD)) => n Ha.
  by exists n.
Qed.

Lemma subctx_app Γ Γ' X :
  Γ ⪽ X -> Γ' ⪽ X ->
  (Γ ++ Γ') ⪽ X.
Proof.
  rewrite /subctx.
  move => H H' D HD.
  decompose_elem_of_list.
  * case (H D H0) => n Ha. by exists n.
  * case (H' D H0) => n Ha. by exists n.
Qed.

Global Instance subctx_Permutation :
  Proper ((≡ₚ) ==> (=) ==> (↔)) (subctx).
Proof.
  repeat red. move => Γ Γ' Hperm X Y Heq; subst.
  rewrite /subctx. split; move => H D HD.
  * rewrite -Hperm in HD. by apply H.
  * rewrite Hperm in HD. by apply H.
Qed.

Lemma move_cons_right {A} (l l' : list A) (x : A) :
  l ++ x :: l' ≡ₚ (l ++ l') ++ [x].
Proof.
  by solve_Permutation.
Qed.

Lemma subctx_petal_skip A X γ Δ Δ' :
  [A] ⪽ X ->
  [A] ⪽ Petal γ Δ 0 X Δ'.
Proof.
  move => H.
  by apply (subctx_comp_in _ (Petal γ Δ 0 □ Δ') _ H).
Qed.

Lemma subctx_petal A n Φl Φr Δ Δ' :
  [A] ⪽ Petal (n ⋅ Φl ++ ⌈A⌉ ++ Φr) Δ 0 □ Δ'.
Proof.
  move => D HD. inv HD; [> |inv H1].
  exists 0. split; [> by apply is_shifted_zero |].
  red. rewrite bunshift_zero.
  exists □. exists (Petal (n ⋅ Φl ++ ⌈A⌉ ++ Φr) Δ 0 □ Δ').
  split; auto.
  epose proof (Hp := P_self _ □ _ Φl Φr _ 0 _).
  eapply Hp.
Qed.

Ltac subctxpet Φl Φr Δ Δ' :=
  let Hs := fresh "Hs" in
  epose proof (Hs := subctx_petal _ _ Φl Φr Δ Δ');
  list_simplifier; eapply Hs.

Theorem deep_completeness Γ C :
  Γ s⟹ C -> forall X, Γ ⪽ X ->
  X ⋖ ⌈C⌉ ~>* X ⋖ [].
Proof.
  elim =>/= {Γ C} [
    A Γ Γ'
  | A Γ Γ' Γ'' C _ IH1
  | A Γ Γ' Γ'' C _ IH1
  | Γ
  | A B Γ _ IH1 _ IH2
  | A B Γ _ IH1
  | A B Γ _ IH1
  | A B Γ _ IH1
  | Γ C _ IH1
  | t Γ C _ IH1
  | Γ Γ' C _ IH1
  | Γ Γ' C
  | A B Γ Γ' C _ IH1
  | A B Γ Γ' C _ IH1 _ IH2
  | A B Γ Γ' C _ IH1 _ IH2
  | A t Γ Γ' C _ IH1
  | A Γ Γ' C _ IH1
  ] X H.

  Ltac applyIH IH X X0 :=
    specialize (IH (X ⪡ X0));
    repeat rewrite -fill_comp /= in IH;
    etransitivity; [> apply IH |].

  Ltac bypet Δ Δ' :=
    repeat rewrite fill_comp; eapply cstep_congr;
    rpetm (@nil nat) Δ Δ';
    reflexivity.

  Ltac pull_hyp H A C Γ Γ' :=
    assert (HA : A ∈ (Γ ++ A :: Γ')); [> solve_elem_of_list |];
    let Y := fresh "Y" in
    let Z := fresh "Z" in
    let Hpol := fresh "Hpol" in
    let Hshifted := fresh "Hshifted" in
    case (H A HA) => [n [Hshifted [Y [Z [Hpol Hcomp]]]]]; subst;
    estep; [> eapply R_ctx; eapply R_coepis |];
    repeat rewrite -fill_comp;
    estep; [>
      eapply R_ctx;
      let Z0 := constr:(Pistil 0 □ [0 ⋅ ⌈C⌉]) in
      let Hpol' := fresh "Hpol'" in
      let Hp := fresh "Hp" in
      epose proof (Hpol' := pollin_comp_out _ _ _ Z0 Hpol);
      rewrite /= Nat.add_0_r in Hpol';
      epose proof (Hp := R_copol _ _ (Z ⪡ Z0) Hpol');
      rewrite -fill_comp /= in Hp;
      eapply Hp
    |];
    let Hs := fresh "Hs" in
    pose proof (Hs := is_shifted_bshift_unshift _ _ Hshifted);
    rewrite /= in Hs; try rewrite Hs; clear Hs;
    repeat rewrite -fill_comp /=;

    assert (Hsubctx : (Γ ++ Γ') ⪽ Y ⪡ Z); [>
      eapply subctx_subset; [> |eapply H];
      apply proper_app_subseteq; auto;
      by apply list_subseteq_cons |].

  (* Axiom *)
  * assert (Hprem : A ∈ (Γ ++ A :: Γ')).
    { solve_elem_of_list. }
    elim (H A Hprem) => n [[B ?] [Y [Z [Hpol Hcomp]]]]; subst.
    rewrite -shift_fshift in Hpol |- *.
    pose proof (Hs := bunshift_shift 0 n 0 ⌈B⌉).
    rewrite bunshift_zero /= in Hs. rewrite Hs in Hpol.
    pose proof (Hp := R_pol _ _ _ Hpol).
    rewrite -fill_comp -fill_comp; apply cstep_congr.
    apply rtc_once. rself.
    exact Hp.

  (* Right contraction *)
  * apply IH1. red. intros. apply H.
    decompose_elem_of_list; solve_elem_of_list.

  (* Left contraction *)
  * apply IH1. red. intros. apply H.
    decompose_elem_of_list; solve_elem_of_list.

  (* R⊤ *)
  * reflexivity.

  (* R∧ *)
  * applyIH IH1 X (Planter [] □ ⌈B⌉).
    subctxout H.
    by apply IH2.

  (* R∨₁ *)
  * applyIH IH1 X (Petal ∅ [] 0 □ [0 ⋅ ⌈B⌉]).
    subctxout H.
    bypet (@nil garden) [0 ⋅ ⌈B⌉].

  (* R∨₁ *)
  * applyIH IH1 X (Petal ∅ [0 ⋅ ⌈A⌉] 0 □ []).
    subctxout H.
    bypet [0 ⋅ ⌈A⌉] (@nil garden).

  (* R⊃ *) 
  * applyIH IH1 X (Petal (0 ⋅ ⌈A⌉) [] 0 □ []).
    { rewrite cons_app. apply subctx_app.
      * apply subctx_comp_in.
        subctxpet (@nil flower) (@nil flower) (@nil garden) (@nil garden).
      * subctxout H. }
    bypet (@nil garden) (@nil garden).

  (* R∀ *)
  * applyIH IH1 X (Petal (1 ⋅ []) [] 0 □ []).
    subctxout H.
    bypet (@nil garden) (@nil garden).

  (* R∃ *)
  * estep.
    { eapply R_ctx.
      epose proof (Hipet := R_ipet 0 t 0 _ _ [] []); list_simplifier.
      eapply Hipet. lia. }
    rewrite subst_fsubst unshift_funshift.

    applyIH IH1 X (Petal ∅ [] 0 □ [1 ⋅ ⌈C⌉]).
    subctxout H.
    bypet (@nil garden) [1 ⋅ ⌈C⌉].

  (* L⊤ *)
  * pull_hyp H ⊤ C Γ Γ'.

    applyIH IH1 (Y ⪡ Z) (Petal ∅ [] 0 □ []).
    { subctxout Hsubctx. }

    bypet (@nil garden) (@nil garden).

  (* L⊥ *)
  * pull_hyp H ⊥ C Γ Γ'.

    etransitivity. rewrite fill_comp. eapply cstep_congr.
    rewrite /ftob. rrep (@nil flower) (@nil flower). reflexivity.

    rewrite /=.
    bypet (@nil garden) (@nil garden).

  (* L∧ *)
  * pull_hyp H (A ∧ B) C Γ Γ'.

    applyIH IH1 (Y ⪡ Z) (Petal (0 ⋅ ⌈A⌉ ++ ⌈B⌉) [] 0 □ []).
    { rewrite move_cons_right [_ ++ B :: _]move_cons_right.
      apply subctx_app. apply subctx_app.
      subctxout Hsubctx.
      apply subctx_comp_in.
      subctxpet ⌈A⌉ (@nil flower) (@nil garden) (@nil garden).
      apply subctx_comp_in.
      subctxpet (@nil flower) ⌈B⌉ (@nil garden) (@nil garden). }

    bypet (@nil garden) (@nil garden).

  (* L∨ *)
  * pull_hyp H (A ∨ B) C Γ Γ'.

    etransitivity. rewrite fill_comp. eapply cstep_congr.
    rewrite /ftob. rrep (@nil flower) (@nil flower). reflexivity.

    rewrite /= bshift_zero.
    rewrite -fill_comp.
    applyIH IH1 (Y ⪡ Z) (Petal ∅ [] 0 (Planter [] (Petal (0 ⋅ ⌈A⌉) [] 0 □ []) [0 ⋅ ⌈B⌉ ⫐ [0 ⋅ ⌈C⌉]]) []).
    { rewrite move_cons_right. apply subctx_app.
      subctxout Hsubctx.
      apply subctx_comp_in.
      apply (subctx_comp_in _ (Petal ∅ [] 0 □ [])).
      apply (subctx_comp_in _ (Planter [] □ _)).
      subctxpet (@nil flower) (@nil flower) (@nil garden) (@nil garden). }

    etransitivity. rewrite fill_comp. eapply cstep_congr.
    rpetm [0;1;0] (@nil garden) (@nil garden). reflexivity.

    rewrite -fill_comp.
    applyIH IH2 (Y ⪡ Z) (Petal ∅ [] 0 (Petal (0 ⋅ ⌈B⌉) [] 0 □ []) []).
    { rewrite move_cons_right. apply subctx_app.
      subctxout Hsubctx.
      apply subctx_comp_in.
      apply (subctx_comp_in _ (Petal ∅ [] 0 □ [])).
      subctxpet (@nil flower) (@nil flower) (@nil garden) (@nil garden). }

    repeat rewrite fill_comp. apply cstep_congr.
    rpetm [0;1;0] (@nil garden) (@nil garden).
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* L⊃ *)
  * pull_hyp H (A ⊃ B) C Γ Γ'.

    applyIH IH1 (Y ⪡ Z) (Pistil 0 (Pistil 0 □ [0 ⋅ ⌈B⌉]) [0 ⋅ ⌈C⌉]).
    { subctxout Hsubctx. }

    etransitivity. rewrite fill_comp. eapply cstep_congr.
    repispis 0 0 (@nil flower) (@nil flower). reflexivity.

    rewrite -fill_comp.
    applyIH IH2 (Y ⪡ Z) (Petal (0 ⋅ ⌈B⌉) [] 0 □ []).
    { rewrite move_cons_right. apply subctx_app.
      subctxout Hsubctx.
      apply subctx_comp_in.
      subctxpet (@nil flower) (@nil flower) (@nil garden) (@nil garden). }

    bypet (@nil garden) (@nil garden).

  (* L∀ *)
  * pull_hyp H (#∀ A) C Γ Γ'.

    estep; [> rewrite fill_comp |].
    { set X0 := Pistil 0 □ [0 ⋅ ⌈C⌉].
      epose proof (Hctx := fill_comp _ X0 _).
      rewrite /= in Hctx. rewrite /ftob.
      erewrite Hctx. eapply R_ctx.
      epose proof (Hipis := R_ipis 0 t 0 _ _).
      eapply Hipis. lia. }
    rewrite -fill_comp/= Terms.tshift_zero subst_fsubst unshift_funshift.

    etransitivity. eapply cstep_congr.
    repispis 0 0 (@nil flower) [1 ⋅ [] ⫐ [0 ⋅ ⌈A⌉]]. reflexivity.

    set iA := funshift 1 0 (fsubst 0 (Terms.tshift 1 0 t) A) in IH1 |- *.
    set X0 := Petal (0 ⋅ ⌈iA⌉ ++ [1 ⋅ [] ⫐ [0 ⋅ ⌈A⌉]]) [] 0 □ [].
    rewrite -fill_comp.
    applyIH IH1 (Y ⪡ Z) X0.
    { rewrite move_cons_right. apply subctx_app.
      subctxout Hsubctx.
      apply subctx_comp_in.
      subctxpet (@nil flower) [1 ⋅ [] ⫐ [0 ⋅ ⌈A⌉]] (@nil garden) (@nil garden). }

    bypet (@nil garden) (@nil garden).

  (* L∃ *)
  * pull_hyp H (#∃ A) C Γ Γ'.

    repeat rewrite fill_comp. etransitivity. apply cstep_congr.
    repispis 0 1 (@nil flower) (@nil flower). reflexivity.

    rewrite shift_fshift -fill_comp.
    applyIH IH1 (Y ⪡ Z) (Petal (1 ⋅ ⌈A⌉) [] 0 □ []).
    { rewrite move_cons_right. apply subctx_app.
      subctxout Hsubctx.
      apply subctx_comp_in.
      subctxpet (@nil flower) (@nil flower) (@nil garden) (@nil garden). }

    bypet (@nil garden) (@nil garden).
Qed.

Lemma elem_of_cons_app {A} : forall (l : list A) x,
  x ∈ l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  elim => [|y l IH] x H; inv H.
  * by exists []; exists l.
  * case (IH x H2) => [l1' [l2' H']].
    rewrite H'.
    by exists (y :: l1'); exists l2'.
Qed.

Lemma elem_of_finterp A Γ :
  A ∈ Γ -> exists Φl Φr, ⌈⋀ Γ⌉ = Φl ++ ⌈A⌉ ++ Φr.
Proof.
  move => H.
  case (elem_of_cons_app _ _ H) => [Γ1 [Γ2 HΓ]].
  rewrite HΓ finterp_And /cinterp bind_app bind_cons.
  by exists ⌈[Γ1]⌉; exists ⌈[Γ2]⌉.
Qed.

Theorem completeness Γ C :
  Γ s⟹ C ->
  ⌈⋀ Γ ⊃ C⌉ ~>* [].
Proof.
  move => H.
  pose proof (Hfc := deep_completeness _ _ H (Petal (0 ⋅ ⌈⋀ Γ⌉) [] 0 □ [])).
  rewrite /= in Hfc |- *.
  etransitivity; [> eapply Hfc |].
  { move => D HD.
    case (elem_of_finterp _ _ HD) => [Φl [Φr HΓ]].
    exists 0. split; [> by apply is_shifted_zero |].
    red. rewrite bunshift_zero.
    exists □. exists (Petal (0 ⋅ ⌈⋀ Γ⌉) [] 0 □ []). split; auto.
    rewrite HΓ.
    epose proof (Hp := P_self _ □ 0 Φl Φr [] 0 []); list_simplifier.
    eapply Hp. }
  rpetm (@nil nat) (@nil garden) (@nil garden).
  reflexivity.
Qed.

(** ** Admissibility of structural rules *)

(** Currently structural rules only comprise the grow rule, but the above
    completeness proof entails admissibility of any imaginable sound rule,
    like the fall (weakening) rule or permutations for gardens and petals. *)

Lemma finterp_interp Φ :
  ⌈⟦Φ⟧⌉ = ⌈[⌊[Φ]⌋]⌉.
Proof.
  by rewrite /interp/= finterp_And.
Qed.

Lemma interp_weak_iso : forall (Φ : bouquet),
  ⌈[⌊[Φ]⌋]⌉ ≡ Φ.
Proof.
Admitted.

Add Morphism cinterp with signature
  Forall2 eqderiv ==> eqprov
  as proper_cinterp_eqprov.
Proof.
  move => Γ Γ' H.
  split; rewrite /prov; intro Hp.
Admitted.

Add Morphism prov with signature
  eqprov ==> iff
  as proper_prov_eqprov.
Admitted.

Lemma interp_entails Φ Ψ :
  ⌈⟦Φ⟧⌉ ⊢ ⌈⟦Ψ⟧⌉ ->
  Φ ⊢ Ψ.
Proof.
  move => H.
  pose proof (Hiso := interp_weak_iso (0 ⋅ Φ ⫐ [0 ⋅ Ψ])).
  rewrite [⌊[_]⌋]/= false_or/= finterp_And finterp_And in Hiso.
  repeat rewrite finterp_interp in H. red in H.
  rewrite /ftob Hiso in H.
  apply deduction in H.
  by apply deduction.
Qed.

Theorem structural_admissibility Φ Ψ :
  Φ ⊩ Ψ -> Φ ⊢ Ψ.
Proof.
  move => H. red in H.
  apply ssoundness in H.
  rewrite /interp/= true_and false_or in H.
  apply Semantics.structural_admissibility in H.
  apply completeness in H. rewrite /= in H.
  apply deduction in H.
  by apply interp_entails.
Qed.

(** * Semantical adequation *)

(** This is the more standard model-theoretical formulation of
    soundness/completeness. It allows to dispense with the semantics -> syntax
    translation [finterp] from formulas to flowers in the statement, and
    ensures that it is the weak inverse of the syntax -> semantics
    interpretation [interp].

    By weak inverse, we mean that we have only an equivalence instead of an
    equality between ⌈⌊Φ⌋⌉ and Φ. We conjecture that syntactic equivalence
    holds, i.e. ⌈⌊Φ⌋⌉ ⊣⊢ Φ, but this cannot make sense without admissibility of
    the grow rule, which is a priori necessary for transitivity of ⊣⊢ (and also
    to prove that ⊣⊢ implies equiprovability).

    Instead we rely on semantic equivalence Φ ⫤⊨ Ψ, the fact that [interp] is a
    weak inverse of [finterp] in the sense of equiderivability in sequent
    calculus, and cut admissibility. *)

Definition mentails (Φ Ψ : bouquet) := [⟦Φ⟧] ⟹ ⟦Ψ⟧.
Infix "⊨" := mentails (at level 70).

Definition eqmentails Φ Ψ := Φ ⊨ Ψ /\ Ψ ⊨ Φ.
Infix "⫤⊨" := eqmentails (at level 70).

Lemma finterp_weak_iso (A : form) :
  ⟦⌈A⌉⟧ ⟺ A.
Admitted.

Lemma eqmentails_eqderiv Φ Ψ :
  Φ ⫤⊨ Ψ <-> (⟦Φ⟧ ⟺ ⟦Ψ⟧).
Proof.
  by rewrite /eqmentails/mentails/eqderiv.
Qed.

Lemma finterp_interp_eqmentails Φ :
  Φ ⫤⊨ ⌈⟦Φ⟧⌉.
Proof.
  by rewrite eqmentails_eqderiv finterp_weak_iso.
Qed.

(** Weak provability *)
Definition wprov Φ := exists Ψ, Ψ ~>* [] /\ Φ ⫤⊨ Ψ.

Definition mtrue Φ := ⟦Φ⟧ ⟺ ⊤.

Lemma interp_void :
  ⟦[]⟧ = ⊤.
Proof.
  done.
Qed.

Theorem weak_adequation Φ :
  wprov Φ <-> mtrue Φ.
Proof.
  rewrite /wprov/mtrue. split; move => H.

  (* Soundness *)
  * move: H => [Ψ [Hprov Heqm]].
    rewrite eqmentails_eqderiv in Heqm.
    rewrite Heqm -interp_void.
    by apply soundness.

  (* Completeness *)
  * exists ⌈⟦Φ⟧⌉. split.
    - pose proof (Hc := completeness [] ⟦Φ⟧).
      rewrite /= in Hc.
      estep. rself. apply R_coepis.
      apply Hc.
      apply Semantics.structural_admissibility.
      rewrite H.
      isrch.
    - by apply finterp_interp_eqmentails.
Qed.

Theorem weak_structural_admissibility Φ :
  [] ⊩ Φ -> wprov Φ.
Proof.
  move => H.
  apply ssoundness in H.
  apply weak_adequation.
  rewrite /interp/= true_and false_or true_imp_l in H.
  by split; [> isrch |].
Qed.

Theorem adequation Φ Ψ :
  Φ ⊢ Ψ <-> Φ ⊨ Ψ.
Proof.
  split; move => H.

  (* Soundness *)
  * apply soundness in H.
    rewrite /interp/= true_and false_or in H.
    apply Semantics.deduction.
    rewrite H. isrch.

  (* Completeness *)
  * apply Semantics.structural_admissibility in H.
    apply completeness in H. rewrite /= in H. list_simplifier.
    by apply interp_entails.
Qed.