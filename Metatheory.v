Require Import stdpp.list stdpp.relations.
Require Import ssreflect.

Require Import Flowers.Syntax Flowers.Semantics Flowers.Utils.

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
  set f := λ δ : garden, fshift n (c + m) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋.
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
  set f := λ δ : garden, funshift n (c + m) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋.
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
  set f := λ δ : garden, fsubst (n + m) (Terms.tshift m 0 t) (let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋).
  set g := λ δ : garden, let 'm0 ⋅ Ψ := δ in m0#∃ ⋀ ⌊⌊Ψ⌋⌋.
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

Lemma wpol X : ∀ (Ψ : bouquet),
  ⟦Ψ⟧ ∧ ⟦X ⋖ (shift (bv X) 0 <$> Ψ)⟧ ⟺
  ⟦Ψ⟧ ∧ ⟦X ⋖ []⟧.
Proof.
  induction X; intro;
  rewrite /interp//=;
  repeat rewrite true_and.
  * rewrite bshift_zero. eqd.
  * repeat rewrite fmap_app And_app.
    rewrite and_assoc [(⋀ ⌊⌊Ψ⌋⌋) ∧ _]and_comm and_assoc -[(_ ∧ ⋀ ⌊⌊Ψ⌋⌋) ∧ _]and_assoc.
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
    rewrite [⋀ ⌊⌊Ψ⌋⌋ ∧ _]and_comm.
    repeat rewrite [⋀ ⌊⌊Φ⌋⌋ ∧ _]and_assoc.
    repeat rewrite [_ ∧ ⋀ ⌊⌊Ψ⌋⌋ ⊃ _]currying.
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
    rewrite [⋀ ⌊⌊Φ⌋⌋ ∧ _]and_comm.
    rewrite -[_ ∧ ⋀ ⌊⌊Φ⌋⌋]and_assoc.
    repeat rewrite [_ ∧ ⋀ ⌊⌊Ψ⌋⌋ ∧ _]and_assoc.
    apply proper_and; auto.
    repeat rewrite [_ ∧ ⋀ ⌊⌊Ψ⌋⌋]and_comm.
    by rewrite wpol.
  * rewrite /interp. list_simplifier.
    repeat rewrite And_app.
    apply proper_and; auto.
    repeat rewrite and_assoc.
    apply proper_and; auto.
    rewrite [_ ∧ ⋀ ⌊⌊Φ'⌋⌋]and_comm.
    rewrite -and_assoc -and_assoc.
    apply proper_and; auto.
    by rewrite wpol.
Qed.

Lemma reproduction (Δ : list garden) n (Φ Φ' : bouquet) (Δ' : list garden) :
  ⟦n ⋅ Φ ++ [⊢ Δ] ++ Φ' ⊢ Δ'⟧ ⟺
  ⟦n ⋅ Φ ++ Φ' ⊢ [0 ⋅ (λ '(m ⋅ Ψ), m ⋅ Ψ ⊢ gshift m 0 <$> Δ') <$> Δ]⟧.
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
    fshift k 0 ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊⌊Ψ⌋⌋) <$> Δ') ⟺
    ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊⌊Ψ⌋⌋) <$> (gshift k 0 <$> Δ'))).
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
  ⟦n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' ⊢ Δ⟧ ⟺
  ⟦n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ') ⊢ gshift m 0 <$> Δ⟧.
Proof.
  rewrite /interp/= true_and true_and.
  rewrite -nforall_add.
  apply proper_nforall; auto.
  rewrite cons_app; repeat rewrite fmap_app.
  repeat rewrite And_app.
  rewrite fmap_singl And_singl /= true_imp_l false_or.
  rewrite [m#∃ _ ∧ _]and_comm and_assoc currying.
  rewrite nexists_intro_l.
  rewrite [⋀ ⌊⌊Ψ⌋⌋ ∧ _]and_comm and_assoc [_ ∧ ⋀ ⌊⌊Ψ⌋⌋ ⊃ _]currying.
  assert (H :
    ⋀ ⌊⌊shift m 0 <$> Φ⌋⌋ ∧ ⋀ ⌊⌊shift m 0 <$> Φ'⌋⌋ ⟺
    fshift m 0 (⋀ ⌊⌊Φ⌋⌋ ∧ ⋀ ⌊⌊Φ'⌋⌋)).
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
  ⟦γ ⊢ Δ ++ [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'] ++ Δ'⟧ ⟺
  ⟦γ ⊢ Δ ++ [n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ')] ++ Δ'⟧.
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
  rewrite [⋀ ⌊⌊Ψ⌋⌋ ∧ _]and_comm [⋀ ⌊⌊shift m 0 <$> Φ⌋⌋ ∧ _]and_assoc.
  assert (H :
    ⋀ ⌊⌊shift m 0 <$> Φ⌋⌋ ∧ ⋀ ⌊⌊shift m 0 <$> Φ'⌋⌋ ⟺
    fshift m 0 (⋀ ⌊⌊Φ⌋⌋ ∧ ⋀ ⌊⌊Φ'⌋⌋)).
  { rewrite /= fshift_And fshift_And.
    apply proper_and;
    apply proper_And; rewrite -list_fmap_compose;
    apply Forall_equiv_map; apply equiv_Forall; move => ϕ /=;
    by rewrite fshift_shift. }
  rewrite H.
  rewrite nexists_and_switch_r.
  eqd.
Qed.

Lemma pet γ Δ Δ' :
  ⟦γ ⊢ Δ ++ [∅] ++ Δ'⟧ ⟺
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
  ⟦S n ⋅ Φ ⊢ Δ⟧ ⟺
  ⟦[(n ⋅ unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ) ⊢
    gunshift 1 i <$> (gsubst i (Terms.tshift (S n) 0 t) <$> Δ)); S n ⋅ Φ ⊢ Δ]⟧.
Proof.
  intros Hi.
  rewrite /interp/= true_and.
  eqd.
  * rewrite nforall_one nforall_add.
    assert (H : 1 + n = S n); first lia; rewrite H; clear H.
    set A := ⋀ ⌊⌊Φ⌋⌋ ⊃ ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊⌊Ψ⌋⌋) <$> Δ).
    assert (H :
      funshift 1 i (fsubst i (Terms.tshift (S n) 0 t) A) ⟺
      ⋀ ⌊⌊unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ)⌋⌋
       ⊃ ⋁ ((λ '(m ⋅ Ψ), m#∃ ⋀ ⌊⌊Ψ⌋⌋) <$>
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
  ⟦γ ⊢ Δ ++ [S n ⋅ Φ] ++ Δ'⟧ ⟺
  ⟦γ ⊢ Δ ++ [n ⋅ unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ); S n ⋅ Φ] ++ Δ'⟧.
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
    funshift 1 i (fsubst i (Terms.tshift (S n) 0 t) ⋀ ⌊⌊Φ⌋⌋) ⟺
    ⋀ ⌊⌊unshift 1 i <$> (subst i (Terms.tshift (S n) 0 t) <$> Φ)⌋⌋).
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
  * symmetry; by apply pollination.

  (* Empty pistil *)

  * by apply epis_pis.
  * by apply epis_pet.
  * symmetry. by apply epis_pis.
  * symmetry. by apply epis_pet.

  (* Empty petal *)

  * by apply pet.

  (* Reproduction *)

  * by apply reproduction.

  (* Instantiation *)

  * by apply ipis.
  * by apply ipet.
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

Theorem soundness : ∀ Φ Ψ,
  Φ ~>* Ψ -> ⟦Φ⟧ ⟺ ⟦Ψ⟧.
Proof.
  move => x y.
  elim => [Φ |Φ1 Φ2 Φ3 Hstep H IH] //.
  rewrite -IH. elim: Hstep => X Φ Ψ Hstep.
  apply grounding. by apply local_soundness.
Qed.

End Soundness.

(** * Completeness *)

Section Completeness.

Reserved Notation "⌈ A ⌉" (format "⌈ A ⌉", at level 0).

Fixpoint finterp (A : form) : bouquet :=
  match A with
  | FAtom p args => Atom p args
  | ⊤ => []
  | ⊥ => ∅ ⊢
  | A ∧ B => ⌈A⌉ ++ ⌈B⌉
  | A ∨ B => ⊢ [0 ⋅ ⌈A⌉; 0 ⋅ ⌈B⌉]
  | A ⊃ B => 0 ⋅ ⌈A⌉ ⊢ [0 ⋅ ⌈B⌉]
  | #∀ A => 1 ⋅ [] ⊢ [0 ⋅ ⌈A⌉]
  | #∃ A => ⊢ [1 ⋅ ⌈A⌉]
  end
where "⌈ A ⌉" := (finterp A).

Notation "⌈[ Γ ]⌉" := (A ← Γ; ⌈A⌉).

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
  rewrite bind_cons fmap_cons fmap_app bind_cons.
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
  rewrite bind_cons fmap_cons fmap_app bind_cons.
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
  rewrite bind_cons fmap_cons fmap_app bind_cons.
  by rewrite subst_fsubst IH.
Qed.

(* Definition dummin := 0.

Definition lmin (l : list nat) : nat :=
  match l with
  | [] => dummin
  | n :: l => foldr Nat.min n l
  end.

Fixpoint tminvar (c : nat) (t : Terms.term) : nat :=
  match t with
  | Terms.TVar n => if c <? n then n else dummin
  | Terms.TFun _ args => lmin (tminvar c <$> args)
  end.

Fixpoint fminvar (c : nat) (A : form) : nat :=
  match A with
  | FAtom p args => lmin (tminvar c <$> args)
  | FTrue => dummin
  | FFalse => dummin
  | FAnd A B => lmin [fminvar c A; fminvar c B]
  | FOr A B => lmin [fminvar c A; fminvar c B]
  | FImp A B => lmin [fminvar c A; fminvar c B]
  | FForall A => fminvar (c + 1) A
  | FExists A => fminvar (c + 1) A
  end. *)

Definition is_shifted (n : nat) (A : form) : Prop :=
  exists B, A = fshift n 0 B.

Lemma is_shifted_zero A :
  is_shifted 0 A.
Proof.
  exists A. by rewrite fshift_zero.
Qed.

Definition subctx (Γ : list form) (X : ctx) : Prop :=
  forall D, D ∈ Γ -> exists n, is_shifted n D /\ nassum n ⌈D⌉ X.

Infix "⪽" := subctx (at level 30).

Ltac estep := etransitivity; [> eapply rtc_once |].

Theorem full_completeness Γ C :
  Γ c⟹ C -> forall X, Γ ⪽ X ->
  X ⋖ ⌈C⌉ ~>* X ⋖ [].
Proof.
  elim =>/= {Γ C} [
    A Γ Γ'
  | A Γ Γ' Γ'' C Hp1 IH1
  | A Γ Γ' Γ'' C Hp1 IH1
  | Γ
  | A B Γ Hp1 IH1 Hp2 IH2
  | A B Γ Hp1 IH1
  | A B Γ Hp1 IH1
  | A B Γ Hp1 IH1
  | Γ C Hp1 IH1
  | t Γ C Hp1 IH1
  | Γ Γ' C Hp1 IH1
  | Γ Γ' C
  | A B Γ Γ' C Hp1 IH1
  | A B Γ Γ' C Hp1 IH1 Hp2 IH2
  | A B Γ Γ' C Hp1 IH1 Hp2 IH2
  | A t Γ Γ' C Hp1 IH1
  | A t Γ Γ' C IH1
  ] X H.

  (* Axiom *)
  * assert (Hprem : A ∈ (Γ ++ A :: Γ')).
    { solve_elem_of_list. }
    elim (H A Hprem) => n [[B ?] [Y [Z [Hpol Hcomp]]]]; subst.
    pose proof (Hp := R_pol _ _ _ Hpol).
    rewrite -fill_comp -fill_comp; apply cstep_congr.
    rewrite -shift_fshift in Hp |- *.
    rewrite bunshift_shift in Hp.
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
  * set X0 := Planter [] □ ⌈B⌉.
    specialize (IH1 (X ⪡ X0)).
    repeat rewrite -fill_comp /= in IH1.
    etransitivity; [> apply IH1 |].
    - move => D HD.
      case (H D HD) => n [Hshift Hassum].
      exists n. split; auto.
      pose proof (Hass := nassum_comp_out n ⌈D⌉ X X0 Hassum).
      by rewrite /= bshift_zero Nat.add_0_r in Hass.
    - by apply IH2.

  (* R∨₁ *)
  (* * specialize (IH1 (X ⪡ Petal ∅ [] 0 □ [0 ⋅ shift (bv X) 0 <$> ⌈B⌉])).
    rewrite /fill_ca in IH1 |- *.
    repeat rewrite -fill_comp in IH1.
    rewrite bv_comp /= Nat.add_0_r in IH1.
    rewrite fmap_singl.
    etransitivity; [> apply IH1 |].
    - move => D HD. by apply assum_ca_comp_out.
    - apply cstep_congr.
      rpetm (@nil nat) (@nil garden) [0 ⋅ shift (bv X) 0 <$> ⌈B⌉].
      reflexivity. *)
  * admit.

  (* R∨₁ *)
  (* * specialize (IH1 (X ⪡ Petal ∅ [0 ⋅ shift (bv X) 0 <$> ⌈A⌉] 0 □ [])).
    rewrite /fill_ca in IH1 |- *.
    repeat rewrite -fill_comp in IH1.
    rewrite bv_comp /= Nat.add_0_r in IH1.
    rewrite fmap_singl.
    etransitivity; [> apply IH1 |].
    - move => D HD. by apply assum_ca_comp_out.
    - apply cstep_congr.
      rpetm (@nil nat) [0 ⋅ shift (bv X) 0 <$> ⌈A⌉] (@nil garden).
      reflexivity. *)
  * admit.

  (* R⊃ *) 
  * set X0 := Petal (0 ⋅ ⌈A⌉) [] 0 □ [].
    specialize (IH1 (X ⪡ X0)).
    repeat rewrite -fill_comp /= in IH1.
    etransitivity; [> apply IH1 |].
    - move => D HD. decompose_elem_of_list.
      + subst.
        exists 0. split; [> apply is_shifted_zero |].
        red.
        rewrite bunshift_zero.
        eexists. eexists.
        split; [> |reflexivity]. rewrite /X0.
        epose proof (Hp := P_self _ □ _ [] [] _ 0); list_simplifier.
        eapply Hp.
      + case (H D H0) => n [Hshift Hassum].
        exists n. split; auto.
        pose proof (Hass := nassum_comp_out n ⌈D⌉ X X0 Hassum).
        by rewrite /= bshift_zero Nat.add_0_r in Hass.
    - apply cstep_congr.
      rpetm (@nil nat) (@nil garden) (@nil garden).
      reflexivity.

  (* R∀ *)
  * set X0 := Petal (1 ⋅ []) [] 0 □ [].
    specialize (IH1 (X ⪡ X0)).
    repeat rewrite -fill_comp /= in IH1.
    etransitivity; [> apply IH1 |].
    - move => D HD.
      apply elem_of_map in HD.
      case: HD => [E [HE1 HE2]].
      case (H E HE1) => m [Hshift Hassum].
      exists (m + 1). split.
      { red. case: Hshift => F ?; subst.
        exists F. by rewrite -fshift_add Nat.add_comm. }
      pose proof (Hass := nassum_comp_out _ _ X X0 Hassum).
      rewrite HE2 -shift_fshift.
      by rewrite /= in Hass.
    - apply cstep_congr.
      rpetm (@nil nat) (@nil garden) (@nil garden).
      reflexivity.

  (* R∃ *)
  * admit.

  (* L⊤ *)
  * admit.

  (* L⊥ *)
  * admit.

  (* L∧ *)
  * admit.

  (* L∨ *)
  * admit.

  (* L⊃ *)
  * admit.

  (* L∀ *)
  * admit.

  (* L∃ *)
  * admit.
Admitted.

Theorem completeness Γ C :
  Γ c⟹ C ->
  ⌈⋀ Γ ⊃ C⌉ ~>* [].
Proof.
  elim =>/=; clear Γ C.

  (* Axiom *)
  * move => A Γ Γ'.
    rewrite finterp_And bind_app bind_cons.

    rspolm [1] ⌈[Γ]⌉ ⌈[Γ']⌉.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* Right contraction *)
  * move => A Γ Γ' Γ'' C H IH.
    rewrite finterp_And bind_app bind_app bind_cons.
    rewrite finterp_And bind_app bind_cons bind_app bind_cons in IH.

    rctransm [0;0] (⌈[ Γ ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ' ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ'' ]⌉).
    rewrite -{1}[⌈[Γ]⌉]app_nil_r -app_assoc.
    rwcopolm (@nil nat) 0 ⌈[ Γ' ]⌉ ⌈A⌉ ⌈[ Γ'' ]⌉.
    list_simplifier; reflexivity.

    exact IH.

  (* Left contraction *)
  * move => A Γ Γ' Γ'' C H IH.
    rewrite finterp_And bind_app bind_cons bind_app.
    rewrite finterp_And bind_app bind_cons bind_app bind_cons in IH.

    rctransm [0;0] (⌈[ Γ ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ' ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ'' ]⌉).
    assert (Ha :
      ⌈[ Γ ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ' ]⌉ ++ ⌈[ Γ'' ]⌉ =
      (⌈[ Γ ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ' ]⌉) ++ [] ++ ⌈[ Γ'' ]⌉).
    { list_simplifier. reflexivity. }
    rewrite Ha.
    rwcopolm (@nil nat) 0 ⌈[ Γ ]⌉ ⌈A⌉ ⌈[ Γ' ]⌉.
    list_simplifier; reflexivity.

    exact IH.

  (* R⊤ *)
  * move => Γ.

    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∧ *)
  * move => A B Γ Hp1 IH1 Hp2 IH2.

    rcoepispet 0 0 (@nil flower) ⌈B⌉ (@nil garden) (@nil garden).
    rcoepispet 0 0 [⊢ [0 ⋅ ⌈A⌉]] (@nil flower) (@nil garden) (@nil garden).

    rscopolm [1;0;0] 0 0 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rscopolm [1;1;0] 0 0 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).

    rctxmH [0;1;0] IH1.
    rctxmH [0;1;0] IH2.

    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∨₁ *)
  * move => A B Γ Hp1 IH1.

    rectxmt [0;1].
    rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) [0 ⋅ ⌈B⌉].
    reflexivity.

    rscopolm [1;0;1;0;0] 0 0 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rctxmH [0;1;0;1;0] IH1.
    rpetm [0;1] (@nil garden) [0 ⋅ ⌈B⌉].
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∨₂ *)
  * move => A B Γ Hp1 IH1.

    rectxmt [0;1].
    rcoepispet 0 0 (@nil flower) (@nil flower) [0 ⋅ ⌈A⌉] (@nil garden).
    reflexivity.

    rscopolm [1;0;2;0;0] 0 0 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rctxmH [0;1;0;2;0] IH1.
    rpetm [0;1] [0 ⋅ ⌈A⌉] (@nil garden).
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R⊃ *)
  * move => A B Γ Hp1 IH1.

    rscopolm [1;0;0] 1 0 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).

    rctxmH [0;1;0] IH1.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∀ *)
  * move => Γ C Hp1 IH1.

    rectxmt [0;1;0].
    rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) (@nil garden).
    reflexivity.

    rscopolm [1;0;1;0;0] 0 1 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rewrite {2}finterp_And bshift_fshift -finterp_And.
    rctxmH [0;1;0;1] IH1.

    rpetm [0;1] (@nil garden) (@nil garden).
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∃ *)
  * move => t Γ C Hp1 IH1.

    pose proof (H := R_ipet 0 t 0 ⌈C⌉ ∅ [] []).
    assert (Hbounds : 0 <= 0 <= 0). { lia. }
    specialize (H Hbounds).
    list_simplifier.
    apply (R_ctx □) in H; simpl in H.
    apply rtc_once in H.
    rctxmH [0;1;0] H.
    rewrite subst_fsubst unshift_funshift.

    rectxmt [0;1;0].
    rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) [1 ⋅ ⌈C⌉].
    reflexivity.

    rscopolm [1;0;1;0;0] 0 0 (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rctxmH [0;1;0;1;0] IH1.

    rpetm [0;1;0] (@nil garden) [1 ⋅ ⌈C⌉].
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* L⊤ *)
  * move => Γ Γ' C Hp1 IH1.
    rewrite finterp_And bind_app bind_cons /=.
    rewrite finterp_And bind_app /= in IH1.

    exact IH1. 

  (* L⊥ *)
  * move => Γ Γ' C.
    rewrite finterp_And bind_app bind_cons /=.

    rewrite /ftob [(⊢ []) :: _]cons_app.
    rrep.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* L∧ *)
  * move => A B Γ Γ' C Hp1 IH1.
    rewrite finterp_And bind_app bind_cons /=.
    rewrite finterp_And bind_app bind_cons bind_cons /= in IH1.

    by rewrite -app_assoc.

  (* L∨ *)
  * move => A B Γ Γ' C Hp1 IH1 Hp2 IH2.
    rewrite finterp_And bind_app bind_cons /=.
    rewrite finterp_And bind_app bind_cons /= in IH1.
    rewrite finterp_And bind_app bind_cons /= in IH2.

    rewrite /ftob [_ :: ⌈[Γ']⌉]cons_app.
    rrep.
    rewrite bshift_zero.

    rewrite /ftob.
    rscopolm [1;0;0] 0 0 (@nil flower) ⌈[Γ]⌉ ⌈[Γ']⌉.
    rscopolm [1;0;0] 1 0 ⌈[Γ]⌉ ⌈[Γ']⌉ (@nil flower).
    rscopolm [1;1;0] 0 0 (@nil flower) ⌈[Γ]⌉ ⌈[Γ']⌉.
    rscopolm [1;1;0] 1 0 ⌈[Γ]⌉ ⌈[Γ']⌉ (@nil flower).

    rctxmH [0;1;0] IH1.
    rctxmH [0;1;0] IH2.

    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* L⊃ *)
  * move => A B Γ Γ' C Hp1 IH1 Hp2 IH2.
    rewrite finterp_And bind_app bind_cons /=.
    rewrite finterp_And bind_app /= in IH1.
    rewrite finterp_And bind_app bind_cons /= in IH2.

    rctransm [0;0] (⌈[Γ]⌉ ++ (0 ⋅ [⊢ [0 ⋅ ⌈A⌉]] ⊢ [0 ⋅ ⌈B⌉]) :: ⌈[Γ']⌉).
    rctxt_app (@nil nat) 1.
    rctxt_app (@nil nat) 0.
    rcoepispis 0 0 (@nil flower) (@nil flower).
    reflexivity.

    rctransm [0;0] (⌈[Γ]⌉ ++ (0 ⋅ [0 ⋅ ⌈[Γ]⌉ ⊢ [0 ⋅ ⌈A⌉]] ⊢ [0 ⋅ ⌈B⌉]) :: ⌈[Γ']⌉).
    do 2 rewrite [_ :: ⌈[Γ']⌉]cons_app.
    assert (Ha : ⌈[ Γ ]⌉ = [] ++ ⌈[ Γ ]⌉ ++ []). { by list_simplifier. }
    rewrite {1}Ha {2}Ha.
    rwcopolm [0;0;0;0] 0 (@nil flower) ⌈[Γ]⌉ (@nil flower).
    list_simplifier. reflexivity.

    rctransm [0;0] (⌈[Γ]⌉ ++ (0 ⋅ [0 ⋅ ⌈[Γ]⌉ ++ ⌈[Γ']⌉ ⊢ [0 ⋅ ⌈A⌉]] ⊢ [0 ⋅ ⌈B⌉]) :: ⌈[Γ']⌉).
    do 2 rewrite [_ :: ⌈[Γ']⌉]cons_app.
    assert (Ha : ⌈[ Γ' ]⌉ = [] ++ ⌈[ Γ' ]⌉ ++ []). { by list_simplifier. }
    rewrite {1}Ha {2}Ha.
    rwcopolm [0;0;0;0] 1 (@nil flower) ⌈[Γ']⌉ (@nil flower).
    list_simplifier. reflexivity.

    rctransm [0;0] (⌈[Γ]⌉ ++ (⊢ [0 ⋅ ⌈B⌉]) :: ⌈[Γ']⌉).
    rctxt_app (@nil nat) 1.
    rctxt_app (@nil nat) 0.
    rctxmH [0;0] IH1. reflexivity.

    etransitivity; [> |eapply IH2].
    repispis 0 0 ⌈[Γ]⌉ ⌈[Γ']⌉.
    reflexivity.
  
  (* L∀ *)
  * move => A t Γ Γ' C Ip1 IH1.
    rewrite finterp_And bind_app bind_cons /=.
    rewrite finterp_And bind_app bind_cons /= in IH1.

    epose proof (H := R_ipis 0 t 0 _ [0 ⋅ ⌈A⌉]).
    assert (Hbounds : 0 <= 0 <= 0). { lia. }
    specialize (H Hbounds).
    list_simplifier.
    apply (R_ctx □) in H; simpl in H.
    apply rtc_once in H.
    rectxmt [0;0].
    pose proof (Hctx := cstep_congr (Planter ⌈[Γ]⌉ □ ⌈[Γ']⌉)); simpl in Hctx.
    rewrite cons_app. apply Hctx.
    rctxmH (@nil nat) H. list_simplifier.
    rewrite subst_fsubst unshift_funshift Terms.tshift_zero.
    reflexivity.

    change ([?ϕ; ?ψ] ++ ?Φ) with ([ϕ] ++ ψ :: Φ).
    epose proof (H' := R_epis_pis 0 _ 0 _ _ _).
    rewrite bshift_zero bshift_zero pshift_zero /= in H'.
    eapply rtc_l. rself. eapply H'.

    rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) (@nil garden).
    rewrite cons_app /ftob.
    match goal with
    | |- [_ ⋅ ?Φ1 ++ ?Φ2 ++ ?Φ3 ++ ?Φ4 ⊢ _] ~>* _ =>
        rscopolm [1;0;0] 0 0 (@nil flower) Φ1 (Φ2 ++ Φ3 ++ Φ4);
        rscopolm [1;0;0] 1 0 Φ1 Φ2 (Φ3 ++ Φ4);
        rscopolm [1;0;0] 1 0 (Φ1 ++ Φ2 ++ Φ3) Φ4 (@nil flower)
    end.
    rctxmH [0;1;0] IH1.

    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* L∃ *)
  * move => A Γ Γ' C Ip1 IH1.
    rewrite finterp_And bind_app bind_cons /=.
    rewrite finterp_And bind_app bind_cons /= in IH1.

    repispis 0 1 ⌈[Γ]⌉ ⌈[Γ']⌉.

    rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) (@nil garden).

    rscopolm [1;0;0] 0 0 ((shift 1 0 <$> ⌈[Γ]⌉) ++ ⌈A⌉) (shift 1 0 <$> ⌈[Γ']⌉) (@nil flower).
    rscopolm [1;0;0] 0 0 (shift 1 0 <$> ⌈[Γ]⌉) ⌈A⌉ (shift 1 0 <$> ⌈[Γ']⌉).
    rscopolm [1;0;0] 0 0 (@nil flower) (shift 1 0 <$> ⌈[Γ]⌉) (⌈A⌉ ++ (shift 1 0 <$> ⌈[Γ']⌉)).

    repeat rewrite bshift_fshift.
    rewrite shift_fshift.
    rctxmH [0;1;0] IH1.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.
Qed.

End Completeness.

(** * Deduction *)

Definition entails (Φ Ψ : bouquet) := 0 ⋅ Φ ⊢ [0 ⋅ Ψ] ~>* [].

Infix "===>" := entails (at level 90).

Theorem deduction Φ Ψ :
  Φ ===> Ψ <-> [] ===> 0 ⋅ Φ ⊢ [0 ⋅ Ψ].
Proof.
  split; rewrite /entails; move => H.

  * rctxmH [0;1] H.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  * rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) (@nil garden).

    rscopolm [1;0;0] 0 0 (@nil flower) Φ (@nil flower).
    rcoepispet 0 0 (@nil flower) (@nil flower) (@nil garden) (@nil garden).

    rctxmH [0;1;0] H.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.
Qed.