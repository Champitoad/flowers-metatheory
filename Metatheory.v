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

Ltac rspol p Φl Φr :=
  match goal with
  | |- ftob ?ϕ ⇀ _ =>
              idtac "pouet";
      let XΨ := eval cbn in (fpath p ϕ) in
      match XΨ with
      | Some (?X, ?Ψ) =>
          let H := fresh "H" in
          pose proof (H := R_pol Ψ 0 X);
          rewrite bshift_zero /= in H;
          apply H;
          match X with
          | Petal _ _ _ ?Y _ =>
              let H := fresh "H" in
              epose proof (H := P_self _ Y 0 Φl Φr _ 0 _);
              list_simplifier; apply H
          end
      end
  end.

Ltac rspolm p Φl Φr :=
  rstepm (0 :: p) (@nil flower); [>
    rself;
    rspol p Φl Φr
  |].

Ltac rscopol p Φl Ψ Φr :=
  match goal with
  | |- [?ϕ] ⇀ _ =>
      let XΨ := eval cbn in (fpath p ϕ) in
      match XΨ with
      | Some (?X, []) =>
          let H := fresh "H" in
          pose proof (H := R_co_pol Ψ 0 X);
          rewrite bshift_zero /= in H;
          apply H;
          match X with
          | Petal _ _ _ ?Y _ =>
              let H := fresh "H" in
              epose proof (H := P_self _ Y 0 Φl Φr _ 0 _);
              list_simplifier; apply H
          end
      end
  end.

Ltac rscopolm p Φl Ψ Φr :=
  rstepm (0 :: p) Ψ; [>
    rself;
    rscopol p Φl Ψ Φr
  |].

Theorem full_completeness Γ C :
  Γ c⟹ C -> forall X,
  (forall A, In A Γ -> ⌈A⌉ ∈ X) ->
  X ⋖ ⌈C⌉ ~>* X ⋖ [].
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

    rstepm_app [0;0] 0 (⌈[Γ]⌉ ++ ⌈A⌉); [> |apply IH].
    rctxm [0;0].
    set Ψ := ⌈A⌉.
    set X := Planter ⌈[Γ]⌉ □ (⌈[Γ']⌉ ++ ⌈A⌉ ++ ⌈[Γ'']⌉).
    let H := fresh "H" in
    pose proof (H := R_co_pol Ψ 0 X);
    rewrite bshift_zero /= in H;
    apply H.
    apply (P_wind_l _ □).

  (* Left contraction *)
  * move => A Γ Γ' Γ'' C H IH.
    rewrite finterp_And bind_app bind_cons bind_app.
    rewrite finterp_And bind_app bind_cons bind_app bind_cons in IH.

    rstepm_app [0;0] 1 (⌈A⌉ ++ ⌈[ Γ' ]⌉ ++ ⌈A⌉ ++ ⌈[ Γ'' ]⌉); [> |apply IH].
    rctxm [0;0].
    set Ψ := ⌈A⌉.
    set X := Planter (⌈[Γ]⌉ ++ Ψ ++ ⌈[Γ']⌉) □ ⌈[Γ'']⌉.
    let H := fresh "H" in
    pose proof (H := R_co_pol Ψ 0 X);
    rewrite bshift_zero /= in H; list_simplifier;
    apply H.
    apply (P_wind_r _ □).

  (* R⊤ *)
  * move => Γ.

    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∧ *)
  * move => A B Γ Hp1 IH1 Hp2 IH2.

    rstepm_app [0;1] 0 ([⊢ [0 ⋅ ⌈A⌉]]).
    pose proof (H := R_co_epis_pet 0 ⌈A⌉ 0 [] ⌈B⌉ (0 ⋅ ⌈⋀ Γ⌉) [] []).
    list_simplifier; rewrite bshift_zero in H.
    rself. apply H.

    rstepm_app [0;1] 1 ([⊢ [0 ⋅ ⌈B⌉]]).
    pose proof (H := R_co_epis_pet 0 ⌈B⌉ 0 [⊢ [0 ⋅ ⌈A⌉]] [] (0 ⋅ ⌈⋀ Γ⌉) [] []).
    list_simplifier; rewrite bshift_zero in H.
    rself; apply H.

    rscopolm [1;0;0] (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rscopolm [1;1;0] (@nil flower) ⌈⋀ Γ⌉ (@nil flower).

    rctxmH [0;1;0] IH1.
    rctxmH [0;1;0] IH2.

    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∨₁ *)
  * move => A B Γ Hp1 IH1.

    rstepm [0;1;0;1] (⊢ [0 ⋅ ⌈A⌉]).
    rctxm [0;1].
    epose proof (H := R_co_epis_pet 0 _ 0 [] [] _ [] [0 ⋅ ⌈B⌉]);
    list_simplifier; apply H.

    rscopolm [1;0;1;0;0] (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rctxmH [0;1;0;1;0] IH1.
    rpetm [0;1] (@nil garden) [0 ⋅ ⌈B⌉].
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.

  (* R∨₂ *)
  * move => A B Γ Hp1 IH1.

    rstepm [0;1;0;2] (⊢ [0 ⋅ ⌈B⌉]).
    rctxm [0;1].
    epose proof (H := R_co_epis_pet 0 _ 0 [] [] _ [0 ⋅ ⌈A⌉] []);
    list_simplifier; apply H.

    rscopolm [1;0;2;0;0] (@nil flower) ⌈⋀ Γ⌉ (@nil flower).
    rctxmH [0;1;0;2;0] IH1.
    rpetm [0;1] [0 ⋅ ⌈A⌉] (@nil garden).
    rpetm (@nil nat) (@nil garden) (@nil garden).
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

  (* Permutation *)
  * move => γ γ' C.
    move => Hperm Ip1 IH1.

    have H : ⌈⋀ γ⌉ ≡ₚ ⌈⋀ γ'⌉.
    { clear C Ip1 IH1.
      repeat rewrite finterp_And.
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