Require Import String Setoid Lia.
Require Import stdpp.list.
Require Import ssreflect.

Require Import Flowers.Terms Flowers.Utils.

(** Our semantics will be the sequent calculus LJ *)

(** * Syntax *)

Inductive form :=
| FAtom (p : name) (args : list term)
| FTrue
| FFalse
| FAnd (A : form) (B : form)
| FOr (A : form) (B : form)
| FImp (A : form) (B : form)
| FForall (A : form)
| FExists (A : form).

Notation "⊤" := FTrue.
Notation "⊥" := FFalse.
Infix "∧" := FAnd.
Infix "∨" := FOr.
Infix "⊃" := FImp (at level 85, right associativity).
Notation "#∀ A" := (FForall A) (at level 1).
Notation "#∃ A" := (FExists A) (at level 1).

Lemma form_induction_full :
  ∀ (P : form -> Prop) (Pt : term -> Prop)
  (IHt : ∀ t, Pt t)
  (IHatom : ∀ p args, Forall Pt args -> P (FAtom p args))
  (IHtrue : P ⊤) (IHfalse : P ⊥)
  (IHand : ∀ A B, P A -> P B -> P (A ∧ B))
  (IHor : ∀ A B, P A -> P B -> P (A ∨ B))
  (IHimp : ∀ A B, P A -> P B -> P (A ⊃ B))
  (IHfa : ∀ A, P A -> P (#∀ A))
  (IHex : ∀ A, P A -> P (#∃ A)),
  ∀ A, P A.
Proof.
  intros; move: A; fix IH 1; induction A.
  * apply IHatom. elim args; auto.
  * apply IHtrue.
  * apply IHfalse.
  * apply IHand; auto.
  * apply IHor; auto.
  * apply IHimp; auto.
  * apply IHfa; auto.
  * apply IHex; auto.
Qed.

Lemma form_induction :
  ∀ (P : form -> Prop)
  (IHatom : ∀ p args, P (FAtom p args))
  (IHtrue : P ⊤) (IHfalse : P ⊥)
  (IHand : ∀ A B, P A -> P B -> P (A ∧ B))
  (IHor : ∀ A B, P A -> P B -> P (A ∨ B))
  (IHimp : ∀ A B, P A -> P B -> P (A ⊃ B))
  (IHfa : ∀ A, P A -> P (#∀ A))
  (IHex : ∀ A, P A -> P (#∃ A)),
  ∀ A, P A.
Proof.
  intros; eapply form_induction_full; eauto.
  exact (fun _ => I).
Qed.

Definition And :=
  foldr FAnd ⊤.

Definition Or :=
  foldr FOr ⊥.

Fixpoint nforall n A :=
  match n with
  | 0 => A
  | S n => #∀ (nforall n A)
  end.

Fixpoint nexists n A :=
  match n with
  | 0 => A
  | S n => #∃ (nexists n A)
  end.

Notation "⋀ As" := (And As) (at level 5).
Notation "⋁ As" := (Or As) (at level 5).
Notation "n #∀ A" := (nforall n A) (format "n #∀  A", at level 6).
Notation "n #∃ A" := (nexists n A) (format "n #∃  A", at level 6).

(** * Shifting and substitution *)

Fixpoint fshift (n : nat) (c : nat) (A : form) : form :=
  match A with
  | FAtom p args => FAtom p (tshift n c <$> args)
  | FTrue | FFalse => A
  | FAnd A B => FAnd (fshift n c A) (fshift n c B)
  | FOr A B => FOr (fshift n c A) (fshift n c B)
  | FImp A B => FImp (fshift n c A) (fshift n c B)
  | FForall A => FForall (fshift n (c+1) A)
  | FExists A => FExists (fshift n (c+1) A)
  end.

Fixpoint funshift (n : nat) (c : nat) (A : form) : form :=
  match A with
  | FAtom p args => FAtom p (tunshift n c <$> args)
  | FTrue | FFalse => A
  | FAnd A B => FAnd (funshift n c A) (funshift n c B)
  | FOr A B => FOr (funshift n c A) (funshift n c B)
  | FImp A B => FImp (funshift n c A) (funshift n c B)
  | FForall A => FForall (funshift n (c+1) A)
  | FExists A => FExists (funshift n (c+1) A)
  end.

Fixpoint fsubst (σ : nat -> term) (A : form) : form :=
  match A with
  | FAtom p args => FAtom p (tsubst σ <$> args)
  | FTrue | FFalse => A
  | FAnd A B => FAnd (fsubst σ A) (fsubst σ B)
  | FOr A B => FOr (fsubst σ A) (fsubst σ B)
  | FImp A B => FImp (fsubst σ A) (fsubst σ B)
  | FForall A => FForall (fsubst (sshift 1 σ) A)
  | FExists A => FExists (fsubst (sshift 1 σ) A)
  end.

(** ** Operations commute with n-ary connectives *)

Lemma fshift_And {T} (f : T -> form) : ∀ Γ n c,
  fshift n c ⋀ (f <$> Γ) = ⋀ ((λ A, fshift n c (f A)) <$> Γ).
Proof.
  elim => [n c |B Γ IH n c]//.
  rewrite fmap_cons cons_app //=.
  by rewrite IH.
Qed.

Lemma funshift_And {T} (f : T -> form) : ∀ Γ n t,
  funshift n t ⋀ (f <$> Γ) = ⋀ ((λ A, funshift n t (f A)) <$> Γ).
Proof.
  elim => [n c |B Γ IH n c]//.
  rewrite fmap_cons cons_app //=.
  by rewrite IH.
Qed.

Lemma fsubst_And {T} (f : T -> form) : ∀ Γ σ,
  fsubst σ ⋀ (f <$> Γ) = ⋀ ((λ A, fsubst σ (f A)) <$> Γ).
Proof.
  elim => [|B Γ IH] σ //.
  rewrite fmap_cons cons_app //=.
  by rewrite IH.
Qed.

Lemma fshift_Or {T} (f : T -> form) : ∀ Γ n c,
  fshift n c ⋁ (f <$> Γ) = ⋁ ((λ A, fshift n c (f A)) <$> Γ).
Proof.
  elim => [n c |B Γ IH n c]//.
  rewrite fmap_cons cons_app //=.
  by rewrite IH.
Qed.

Lemma funshift_Or {T} (f : T -> form) : ∀ Γ n c,
  funshift n c ⋁ (f <$> Γ) = ⋁ ((λ A, funshift n c (f A)) <$> Γ).
Proof.
  elim => [n c |B Γ IH n c]//.
  rewrite fmap_cons cons_app //=.
  by rewrite IH.
Qed.

Lemma fsubst_Or {T} (f : T -> form) : ∀ Γ σ,
  fsubst σ ⋁ (f <$> Γ) = ⋁ ((λ A, fsubst σ (f A)) <$> Γ).
Proof.
  elim => [|B Γ IH] σ //.
  rewrite fmap_cons cons_app //=.
  by rewrite IH.
Qed.

Lemma fshift_nforall : ∀ m n c A,
  fshift n c m#∀ A = m#∀ (fshift n (c + m) A).
Proof.
  elim => [n c A |m IH n c A]//=.
  by rewrite Nat.add_0_r.
  f_equal.
  specialize (IH n (c + 1) A).
  assert (H : c + 1 + m = c + S m). { lia. }
  rewrite H in IH.
  by rewrite IH.
Qed.

Lemma funshift_nforall : ∀ m n c A,
  funshift n c m#∀ A = m#∀ (funshift n (c + m) A).
Proof.
  elim => [n c A |m IH n c A]//=.
  by rewrite Nat.add_0_r.
  f_equal.
  specialize (IH n (c + 1) A).
  assert (H : c + 1 + m = c + S m). { lia. }
  rewrite H in IH.
  by rewrite IH.
Qed.

Lemma fsubst_nforall : ∀ m σ A,
  fsubst σ (m#∀ A) = m#∀ (fsubst (sshift m σ) A).
Proof.
  elim => [|m IH] σ A //=.
  by rewrite sshift_zero.
  f_equal.
  specialize (IH (sshift 1 σ) A).
  by rewrite IH -sshift_add Nat.add_1_r.
Qed.

Lemma fshift_nexists : ∀ m n c A,
  fshift n c m#∃ A = m#∃ (fshift n (c + m) A).
Proof.
  elim => [n c A |m IH n c A]//=.
  by rewrite Nat.add_0_r.
  f_equal.
  specialize (IH n (c + 1) A).
  assert (H : c + 1 + m = c + S m). { lia. }
  rewrite H in IH.
  by rewrite IH.
Qed.

Lemma funshift_nexists : ∀ m n c A,
  funshift n c m#∃ A = m#∃ (funshift n (c + m) A).
Proof.
  elim => [n c A |m IH n c A]//=.
  by rewrite Nat.add_0_r.
  f_equal.
  specialize (IH n (c + 1) A).
  assert (H : c + 1 + m = c + S m). { lia. }
  rewrite H in IH.
  by rewrite IH.
Qed.

Lemma fsubst_nexists : ∀ m σ A,
  fsubst σ (m#∃ A) = m#∃ (fsubst (sshift m σ) A).
Proof.
  elim => [|m IH] σ A //=.
  by rewrite sshift_zero.
  f_equal.
  specialize (IH (sshift 1 σ) A).
  by rewrite IH -sshift_add Nat.add_1_r.
Qed.

(** ** Shifting and arithmetic *)

Lemma fshift_zero : ∀ A c,
  fshift 0 c A = A.
Proof.
  induction A using form_induction; intros c; simpl; auto.
  * pose proof (H := eq_map (tshift 0 c) id args (tshift_zero c)).
    by rewrite H list_fmap_id.
  * f_equal; done.
  * f_equal; done.
  * f_equal; done.
  * f_equal. by rewrite IHA.
  * f_equal. by rewrite IHA.
Qed.

Lemma cshift_zero : ∀ (Γ : list form) c,
  fshift 0 c <$> Γ = Γ.
Proof.
  intros. rewrite -{2}[Γ]map_id_ext. apply eq_map.
  intros. by apply fshift_zero.
Qed.

Lemma fshift_add : ∀ A c n m,
  fshift (n + m) c A = fshift n c (fshift m c A).
Proof.
  induction A using form_induction; intros c n m; simpl; auto.
  * pose proof (H := eq_map (tshift (n + m) c) _ args (tshift_add c n m)).
    by rewrite H list_fmap_compose.
  * f_equal; done.
  * f_equal; done.
  * f_equal; done.
  * f_equal. by rewrite IHA.
  * f_equal. by rewrite IHA.
Qed.

Lemma fshift_succ : ∀ A c n,
  fshift (S n) c A = fshift 1 c (fshift n c A).
Proof.
  intros.
  rewrite -Nat.add_1_l.
  apply fshift_add.
Qed.

Lemma fshift_comm A c n m :
  fshift n c (fshift m c A) = fshift m c (fshift n c A).
Proof.
  by rewrite -fshift_add Nat.add_comm fshift_add.
Qed.

(** ** Interaction of shifting and substitution *)

Lemma fsubst_fshift A : ∀ c m,
  fsubst (c ↦ TVar (c + m)) (fshift m (S c) A) = fshift m c A.
Proof.
  induction A; intros; simpl; auto; try by rewrite IHA1 IHA2.
  * induction args; auto. list_simplifier.
    f_equal. f_equal; auto. by apply (tsubst_tshift c m).
  * specialize (IHA (c + 1) m). f_equal.
    rewrite -IHA sshift_mksubst /=.
    assert (H : c + m + 1 = c + 1 + m) by lia. by rewrite H.
  * specialize (IHA (c + 1) m). f_equal.
    rewrite -IHA sshift_mksubst /=.
    assert (H : c + m + 1 = c + 1 + m) by lia. by rewrite H.
Qed.

Lemma fsubst_fshift_vacuous A : ∀ n u m c,
  n < m ->
  fsubst ((n + c) ↦ u) (fshift m c A) = fshift m c A.
Proof.
  induction A; intros; simpl; auto;
  try by rewrite (IHA1 n u m c H) (IHA2 n u m c H).
  * induction args; auto. list_simplifier.
    f_equal. f_equal; auto. by apply (tsubst_tshift_vacuous n u m c).
  * epose proof (IH := IHA n (tshift 1 0 u) m (c + 1) _).
    by rewrite -{2}IH sshift_mksubst Nat.add_assoc.
  * epose proof (IH := IHA n (tshift 1 0 u) m (c + 1) _).
    by rewrite -{2}IH sshift_mksubst Nat.add_assoc.
  Unshelve.
  all: auto.
Qed.

Lemma fsubst_fshift_vacuous2 : ∀ A m c,
  fsubst (c ↦ TVar (c + m)) (fshift m (S c) A) = fshift m c A.
Proof.
  induction A using form_induction; intros; simpl; auto;
  try by rewrite (IHA1 m c) (IHA2 m c).
  * rewrite -list_fmap_compose.
    f_equal. apply eq_fmap. move => t /=.
    by apply tsubst_tshift_vacuous2.
  * f_equal. specialize (IHA m (c + 1)).
    rewrite -IHA sshift_mksubst /=.
    assert (H : c + 1 + m = c + m + 1) by lia.
    by rewrite H.
  * f_equal. specialize (IHA m (c + 1)).
    rewrite -IHA sshift_mksubst /=.
    assert (H : c + 1 + m = c + m + 1) by lia.
    by rewrite H.
Qed.

Lemma funshift_fshift A : ∀ n c,
  funshift n c (fshift n c A) = A.
Proof.
  induction A using form_induction; intros; simpl; auto;
  try by rewrite IHA1 IHA2.
  * rewrite -list_fmap_compose.
    rewrite (eq_map _ id).
    move => t.
    pose proof (H := tunshift_tshift 0 n c t).
    by rewrite tunshift_zero /= in H.
    by rewrite map_id_ext.
  * by rewrite IHA.
  * by rewrite IHA.
Qed.

(** * Contexts *)

(* Inductive fctx :=
| Chole
| CandL (X : fctx) (B : form)
| CandR (B : form) (X : fctx)
| CorL (X : fctx) (B : form)
| CorR (B : form) (X : fctx)
| CimpL (X : fctx) (B : form)
| CimpR (B : form) (X : fctx)
| Cforall (X : fctx)
| Cexists (X : fctx).

Fixpoint CAnd

Reserved Notation "X {{ A }}" (at level 0).

Fixpoint ffill (A : form) (X : fctx) : form :=
  match X with
  | Chole => A
  | CandL X B => X{{A}} ∧ B
  | CandR B X => B ∧ X{{A}}
  | CorL X B => X{{A}} ∨ B
  | CorR B X => B ∨ X{{A}}
  | CimpL X B => X{{A}} ⊃ B
  | CimpR B X => B ⊃ X{{A}}
  | Cforall X => #∀ X{{A}}
  | Cexists X => #∃ X{{A}}
  end
where "X {{ A }}" := (ffill A X). *)

(** * Rules *)

Reserved Infix "⟹" (at level 90).

Inductive deriv : list form -> form -> Prop :=

(** ** Identity *)

| S_ax A Γ Γ' :
  Γ ++ A :: Γ' ⟹ A

| S_cut A Γ Γ' C :
  Γ ++ Γ' ⟹ A -> Γ ++ A :: Γ' ⟹ C ->
  Γ ++ Γ' ⟹ C

(** ** Structural rules *)

| S_perm Γ Γ' C :
  Γ ≡ₚ Γ' ->
  Γ ⟹ C ->
  Γ' ⟹ C

| S_weak A Γ Γ' C :
  Γ ++ Γ' ⟹ C ->
  Γ ++ A :: Γ' ⟹ C

| S_contr_r A Γ Γ' Γ'' C :
  Γ ++ A :: Γ' ++ A :: Γ'' ⟹ C -> 
  Γ ++ Γ' ++ A :: Γ'' ⟹ C

| S_contr_l A Γ Γ' Γ'' C :
  Γ ++ A :: Γ' ++ A :: Γ'' ⟹ C -> 
  Γ ++ A :: Γ' ++ Γ'' ⟹ C

(** ** Right rules *)

| S_R_true Γ :
  Γ ⟹ ⊤

| S_R_and A B Γ :
  Γ ⟹ A -> Γ ⟹ B ->
  Γ ⟹ A ∧ B

| S_R_or_l A B Γ :
  Γ ⟹ A ->
  Γ ⟹ A ∨ B

| S_R_or_r A B Γ :
  Γ ⟹ B ->
  Γ ⟹ A ∨ B

| S_R_imp A B Γ :
  A :: Γ ⟹ B ->
  Γ ⟹ A ⊃ B

| S_R_forall Γ C :
  (fshift 1 0 <$> Γ) ⟹ C ->
  Γ ⟹ #∀ C

| S_R_exists t Γ C :
  Γ ⟹ funshift 1 0 (fsubst (0 ↦ tshift 1 0 t) C) ->
  Γ ⟹ #∃ C

(** ** Left rules *)

| S_L_true Γ Γ' C :
  Γ ++ Γ' ⟹ C ->
  Γ ++ ⊤ :: Γ' ⟹ C

| S_L_false Γ Γ' C :
  Γ ++ ⊥ :: Γ' ⟹ C

| S_L_and A B Γ Γ' C :
  Γ ++ A :: B :: Γ' ⟹ C ->
  Γ ++ (A ∧ B) :: Γ' ⟹ C

| S_L_or A B Γ Γ' C :
  Γ ++ A :: Γ' ⟹ C -> Γ ++ B :: Γ' ⟹ C ->
  Γ ++ (A ∨ B) :: Γ' ⟹ C

| S_L_imp A B Γ Γ' C :
  Γ ++ Γ' ⟹ A -> Γ ++ B :: Γ' ⟹ C ->
  Γ ++ (A ⊃ B) :: Γ' ⟹ C

| S_L_forall A t Γ Γ' C :
  Γ ++ funshift 1 0 (fsubst (0 ↦ tshift 1 0 t) A) :: Γ' ⟹ C ->
  Γ ++ #∀ A :: Γ' ⟹ C

| S_L_exists A Γ Γ' C :
  (fshift 1 0 <$> Γ) ++ A :: (fshift 1 0 <$> Γ') ⟹ fshift 1 0 C ->
  Γ ++ #∃ A :: Γ' ⟹ C

where "Γ ⟹ C" := (deriv Γ C).

(** ** Structural-free derivations *)

Reserved Infix "s⟹" (at level 90).

Inductive sderiv : list form -> form -> Prop :=

(** ** Identity *)

| Sc_ax A Γ Γ' :
  Γ ++ A :: Γ' s⟹ A

(** ** Contraction *)

| Sc_contr_r A Γ Γ' Γ'' C :
  Γ ++ A :: Γ' ++ A :: Γ'' s⟹ C -> 
  Γ ++ Γ' ++ A :: Γ'' s⟹ C

| Sc_contr_l A Γ Γ' Γ'' C :
  Γ ++ A :: Γ' ++ A :: Γ'' s⟹ C -> 
  Γ ++ A :: Γ' ++ Γ'' s⟹ C

(** ** Right rules *)

| Sc_R_true Γ :
  Γ s⟹ ⊤

| Sc_R_and A B Γ :
  Γ s⟹ A -> Γ s⟹ B ->
  Γ s⟹ A ∧ B

| Sc_R_or_l A B Γ :
  Γ s⟹ A ->
  Γ s⟹ A ∨ B

| Sc_R_or_r A B Γ :
  Γ s⟹ B ->
  Γ s⟹ A ∨ B

| Sc_R_imp A B Γ :
  A :: Γ s⟹ B ->
  Γ s⟹ A ⊃ B

| Sc_R_forall Γ C :
  (fshift 1 0 <$> Γ) s⟹ C ->
  Γ s⟹ #∀ C

| Sc_R_exists t Γ C :
  Γ s⟹ funshift 1 0 (fsubst (0 ↦ tshift 1 0 t) C) ->
  Γ s⟹ #∃ C

(** ** Left rules *)

| Sc_L_true Γ Γ' C :
  Γ ++ Γ' s⟹ C ->
  Γ ++ ⊤ :: Γ' s⟹ C

| Sc_L_false Γ Γ' C :
  Γ ++ ⊥ :: Γ' s⟹ C

| Sc_L_and A B Γ Γ' C :
  Γ ++ A :: B :: Γ' s⟹ C ->
  Γ ++ (A ∧ B) :: Γ' s⟹ C

| Sc_L_or A B Γ Γ' C :
  Γ ++ A :: Γ' s⟹ C -> Γ ++ B :: Γ' s⟹ C ->
  Γ ++ (A ∨ B) :: Γ' s⟹ C

| Sc_L_imp A B Γ Γ' C :
  Γ ++ Γ' s⟹ A -> Γ ++ B :: Γ' s⟹ C ->
  Γ ++ (A ⊃ B) :: Γ' s⟹ C

| Sc_L_forall A t Γ Γ' C :
  Γ ++ funshift 1 0 (fsubst (0 ↦ tshift 1 0 t) A) :: Γ' s⟹ C ->
  Γ ++ #∀ A :: Γ' s⟹ C

| Sc_L_exists A Γ Γ' C :
  (fshift 1 0 <$> Γ) ++ A :: (fshift 1 0 <$> Γ') s⟹ fshift 1 0 C ->
  Γ ++ #∃ A :: Γ' s⟹ C

where "Γ s⟹ C" := (sderiv Γ C).

(** * Basic proof search *)

Ltac passum :=
  match goal with
  | |- ?Γ ⟹ ?C =>
      let rec aux Γl Γr :=
        match Γr with
        | ?C :: ?Δ => apply (S_ax C Γl Δ)
        | ?A :: ?Δ => aux (Γl ++ [A]) Δ
        | ?Δ ++ ?Δ' => aux (Γl ++ Δ) Δ'
        | [] => fail
        end
      in 
      aux (@nil form) Γ
  end.

Ltac pweak i :=
  match goal with
  | |- ?Γ ⟹ ?C =>
      let X := eval cbn in (split_at i Γ) in
      match X with
      | Some (?Γl, ?A :: ?Γr) => apply (S_weak A Γl Γr)
      | _ => fail
      end
  end.

Ltac pintroL i :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval cbn in (split_at i Γ) in
      match X with
      | Some (?Γl, ?A :: ?Γr) =>
          let rule :=
            match A with
            | ⊤ => constr:(S_L_true Γl Γr)
            | ⊥ => constr:(S_L_false Γl Γr)
            | ?A ∧ ?B => constr:(S_L_and A B Γl Γr)
            | ?A ∨ ?B => constr:(S_L_or A B Γl Γr)
            | #∃ ?A => constr:(S_L_exists A Γl Γr)
            end
          in apply rule; simpl
      end
  end.

Ltac pimpL i :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval cbn in (split_at i Γ) in
      match X with
      | Some (?Γl, ?A :: ?Γr) =>
          let rule :=
            match A with
            | ?A ⊃ ?B => constr:(S_L_imp A B Γl Γr)
            end
          in apply rule; simpl
      end
  end.

Ltac pfaL i t :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval cbn in (split_at i Γ) in
      match X with
      | Some (?Γl, ?A :: ?Γr) =>
          let rule :=
            match A with
            | #∀ ?A => constr:(S_L_forall A t Γl Γr)
            end
          in apply rule; simpl
      end
  end.

Ltac pintroR :=
  match goal with
  | |- _ ⟹ ?C =>
      let rule :=
        match C with
        | ⊤ => S_R_true
        | _ ∧ _ => S_R_and
        | _ ⊃ _ => S_R_imp
        | #∀ _ => S_R_forall
        end
      in apply rule
  end.

Ltac pexR t :=
  match goal with
  | |- _ ⟹ ?C =>
      let rule :=
        match C with
        | #∃ _ =>
            let r := eval simpl in (S_R_exists t) in r
        end
      in apply rule
  end.

Ltac isrch :=
  match goal with
  | |- ?Γ ⟹ _ =>
      done || passum ||
      tryif pintroR then isrch else
      let rec introΓ n :=
        match n with
        | 0 => idtac
        | S ?m => tryif pintroL m then isrch else introΓ m
        end
      in let n := eval compute in (length Γ) in
      introΓ n; simpl
  end.

Ltac eqd := split; isrch.

Ltac pleft := apply S_R_or_l; isrch.
Ltac pright := apply S_R_or_r; isrch.

(** * Generalized rewriting of equiderivable formulas *)

Definition eqderiv (A B : form) : Prop :=
  ([A] ⟹ B) /\ ([B] ⟹ A).

Infix "⟺" := eqderiv (at level 95).

#[export] Instance equiv_eqderiv : Equivalence eqderiv.
Proof.
  econs; repeat red.
  * move => A. split; passum.
  * move => A B [HAB HBA]; done.
  * move => A B C [HAB HBA] [HBC HCB]. split.
    apply (S_cut B [] [A]); simpl; auto; by pweak 1.
    apply (S_cut B [] [C]); simpl; auto; by pweak 1.
Qed.

(* #[export] Instance : Equiv form := eqderiv. *)

#[global] Hint Extern 1 (_ ⟺ _) => reflexivity : core.

#[global] Instance : subrelation eq eqderiv.
Proof.
  red. intros A B H. by rewrite H.
Qed.

Add Morphism FAnd with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_and.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isrch. by pweak 1. by pweak 0.
  * isrch. by pweak 1. by pweak 0. 
Qed.

Add Morphism FOr with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_or.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isrch. pleft. pright.
  * isrch. pleft. pright.
Qed.

Add Morphism FImp with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_imp.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isrch. pimpL 1. exact. by pweak 0.
  * isrch. pimpL 1. exact. by pweak 0.
Qed.

Add Morphism FForall with signature
  eqderiv ==> eqderiv
  as proper_forall.
Proof.
  move => A B [HAB HBA].
  eqd; pfaL 0 (TVar 0); by rewrite fsubst_fshift funshift_fshift.
Qed.

Add Morphism FExists with signature
  eqderiv ==> eqderiv
  as proper_exists.
Proof.
  move => A B [HAB HBA].
  eqd; pexR (TVar 0); by rewrite fsubst_fshift funshift_fshift.
Qed.

Add Morphism And with signature
  Forall2 eqderiv ==> eqderiv
  as proper_And.
Proof.
  elim => [|A As IHA] //=.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isrch.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isrch.
    - pweak 1. apply H.
    - pweak 0. by apply IHA.
    - pweak 1. apply H.
    - pweak 0. by apply IHA.
Qed.

Add Morphism And with signature
  Forall2 eq ==> eq
  as proper_And_eq.
Proof.
  move => A B H.
  apply Forall2_eq_eq in H.
  by rewrite H.
Qed.

Add Morphism Or with signature
  Forall2 eqderiv ==> eqderiv
  as proper_Or.
Proof.
  elim => [|A As IHA] //=.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isrch.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isrch.
    - pleft. apply H.
    - pright. by apply IHA.
    - pleft. apply H.
    - pright. by apply IHA.
Qed.

Add Morphism Or with signature
  Forall2 eq ==> eq
  as proper_Or_eq.
Proof.
  move => A B H.
  apply Forall2_eq_eq in H.
  by rewrite H.
Qed.

Add Morphism nforall with signature
  eq ==> eqderiv ==> eqderiv
  as proper_nforall.
Proof.
  elim => [|n IH A B H*] //=.
  apply proper_forall. by apply IH.
Qed.

Add Morphism nexists with signature
  eq ==> eqderiv ==> eqderiv
  as proper_nexists.
Proof.
  elim => [|n IH A B H*] //=.
  apply proper_exists. by apply IH.
Qed.

Lemma proper_cons_left_deriv A B Γ C :
  A ⟺ B -> 
  A :: Γ ⟹ C <-> B :: Γ ⟹ C.
Proof.
  move => [HAB HBA]. split.
  * move => HA.
    have HBA' : B :: Γ ⟹ A. { elim Γ => [|D Γ' IH]; auto. by pweak 1. } 
    have HA' : A :: B :: Γ ⟹ C. { by pweak 1. }
    apply (S_cut A [] (B :: Γ)); auto.
  * move => HB.
    have HAB' : A :: Γ ⟹ B. { elim Γ => [|D Γ' IH]; auto. by pweak 1. } 
    have HB' : B :: A :: Γ ⟹ C. { by pweak 1. }
    apply (S_cut B [] (A :: Γ)); auto.
Qed.

Lemma proper_app_deriv : ∀ Γ Γ' Δ C,
  Forall2 eqderiv Γ Γ' ->
  Δ ++ Γ ⟹ C <-> Δ ++ Γ' ⟹ C.
Proof.
  induction Γ, Γ'; move => Δ C Heq; try inv Heq; auto.
  move: a f H2 H4 => B B' HB HΓ.
  split; move => H.
  * specialize (IHΓ Γ' (B :: Δ) C HΓ).
    list_simplifier.
    have Hperm1 : Δ ++ B :: Γ ≡ₚ B :: Δ ++ Γ. { by solve_Permutation. }
    have Hperm2 : B' :: Δ ++ Γ' ≡ₚ Δ ++ B' :: Γ'. { by solve_Permutation. }
    apply (S_perm _ _ _ Hperm2).
    rewrite -(proper_cons_left_deriv _ _ _ _ HB).
    have H' : B :: Δ ++ Γ ⟹ C. { by apply (S_perm _ _ _ Hperm1). }
    by apply IHΓ.
  * specialize (IHΓ Γ' (B' :: Δ) C HΓ).
    list_simplifier.
    have Hperm1 : Δ ++ B :: Γ ≡ₚ B :: Δ ++ Γ. { by solve_Permutation. }
    have Hperm2 : B' :: Δ ++ Γ' ≡ₚ Δ ++ B' :: Γ'. { by solve_Permutation. }
    symmetry in Hperm1. apply (S_perm _ _ _ Hperm1). 
    rewrite (proper_cons_left_deriv _ _ _ _ HB).
    have H' : B' :: Δ ++ Γ' ⟹ C. { symmetry in Hperm2. by apply (S_perm _ _ _ Hperm2). }
    by apply IHΓ.
Qed.

Add Parametric Morphism : deriv with signature
  Forall2 eqderiv ==> eqderiv ==> iff
  as proper_deriv_concl.
Proof.
  move => Γ Δ HΓΔ C D [HCD HDC].
  move: Γ Δ HΓΔ.
  induction Γ, Δ; intros; try inv HΓΔ.
  * split; move => H. by apply (S_cut C [] []). by apply (S_cut D [] []).
  * move: a f H2 H4 => E F HEF HΓΔ.
    pose proof (H := IHΓ _ HΓΔ); case: H => [H1 H2].
    split; move => H.
    - apply (S_cut C [] (F :: Δ)).
      { apply (proper_cons_left_deriv E F); auto.
        apply (proper_app_deriv Γ Δ [E]); auto. }
      pweak 1. elim Δ => [|? ? ?]; auto. by pweak 1.
    - apply (S_cut D [] (E :: Γ)).
      { apply (proper_cons_left_deriv E F); auto.
        apply (proper_app_deriv Δ Γ [F]); auto.
        by symmetry in HΓΔ. }
      pweak 1. elim Γ => [|? ? ?]; auto. by pweak 1.
Qed.

Lemma eqderiv_Forall {A} (f g : A -> form):
  (∀ x, f x ⟺ g x) ->
  ∀ l, Forall (λ x, f x ⟺ g x) l.
Proof.
  move => H. elim => [|x l IH] //=.
Qed.

Lemma eqderiv_map {A} (f g : A -> form) :
  (∀ x, f x ⟺ g x) ->
  ∀ l, Forall2 eqderiv (f <$> l) (g <$> l).
Proof.
  move => H. elim => [|x l IH] //=.
Qed.

(** * Some useful tautologies *)

Section Tautos.

#[local] Ltac L := pleft.
#[local] Ltac R := pright.

Lemma true_and A :
  A ∧ ⊤ ⟺ A.
Proof.
  eqd.
Qed.

Lemma true_or A :
  A ∨ ⊤ ⟺ ⊤.
Proof.
  eqd. R.
Qed.

Lemma true_imp_l A :
  ⊤ ⊃ A ⟺ A.
Proof.
  eqd. pimpL 0; isrch.
Qed.

Lemma true_imp_r A :
  A ⊃ ⊤ ⟺ ⊤.
Proof.
  eqd.
Qed.

Lemma true_forall :
  #∀ ⊤ ⟺ ⊤.
Proof.
  eqd.
Qed.

Lemma true_nforall : ∀ n,
  n#∀ ⊤ ⟺ ⊤.
Proof.
  elim => [|n IHn] //=.
  rewrite IHn. eqd.
Qed.

Lemma false_and A :
  A ∧ ⊥ ⟺ ⊥.
Proof.
  eqd.
Qed.

Lemma false_or A :
  A ∨ ⊥ ⟺ A.
Proof.
  eqd. L.
Qed.

Lemma and_comm A B :
  A ∧ B ⟺ B ∧ A.
Proof.
  eqd.
Qed.

Lemma and_assoc A B C :
  A ∧ B ∧ C ⟺ (A ∧ B) ∧ C.
Proof.
  eqd.
Qed.

Lemma or_comm A B :
  A ∨ B ⟺ B ∨ A.
Proof.
  eqd. R. L. R. L.
Qed.

Lemma or_assoc A B C :
  A ∨ B ∨ C ⟺ (A ∨ B) ∨ C.
Proof.
  eqd. L; L. L; R. R. L. R; L. R; R.
Qed.

Lemma And_app Γ Δ :
  ⋀ (Γ ++ Δ) ⟺ ⋀ Γ ∧ ⋀ Δ.
Proof.
  rewrite /And foldr_app -/And.
  elim: Γ => [|A Γ IH] //=. eqd.
  rewrite IH. eqd.
Qed.

Lemma Or_app Γ Δ :
  ⋁ (Γ ++ Δ) ⟺ ⋁ Γ ∨ ⋁ Δ.
Proof.
  rewrite /Or foldr_app -/Or.
  elim: Γ => [|A Γ IH] //=. eqd. R.
  rewrite IH. eqd.
  L; L. L; R. R. L; L. R; L. R; R.
Qed.

Lemma And_singl A :
  ⋀ [A] ⟺ A.
Proof.
  by rewrite /= true_and.
Qed.

Lemma Or_singl A :
  ⋁ [A] ⟺ A.
Proof.
  by rewrite /= false_or.
Qed.

Lemma currying A B C :
  A ∧ B ⊃ C ⟺ A ⊃ B ⊃ C.
Proof.
  eqd.
  pimpL 2; isrch.
  pimpL 2; isrch.
  pimpL 2; isrch.
Qed.

Lemma and_or_distr A B C :
  A ∧ (B ∨ C) ⟺ A ∧ B ∨ A ∧ C.
Proof.
  eqd. L. R. L. R.
Qed.

Lemma or_imp_distr A B C :
  (A ∨ B) ⊃ C ⟺ (A ⊃ C) ∧ (B ⊃ C).
Proof.
  eqd.
  pimpL 1; isrch. L.
  pimpL 1; isrch. R.
  pimpL 1; isrch.
  pimpL 2; isrch.
Qed.

Lemma imp_and_distr A B C :
  A ⊃ B ∧ C ⟺ (A ⊃ B) ∧ (A ⊃ C).
Proof.
  eqd.
  pimpL 1; isrch.
  pimpL 1; isrch.
  pimpL 1; isrch.
  pimpL 2; isrch.
Qed.

Lemma wpol_imp_l A B C :
  A ∧ (B ⊃ C) ⟺ A ∧ (A ∧ B ⊃ C).
Proof.
  eqd.
  pimpL 3; isrch.
  pimpL 2; isrch.
Qed.

Lemma wpol_imp_r A B C :
  A ∧ (B ⊃ C) ⟺ A ∧ (B ⊃ A ∧ C).
Proof.
  eqd.
  pimpL 2; isrch.
  pimpL 2; isrch.
Qed.

Lemma wpol_And A : ∀ Γ,
  A ∧ ⋀ Γ ⟺ A ∧ ⋀ ((λ B, A ∧ B) <$> Γ).
Proof.
  elim => [|C Γ [IHl IHr]] //=.
  rewrite [A ∧ _]and_assoc [A ∧ _]and_comm -[_ ∧ ⋀ Γ]and_assoc.
  rewrite [A ∧ (C ∧ _) ∧ _]and_assoc [A ∧ C ∧ _]and_assoc -[((A ∧ C) ∧ _) ∧ _]and_assoc.
  split.
  - pintroR. isrch.
    pintroL 0. by pweak 0.
  - pintroR. pintroL 0. pintroL 0. pweak 0. passum.
    pintroL 0. by pweak 0.
Qed.

Lemma wpol_Or {T} A (f : T -> form) : ∀ Γ,
  A ∧ ⋁ (f <$> Γ) ⟺ A ∧ ⋁ ((λ B, A ∧ f B) <$> Γ).
Proof.
  elim => [|C Γ [IHl IHr]]; split; list_simplifier; isrch.
  * pleft; isrch.
  * pright.
    apply (S_cut (A ∧ ⋁ (f <$> Γ)) []); simpl. isrch.
    apply (S_cut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)) []); simpl. pweak 1. by pweak 1.
    pintroL 0. cbv; passum.
  * pleft; isrch.
  * pright.
    apply (S_cut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)) []). cbv; isrch.
    pweak 1. pweak 1.
    apply (S_cut (A ∧ ⋁ (f <$> Γ)) []). assumption.
    pweak 1. isrch.
Qed.

Lemma wpol_exists A B :
  A ∧ #∃ B ⟺ #∃ ((fshift 1 0 A) ∧ B).
Proof.
  eqd.
  * pexR (TVar 0). simpl.
    repeat rewrite fsubst_fshift funshift_fshift. isrch.
  * pexR (TVar 0). simpl.
    repeat rewrite fsubst_fshift funshift_fshift. isrch.
Qed. 

Lemma wpol_nexists n : ∀ A B,
  A ∧ n#∃ B ⟺ n#∃ ((fshift n 0 A) ∧ B).
Proof.
  elim: n => [A B |n IH A B] //=.
  by rewrite fshift_zero.
  rewrite wpol_exists.
  apply proper_exists.
  rewrite IH.
  rewrite [_ (S n) _ _]fshift_succ.
  by rewrite fshift_comm.
Qed.

Lemma wpol_forall A B :
  A ∧ #∀ B ⟺ #∀ ((fshift 1 0 A) ∧ B).
Proof.
  eqd.
  * pfaL 1 (TVar 0).
    repeat rewrite fsubst_fshift funshift_fshift. isrch.
  * pfaL 0 (TVar 0).
    rewrite (fsubst_fshift_vacuous A 0 _ 1 0); [> lia | ..].
    rewrite funshift_fshift. isrch.
  * pfaL 0 (TVar 0).
    repeat rewrite fsubst_fshift funshift_fshift. isrch.
Qed.

Lemma wpol_nforall n : ∀ A B,
  A ∧ n#∀ B ⟺ n#∀ ((fshift n 0 A) ∧ B).
Proof.
  elim: n => [A B |n IH A B] //=.
  by rewrite fshift_zero.
  rewrite wpol_forall.
  apply proper_forall.
  rewrite IH.
  rewrite [_ (S n) _ _]fshift_succ.
  by rewrite fshift_comm.
Qed.

Lemma spol_r A B :
  A ⊃ B ⟺ A ⊃ A ∧ B.
Proof.
  eqd.
  pimpL 1; isrch.
  pimpL 1; isrch.
Qed.

Lemma and_intro_r_msucc A B C D :
  A ⊃ B ∧ C ∨ D ⟺ (A ⊃ B ∨ D) ∧ (A ⊃ C ∨ D).
Proof.
  eqd.
  pimpL 1; isrch. L. R.
  pimpL 1; isrch. L. R.
  pimpL 1; isrch. pimpL 2; isrch. L. R.
  pimpL 2; isrch. R. R.
Qed.

Lemma or_intro_l_nary {T} (f : T -> form) : ∀ l (A B : form),
  A ⊃ ⋀ ((λ x, f x ⊃ B) <$> l) ⟺
  A ∧ ⋁ (f <$> l) ⊃ B.
Proof.
  elim => [|x l IH]; intros.
  * simpl. eqd.
  * rewrite fmap_cons (cons_app (f x ⊃ B)) And_app And_singl.
    rewrite fmap_cons (cons_app (f x)) Or_app Or_singl.
    rewrite currying or_imp_distr [A ⊃ _ ∧ (_ ⊃ _)]imp_and_distr.
    rewrite -[A ⊃ (⋁ _) ⊃ B]currying -IH.
    by rewrite -imp_and_distr.
Qed.

Lemma imp_intro_r_inv A Γ C :
  Γ ⟹ A ⊃ C ->
  A :: Γ ⟹ C.
Proof.
  move => H.
  apply (S_cut (A ⊃ C) []). by pweak 0. pimpL 0; passum.
Qed.

Lemma proper_concl C A B B' :
  A ⊃ B ⟺ A ⊃ B' ->
  A ⊃ (C ∨ B) ⟺ A ⊃ (C ∨ B').
Proof.
  move => H. eqd.
  pimpL 1; isrch. L. R. apply imp_intro_r_inv. rewrite -H. isrch.
  pimpL 1; isrch. L. R. apply imp_intro_r_inv. rewrite H. isrch.
Qed.

Lemma nforall_one A :
  #∀ A = 1#∀ A.
Proof.
  done.
Qed.

Lemma nexists_one A :
  #∃ A = 1#∃ A.
Proof.
  done.
Qed.

Lemma nforall_add : ∀ n m A,
  n#∀ (m#∀ A) = (n + m)#∀ A.
Proof.
  elim => [|n IHn] m A //=. by rewrite IHn.
Qed.

Lemma nexists_add : ∀ n m A,
  n#∃ (m#∃ A) = (n + m)#∃ A.
Proof.
  elim => [|n IHn] m A //=. by rewrite IHn.
Qed.

Lemma forall_vacuous A :
  A ⟺ #∀ (fshift 1 0 A).
Proof.
  eqd.
  * passum.
  * pfaL 0 (TVar 0).
    rewrite (fsubst_fshift_vacuous A 0); first lia.
    rewrite funshift_fshift; passum.
Qed.

Lemma nforall_vacuous : ∀ n A,
  A ⟺ n#∀ (fshift n 0 A).
Proof.
  elim => [|n IHn] A //=.
  by rewrite fshift_zero.
  specialize (IHn A). rewrite {1}IHn.
  rewrite fshift_succ.
  rewrite nforall_one nforall_add Nat.add_comm -nforall_add /=.
  by rewrite -forall_vacuous.
Qed.

Lemma exists_vacuous A :
  A ⟺ #∃ (fshift 1 0 A).
Proof.
  eqd.
  pexR (TVar 0).
  rewrite (fsubst_fshift_vacuous A 0); first lia.
  rewrite funshift_fshift; passum.
Qed.

Lemma nexists_vacuous : ∀ n A,
  A ⟺ n#∃ (fshift n 0 A).
Proof.
  elim => [|n IHn] A //=.
  by rewrite fshift_zero.
  specialize (IHn A). rewrite {1}IHn.
  rewrite fshift_succ.
  rewrite nexists_one nexists_add Nat.add_comm -nexists_add /=.
  by rewrite -exists_vacuous.
Qed.

Lemma exists_intro_l : ∀ A B,
  #∃ A ⊃ B ⟺
  #∀ (A ⊃ fshift 1 0 B).
Proof.
  intros; eqd.

  pimpL 1. pexR (TVar 0).
  rewrite fsubst_fshift_vacuous2 funshift_fshift /=. passum.

  passum.

  pfaL 1 (TVar 0).
  rewrite fsubst_fshift_vacuous2 funshift_fshift /=.
  pimpL 1; first passum.
  rewrite fsubst_fshift_vacuous2 funshift_fshift /=.
  passum.
Qed.

Lemma nexists_intro_l : ∀ n A B,
  n#∃ A ⊃ B ⟺
  n#∀ (A ⊃ fshift n 0 B).
Proof.
  elim => [|n IHn] A B //=.
  by rewrite fshift_zero.
  rewrite exists_intro_l.
  apply proper_forall.
  specialize (IHn A (fshift 1 0 B)).
  by rewrite [_ (S n) _ _]fshift_succ fshift_comm.
Qed.

Lemma forall_imp_switch_r A B :
  #∀ ((fshift 1 0 A) ⊃ B) ⟺ A ⊃ #∀ B.
Proof.
  eqd.
  * pfaL 1 (TVar 0).
    rewrite fsubst_fshift_vacuous2 funshift_fshift.
    pimpL 1; isrch.
    rewrite fsubst_fshift_vacuous2 funshift_fshift.
    passum.
  * pimpL 1; isrch.
    pfaL 1 (TVar 0).
    rewrite fsubst_fshift_vacuous2 funshift_fshift.
    passum.
Qed.

Lemma nforall_imp_switch_r : ∀ n A B,
  n#∀ ((fshift n 0 A) ⊃ B) ⟺ A ⊃ n#∀ B.
Proof.
  elim => [|n IHn] A B /=.
  by rewrite fshift_zero.
  assert (H : S n = n + 1). { lia. }
  rewrite H fshift_add IHn.
  by rewrite forall_imp_switch_r.
Qed.

Lemma exists_or_switch_r A B :
  #∃ ((fshift 1 0 A) ∨ B) ⟺ A ∨ #∃ B.
Proof.
  eqd.
  * L.
  * R. pexR (TVar 0).
    rewrite fsubst_fshift_vacuous2 funshift_fshift.
    passum.
  * pexR (TVar 0). rewrite /=. L.
    rewrite (fsubst_fshift_vacuous A 0); first lia.
    rewrite funshift_fshift.
    passum.
  * pexR (TVar 0). rewrite /=. R.
    rewrite fsubst_fshift_vacuous2.
    rewrite funshift_fshift.
    passum.
Qed.

Lemma exists_and_switch_r A B :
  #∃ ((fshift 1 0 A) ∧ B) ⟺ A ∧ #∃ B.
Proof.
  eqd.
  * pexR (TVar 0).
    rewrite fsubst_fshift_vacuous2 funshift_fshift.
    passum.
  * pexR (TVar 0). rewrite /=.
    repeat rewrite fsubst_fshift_vacuous2 funshift_fshift.
    isrch.
Qed.

Lemma nexists_and_switch_r : ∀ n A B,
  n#∃ ((fshift n 0 A) ∧ B) ⟺ A ∧ n#∃ B.
Proof.
  elim => [|n IHn] A B /=.
  by rewrite fshift_zero.
  assert (H : S n = n + 1). { lia. }
  rewrite H fshift_add IHn.
  by rewrite exists_and_switch_r.
Qed.

Lemma forall_elim A t :
  [#∀ A] ⟹ funshift 1 0 (fsubst (0 ↦ tshift 1 0 t) A).
Proof.
  pfaL 0 t; isrch.
Qed.

Lemma nforall_elim : ∀ n A t i,
  0 <= i <= n ->
  [(S n)#∀ A] ⟹ n#∀ (funshift 1 i (fsubst (i ↦ tshift (S n) 0 t) A)).
Proof.
  elim => [|n IHn] A t i Hi /=.
  assert (H : i = 0). { lia. }
  rewrite H. pfaL 0 t. isrch.
  case (nat_eq_dec i (S n)) => Heqi.
  * rewrite Heqi /=.
    pose proof (Hcut := forall_elim (n#∀ #∀ A) t).
    rewrite fsubst_nforall /= in Hcut.
    rewrite [_ (fsubst _ _)]nforall_one in Hcut.
    rewrite nforall_add Nat.add_comm -nforall_add /= in Hcut.
    rewrite funshift_nforall /= in Hcut.
    rewrite -sshift_add sshift_mksubst -tshift_add Nat.add_1_r /= in Hcut.
    rewrite [#∀ (n#∀ A)]nforall_one nforall_add Nat.add_comm -nforall_add /=.
    done.
  * isrch. pfaL 0 (TVar 0).
    rewrite sshift_mksubst fsubst_fshift funshift_fshift.
    rewrite nforall_one nforall_add -[1 + n]/(S n).
    assert (H : 0 <= i <= n); first lia.
    specialize (IHn A (tshift 1 0 t) i H).
    rewrite -tshift_add in IHn.
    assert (HSn : S n + 1 = S (S n)); first lia; rewrite HSn in IHn; clear HSn.
    done.
Qed.

Lemma exists_intro A t :
  [funshift 1 0 (fsubst (0 ↦ tshift 1 0 t) A)] ⟹ #∃ A.
Proof.
  pexR t; isrch.
Qed.

Lemma nexists_intro : ∀ n A t i,
  0 <= i <= n ->
  [n#∃ (funshift 1 i (fsubst (i ↦ tshift (S n) 0 t) A))] ⟹ (S n)#∃ A.
Proof.
  elim => [|n IHn] A t i Hi /=.
  assert (H : i = 0). { lia. }
  rewrite H. pexR t; isrch.
  case (nat_eq_dec i (S n)) => Heqi.
  * rewrite Heqi.
    pose proof (Hcut := exists_intro (#∃ (n#∃ A)) t).
    rewrite /= fsubst_nexists funshift_nexists /= in Hcut.
    rewrite -sshift_add sshift_mksubst -tshift_add in Hcut.
    by rewrite Nat.add_1_r Nat.add_1_r /= in Hcut.
  * isrch. pexR (TVar 0). rewrite /=.
    rewrite sshift_mksubst /=.
    rewrite fsubst_fshift funshift_fshift.
    rewrite nexists_one nexists_add -[1 + n]/(S n).
    assert (H : 0 <= i <= n); first lia.
    specialize (IHn A (tshift 1 0 t) i H).
    rewrite -tshift_add in IHn.
    assert (HSn : S n + 1 = S (S n)); first lia; rewrite HSn in IHn; clear HSn.
    done.
Qed.

End Tautos.

(** Admissibility of structural rules *)

(* Here the structural rules comprise cut, weakening and exchange *)

Lemma structural_admissibility Γ C :
  Γ ⟹ C -> Γ s⟹ C.
  (* It would be a lot of formalization effort, so we rely on the literature and
    trust that our particular choices of presentation do not pose any problem. *)
Admitted.

(** Deduction theorem *)

Lemma deduction A B :
  [A] ⟹ B <-> [] ⟹ A ⊃ B.
Proof.
  split; move => H.
  * isrch.
  * by apply imp_intro_r_inv.
Qed.

(** * Fun facts *)

Lemma contraction_cut A Γ C :
  A :: A :: Γ ⟹ C ->
  A :: Γ ⟹ C.
Proof.
  move => H. apply (S_cut A []). apply S_ax. exact H.
Qed.