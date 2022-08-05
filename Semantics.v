Require Import String Setoid.
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

Notation "⋀ As" := (And As) (at level 5).
Notation "⋁ As" := (Or As) (at level 5).

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

Fixpoint fsubst (n : nat) (u : term) (A : form) : form :=
  match A with
  | FAtom p args => FAtom p (tsubst n u <$> args)
  | FTrue | FFalse => A
  | FAnd A B => FAnd (fsubst n u A) (fsubst n u B)
  | FOr A B => FOr (fsubst n u A) (fsubst n u B)
  | FImp A B => FImp (fsubst n u A) (fsubst n u B)
  | FForall A => FForall (fsubst (n+1) (tshift 1 0 u) A)
  | FExists A => FExists (fsubst (n+1) (tshift 1 0 u) A)
  end.

(** * Rules *)

Reserved Infix "⟹" (at level 90).

Inductive deriv : list form -> form -> Prop :=

(** ** Identity *)

| S_ax A Γ :
  A :: Γ ⟹ A

| S_cut A Γ C :
  Γ ⟹ A -> A :: Γ ⟹ C ->
  Γ ⟹ C

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
  Γ ⟹ funshift 1 0 (fsubst 0 (tshift 1 0 t) C) ->
  Γ ⟹ #∃ C

(** ** Left rules *)

| S_L_true Γ C :
  Γ ⟹ C ->
  ⊤ :: Γ ⟹ C

| S_L_false Γ C :
  ⊥ :: Γ ⟹ C

| S_L_and A B Γ C :
  A :: B :: Γ ⟹ C ->
  (A ∧ B) :: Γ ⟹ C

| S_L_or A B Γ C :
  A :: Γ ⟹ C -> B :: Γ ⟹ C ->
  (A ∨ B) :: Γ ⟹ C

| S_L_imp A B Γ C :
  Γ ⟹ A -> B :: Γ ⟹ C ->
  (A ⊃ B) :: Γ ⟹ C

| S_L_forall A t Γ C :
  funshift 1 0 (fsubst 0 (tshift 1 0 t) A) :: Γ ⟹ C ->
  #∀ A :: Γ ⟹ C

| S_L_exists A Γ C :
  A :: (fshift 1 0 <$> Γ) ⟹ fshift 1 0 C ->
  #∃ A :: Γ ⟹ C

(** ** Permutation *)

| S_perm Γ Γ' C :
  Γ ≡ₚ Γ' ->
  Γ ⟹ C ->
  Γ' ⟹ C

where "Γ ⟹ C" := (deriv Γ C).

(** ** Cut-free derivations *)

Reserved Infix "c⟹" (at level 90).

Inductive cderiv : list form -> form -> Prop :=

(** ** Identity *)

| Sc_ax A Γ :
  A :: Γ c⟹ A

(** ** Right rules *)

| Sc_R_true Γ :
  Γ c⟹ ⊤

| Sc_R_and A B Γ :
  Γ c⟹ A -> Γ c⟹ B ->
  Γ c⟹ A ∧ B

| Sc_R_or_l A B Γ :
  Γ c⟹ A ->
  Γ c⟹ A ∨ B

| Sc_R_or_r A B Γ :
  Γ c⟹ B ->
  Γ c⟹ A ∨ B

| Sc_R_imp A B Γ :
  A :: Γ c⟹ B ->
  Γ c⟹ A ⊃ B

| Sc_R_forall Γ C :
  (fshift 1 0 <$> Γ) c⟹ C ->
  Γ c⟹ #∀ C

| Sc_R_exists t Γ C :
  Γ c⟹ funshift 1 0 (fsubst 0 (tshift 1 0 t) C) ->
  Γ c⟹ #∃ C

(** ** Left rules *)

| Sc_L_true Γ C :
  Γ c⟹ C ->
  ⊤ :: Γ c⟹ C

| Sc_L_false Γ C :
  ⊥ :: Γ c⟹ C

| Sc_L_and A B Γ C :
  A :: B :: Γ c⟹ C ->
  (A ∧ B) :: Γ c⟹ C

| Sc_L_or A B Γ C :
  A :: Γ c⟹ C -> B :: Γ c⟹ C ->
  (A ∨ B) :: Γ c⟹ C

| Sc_L_imp A B Γ C :
  Γ c⟹ A -> B :: Γ c⟹ C ->
  (A ⊃ B) :: Γ c⟹ C

| Sc_L_forall A t Γ C :
  funshift 1 0 (fsubst 0 (tshift 1 0 t) A) :: Γ c⟹ C ->
  #∀ A :: Γ c⟹ C

| Sc_L_exists A Γ C :
  A :: (fshift 1 0 <$> Γ) c⟹ fshift 1 0 C ->
  #∃ A :: Γ c⟹ C

(** ** Contraction *)

| Sc_contr A Γ C :
  A :: A :: Γ c⟹ C ->
  A :: Γ c⟹ C

(** ** Permutation *)

| Sc_perm Γ Γ' C :
  Γ ≡ₚ Γ' ->
  Γ c⟹ C ->
  Γ' c⟹ C

where "Γ c⟹ C" := (cderiv Γ C).

(** * Basic proof search *)

Ltac permute A :=
  match goal with
  | |- _ ⟹ _ => eapply (S_perm (A :: _) _ _); [> econs; try solve_Permutation | ..]
  end.

Ltac permuti i :=
  match goal with
  | |- ?Γ ⟹ _ =>
      let X := eval simpl in (nth i Γ ⊤) in
      permute X
  end.

Ltac passum :=
  match goal with
  | |- ?Γ ⟹ ?C =>
      let rec aux Δ n :=
        match Δ with
        | ?C :: ?Δ => apply S_ax
        | _ :: ?Δ =>
            let i := constr:(S n) in
            permuti i; aux Δ i
        end
      in 
      aux Γ 0
  end.

Ltac pintroL i :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval simpl in (nth i Γ ⊤) in
      let rule :=
        match X with
        | ⊤ => S_L_true
        | ⊥ => S_L_false
        | _ ∧ _ => S_L_and
        | _ ∨ _ => S_L_or
        | #∃ _ => S_L_exists
        end
      in permute X; apply rule
  end.

Ltac pimpL i :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval simpl in (nth i Γ ⊤) in
      let rule :=
        match X with
        | _ ⊃ _ => S_L_imp
        end
      in permute X; apply rule
  end.

Ltac pfaL i t :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval simpl in (nth i Γ ⊤) in
      let rule :=
        match X with
        | #∀ ?A =>
            let r := eval simpl in (S_L_forall A t) in r
        end
      in permute X; apply rule
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
      introΓ n
  end.

Ltac eqd := split; isrch.

Ltac pleft := apply S_R_or_l; isrch.
Ltac pright := apply S_R_or_r; isrch.

Lemma tshift_zero c : ∀ t,
  tshift 0 c t = t.
Proof.
  induction t as [|?? IH] using term_induction; simpl.
  * destruct (n <? c); auto.
  * f_equal. rewrite Forall_eq_map in IH.
    by rewrite list_fmap_id in IH.
Qed.

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

Lemma shift_weakening Γ C (π : Γ ⟹ C) : ∀ D n,
  (fshift n 0 D) :: Γ ⟹ C.
Proof.
  induction π; intros.
  * isrch.
  * have IHπ2' : A :: fshift n 0 D :: Γ ⟹ C.
    { permute (fshift n 0 D). apply IHπ2. }
    by apply (S_cut A).
  * isrch.
  * isrch.
  * by apply S_R_or_l.
  * by apply S_R_or_r.
  * pintroR. by permute (fshift n 0 D).
  * pintroR. by rewrite fmap_cons.
  * by pexR t.
  * by pintroL 1.
  * by pintroL 1.
  * pintroL 1.
    apply (S_perm (fshift n 0 D :: A :: B :: Γ)); auto. solve_Permutation.
  * pintroL 1; by permuti 1.
  * pimpL 1; auto. by permuti 1.
  * pfaL 1 t. by permuti 1.
  * pintroL 1. by permuti 1.
  * apply (S_perm (fshift n 0 D :: Γ)); auto.
Qed.

Lemma weakening Γ C (π : Γ ⟹ C) D :
  D :: Γ ⟹ C.
Proof.
  pose proof (H := shift_weakening Γ C π D 0).
  rewrite fshift_zero in H. by apply H.
Qed.

Ltac pweak i :=
  permuti i; apply weakening.

Ltac pcut A := apply (S_cut A).

(** * Generalized rewriting of equiderivable formulas *)

Definition eqderiv (A B : form) : Prop :=
  ([A] ⟹ B) /\ ([B] ⟹ A).

Infix "⟺" := eqderiv (at level 95).

#[export] Instance equiv_eqderiv : Equivalence eqderiv.
Proof.
  econs; repeat red.
  * move => A. split; apply S_ax.
  * move => A B [HAB HBA]; done.
  * move => A B C [HAB HBA] [HBC HCB]. split.
    pcut B; auto. by pweak 1.
    pcut B; auto. by pweak 1.
Qed.

#[export] Instance : Equiv form := eqderiv.

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
  * isrch.
    by apply S_R_or_l.
    by apply S_R_or_r.
  * isrch.
    by apply S_R_or_l.
    by apply S_R_or_r.
Qed.

Add Morphism FImp with signature
  eqderiv ==> eqderiv ==> eqderiv
  as proper_imp.
Proof.
  move => A B [HAB HBA] C D [HCD HDC].
  split.
  * isrch. pimpL 1. exact. by pweak 1.
  * isrch. pimpL 1. exact. by pweak 1.
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

Add Morphism Or with signature
  Forall2 eqderiv ==> eqderiv
  as proper_Or.
Proof.
  elim => [|A As IHA] //=.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isrch.
  * elim => [H |B Bs IHB H] //=; split; decompose_Forall_hyps; isrch.
    - apply S_R_or_l. apply H.
    - apply S_R_or_r. by apply IHA.
    - apply S_R_or_l. apply H.
    - apply S_R_or_r. by apply IHA.
Qed.

Lemma proper_cons_left_deriv A B Γ C :
  A ⟺ B -> 
  A :: Γ ⟹ C <-> B :: Γ ⟹ C.
Proof.
  move => [HAB HBA]. split.
  * move => HA.
    have HBA' : B :: Γ ⟹ A. { elim Γ => [|D Γ' IH]; auto. by pweak 1. } 
    have HA' : A :: B :: Γ ⟹ C. { by pweak 1. }
    by pcut A.
  * move => HB.
    have HAB' : A :: Γ ⟹ B. { elim Γ => [|D Γ' IH]; auto. by pweak 1. } 
    have HB' : B :: A :: Γ ⟹ C. { by pweak 1. }
    by pcut B.
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
  * split; move => H. by pcut C. by pcut D.
  * move: a f H2 H4 => E F HEF HΓΔ.
    pose proof (H := IHΓ _ HΓΔ); case: H => [H1 H2].
    split; move => H.
    - pcut C.
      { apply (proper_cons_left_deriv E F); auto.
        apply (proper_app_deriv Γ Δ [E]); auto. }
      pweak 1. elim Δ => [|? ? ?]; auto. by pweak 1.
    - pcut D.
      { apply (proper_cons_left_deriv E F); auto.
        apply (proper_app_deriv Δ Γ [F]); auto.
        by symmetry in HΓΔ. }
      pweak 1. elim Γ => [|? ? ?]; auto. by pweak 1.
Qed.

Lemma eqderiv_Forall {A} (f g : A -> form):
  (∀ x, f x ⟺ g x) ->
  ∀ l, Forall (λ x, f x ⟺ g x) l.
Proof.
  move => H. elim => [|x l IH] //=. econs.
Qed.

Lemma eqderiv_map {A} (f g : A -> form) :
  (∀ x, f x ⟺ g x) ->
  ∀ l, Forall2 eqderiv (f <$> l) (g <$> l).
Proof.
  move => H. elim => [|x l IH] //=. econs.
Qed.

(** * Some useful tautologies *)

Section Tautos.

#[local] Ltac L := pleft.
#[local] Ltac R := pright.

Lemma true_and A :
  A ∧ ⊤ ⟺ A.
Proof.
  split; isrch.
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
  rewrite /= true_and. reflexivity.
Qed.

Lemma Or_singl A :
  ⋁ [A] ⟺ A.
Proof.
  rewrite /= false_or. reflexivity.
Qed.

Lemma currying A B C :
  A ∧ B ⊃ C ⟺ A ⊃ B ⊃ C.
Proof.
  eqd.
  permuti 2. Unshelve. 4: exact [B; A]. solve_Permutation. pimpL 0; isrch.
  permuti 2. Unshelve. 3: exact [B; A]. solve_Permutation. pimpL 0; isrch. pimpL 0; isrch.
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
  permuti 2. Unshelve. 3: exact [A ⊃ C; B ⊃ C]. solve_Permutation.
  pintroL 0. pimpL 1; isrch.
  pweak 1. pimpL 1; isrch.
Qed.

Lemma imp_and_distr A B C :
  A ⊃ B ∧ C ⟺ (A ⊃ B) ∧ (A ⊃ C).
Proof.
  eqd.
  pimpL 1; isrch.
  pimpL 1; isrch.
  pimpL 0; isrch.
  pimpL 1; isrch.
Qed.

Lemma wpol_imp_l A B C :
  A ∧ (B ⊃ C) ⟺ A ∧ (A ∧ B ⊃ C).
Proof.
  eqd.
  pimpL 1; isrch.
  pimpL 1; isrch.
Qed.

Lemma wpol_imp_r A B C :
  A ∧ (B ⊃ C) ⟺ A ∧ (B ⊃ A ∧ C).
Proof.
  eqd.
  pimpL 1; isrch.
  pimpL 1; isrch.
Qed.

Lemma wpol_And A : ∀ Γ,
  A ∧ ⋀ Γ ⟺ A ∧ ⋀ ((λ B, A ∧ B) <$> Γ).
Proof.
  elim => [|C Γ [IHl IHr]] //=.
  * eqd.
  * rewrite [A ∧ _]and_assoc [A ∧ _]and_comm -[_ ∧ ⋀ Γ]and_assoc.
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
  * apply S_R_or_l; isrch.
  * apply S_R_or_r.
    pcut (A ∧ ⋁ (f <$> Γ)). isrch.
    pcut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)). pweak 1. by pweak 1.
    pintroL 0. cbv; passum.
  * apply S_R_or_l; isrch.
  * apply S_R_or_r.
    pcut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)). cbv; isrch.
    pweak 1. pweak 1.
    pcut (A ∧ ⋁ (f <$> Γ)). assumption.
    pweak 1. isrch.
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
  pimpL 0; isrch. pimpL 1; isrch. L. R.
  pimpL 1; isrch. R. R.
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
    rewrite -imp_and_distr.
    reflexivity.
Qed.

Lemma imp_intro_r_inv A Γ C :
  Γ ⟹ A ⊃ C ->
  A :: Γ ⟹ C.
Proof.
  move => H.
  pcut (A ⊃ C). by pweak 0. pimpL 0; passum.
Qed.

Lemma proper_concl C A B B' :
  A ⊃ B ⟺ A ⊃ B' ->
  A ⊃ (C ∨ B) ⟺ A ⊃ (C ∨ B').
Proof.
  move => H. eqd.
  pimpL 1; isrch. L. R. permute A. apply imp_intro_r_inv. rewrite -H. isrch.
  pimpL 1; isrch. L. R. permute A. apply imp_intro_r_inv. rewrite H. isrch.
Qed.

End Tautos.

(** * Fun facts *)

Lemma contraction_cut A Γ C :
  A :: A :: Γ ⟹ C ->
  A :: Γ ⟹ C.
Proof.
  move => H. pcut A. apply S_ax. exact H.
Qed.