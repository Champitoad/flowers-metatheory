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
  Γ ⟹ funshift 1 0 (fsubst 0 (tshift 1 0 t) C) ->
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
  Γ ++ funshift 1 0 (fsubst 0 (tshift 1 0 t) A) :: Γ' ⟹ C ->
  Γ ++ #∀ A :: Γ' ⟹ C

| S_L_exists A Γ Γ' C :
  (fshift 1 0 <$> Γ) ++ A :: (fshift 1 0 <$> Γ') ⟹ fshift 1 0 C ->
  Γ ++ #∃ A :: Γ' ⟹ C

where "Γ ⟹ C" := (deriv Γ C).

(** ** Cut-free derivations *)

Reserved Infix "c⟹" (at level 90).

Inductive cderiv : list form -> form -> Prop :=

(** ** Identity *)

| Sc_ax A Γ Γ' :
  Γ ++ A :: Γ' c⟹ A

(** ** Structural rules *)

| Sc_contr_r A Γ Γ' Γ'' C :
  Γ ++ A :: Γ' ++ A :: Γ'' c⟹ C -> 
  Γ ++ Γ' ++ A :: Γ'' c⟹ C

| Sc_contr_l A Γ Γ' Γ'' C :
  Γ ++ A :: Γ' ++ A :: Γ'' c⟹ C -> 
  Γ ++ A :: Γ' ++ Γ'' c⟹ C

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

| Sc_L_true Γ Γ' C :
  Γ ++ Γ' c⟹ C ->
  Γ ++ ⊤ :: Γ' c⟹ C

| Sc_L_false Γ Γ' C :
  Γ ++ ⊥ :: Γ' c⟹ C

| Sc_L_and A B Γ Γ' C :
  Γ ++ A :: B :: Γ' c⟹ C ->
  Γ ++ (A ∧ B) :: Γ' c⟹ C

| Sc_L_or A B Γ Γ' C :
  Γ ++ A :: Γ' c⟹ C -> Γ ++ B :: Γ' c⟹ C ->
  Γ ++ (A ∨ B) :: Γ' c⟹ C

| Sc_L_imp A B Γ Γ' C :
  Γ ++ Γ' c⟹ A -> Γ ++ B :: Γ' c⟹ C ->
  Γ ++ (A ⊃ B) :: Γ' c⟹ C

| Sc_L_forall A t Γ Γ' C :
  Γ ++ funshift 1 0 (fsubst 0 (tshift 1 0 t) A) :: Γ' c⟹ C ->
  Γ ++ #∀ A :: Γ' c⟹ C

| Sc_L_exists A Γ Γ' C :
  (fshift 1 0 <$> Γ) ++ A :: (fshift 1 0 <$> Γ') c⟹ fshift 1 0 C ->
  Γ ++ #∃ A :: Γ' c⟹ C

where "Γ c⟹ C" := (cderiv Γ C).

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
          in apply rule
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
          in apply rule
      end
  end.

Ltac pfaL i t :=
  match goal with
  | |- ?Γ ⟹ _ => 
      let X := eval cbn in (split_at i Γ) in
      match X with
      | Some (?Γl, ?A :: ?Γr) =>
          let rule :=
            match X with
            | #∀ ?A =>
                let r := eval simpl in (S_L_forall A t) in r
            end
          in apply rule
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
    - pleft. apply H.
    - pright. by apply IHA.
    - pleft. apply H.
    - pright. by apply IHA.
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
    (* have Hperm1 : Δ ++ B :: Γ ≡ₚ B :: Δ ++ Γ. { by solve_Permutation. }
    have Hperm2 : B' :: Δ ++ Γ' ≡ₚ Δ ++ B' :: Γ'. { by solve_Permutation. } *)
    (* apply (S_perm _ _ _ Hperm2).  *)
    (* rewrite -(proper_cons_left_deriv _ _ _ _ HB).
    have H' : B :: Δ ++ Γ ⟹ C. { by apply (S_perm _ _ _ Hperm1). }
    by apply IHΓ.
  * specialize (IHΓ Γ' (B' :: Δ) C HΓ).
    list_simplifier.
    have Hperm1 : Δ ++ B :: Γ ≡ₚ B :: Δ ++ Γ. { by solve_Permutation. }
    have Hperm2 : B' :: Δ ++ Γ' ≡ₚ Δ ++ B' :: Γ'. { by solve_Permutation. }
    symmetry in Hperm1. apply (S_perm _ _ _ Hperm1). 
    rewrite (proper_cons_left_deriv _ _ _ _ HB).
    have H' : B' :: Δ ++ Γ' ⟹ C. { symmetry in Hperm2. by apply (S_perm _ _ _ Hperm2). }
    by apply IHΓ. *)
Admitted.

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
  * pleft; isrch.
  * pright.
    pcut (A ∧ ⋁ (f <$> Γ)). isrch.
    pcut (A ∧ ⋁ ((λ x, A ∧ f x) <$> Γ)). pweak 1. by pweak 1.
    pintroL 0. cbv; passum.
  * pleft; isrch.
  * pright.
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