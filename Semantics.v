Require Import String Setoid.
Require Import stdpp.list.
Require Import ssreflect.

Require Import Flowers.Utils.

(** Our semantics will be the sequent calculus LJ *)

(** * Formulas *)

Inductive form :=
| FAtom : name -> form
| FTrue : form
| FFalse : form
| FAnd : form -> form -> form
| FOr : form -> form -> form
| FImp : form -> form -> form.

Coercion FAtom : name >-> form.

Notation "# a" := (FAtom a) (format "# a", at level 1).
Notation "⊤" := FTrue.
Notation "⊥" := FFalse.
Infix "∧" := FAnd.
Infix "∨" := FOr.
Infix "⊃" := FImp (at level 85, right associativity).

Definition And :=
  foldr FAnd ⊤.

Definition Or :=
  foldr FOr ⊥.

Notation "⋀ As" := (And As) (at level 5).
Notation "⋁ As" := (Or As) (at level 5).

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

(** ** Permutation *)

| S_perm Γ Γ' C :
  Γ ≡ₚ Γ' ->
  Γ ⟹ C ->
  Γ' ⟹ C

where "Γ ⟹ C" := (deriv Γ C).

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

Ltac pintroR :=
  match goal with
  | |- _ ⟹ ?C =>
      let rule :=
        match C with
        | ⊤ => S_R_true
        | _ ∧ _ => S_R_and
        | _ ⊃ _ => S_R_imp
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

Lemma weakening A Γ C :
  Γ ⟹ C ->
  A :: Γ ⟹ C.
Proof.
  elim.
  * move => B Γ'. isrch.
  * move: C => _ B Γ' C Hr Hr' Hl Hl'.
    have Hl'' : B :: A :: Γ' ⟹ C. { by permute A. }
    by apply (S_cut B).
  * move => Γ'. isrch.
  * move => D B Γ' *. isrch.
  * move => D B Γ' *. by apply S_R_or_l.
  * move => D B Γ' *. by apply S_R_or_r.
  * move => D B Γ' *. pintroR. by permute A.
  * move => D B Γ' *. by pintroL 1.
  * move => Γ' D. by pintroL 1.
  * move => D B Γ' E *. pintroL 1.
    apply (S_perm (A :: D :: B :: Γ')); auto. solve_Permutation.
  * move => D B Γ' E *. pintroL 1; by permuti 1.
  * move => D B Γ' E *. pimpL 1; auto. by permuti 1.
  * move => Δ Δ' D *. apply (S_perm (A :: Δ)); auto.
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