Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Terms Flowers.Utils.

(** * Flowers *)

Inductive flower :=
| Atom (p : name) (args : list term)
| Flower (γ : garden) (Δ : list garden)
with garden :=
| Garden (n : nat) (Φ : list flower).

Definition ftog : flower -> garden := fun ϕ => Garden 0 [ϕ].
Coercion ftog : flower >-> garden.

(* Definition gl : garden -> list flower := fun '(Garden _ Φ) => Φ.
Coercion gl : garden >-> list. *)

Notation "∅" := (Garden 0 nil).
Notation "n ⋅ Φ" := (Garden n Φ) (format "n  ⋅  Φ", at level 63).

Notation "γ ⊢ Δ" := (Flower γ Δ) (at level 65).
Notation "γ ⊢" := (Flower γ nil) (at level 65).
Notation "⊢ Δ" := (Flower ∅ Δ) (at level 65).

(** ** Induction principles *)

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pt : term -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHt : ∀ (t : term), Pt t)
    (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⊢ Δ))
    (IHgarden : ∀ (n : nat) (Φ : list flower),
      Forall P Φ -> Pγ (n ⋅ Φ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. move: ϕ. fix IH 1. induction ϕ.
  * apply IHatom. apply In_Forall. intros. by apply IHt.
  * apply IHflower.
    - case: γ => n Φ.
      apply IHgarden.
      elim: Φ => [|ϕ Φ IHΦ] //.
      decompose_Forall; auto.
    - elim: Δ => [|δ Δ IHΔ] //.
      decompose_Forall; auto.
      case δ => n Φ. apply IHgarden; auto.
      decompose_Forall; auto.
Qed.

Definition garden_induction_full :
  ∀ (P : garden -> Prop)
    (Pt : term -> Prop)
  (IHt : ∀ (t : term), Pt t)
  (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
  (IHflower : ∀ (γ : garden) (Δ : list garden),
    P γ -> Forall P Δ -> P (γ ⊢ Δ))
  (IHnil : ∀ n, P (n ⋅ []))
  (IHcons : ∀ (ϕ : flower) (n : nat) (Φ : list flower),
    P ϕ -> P (n ⋅ Φ) -> P (n ⋅ ϕ :: Φ)),
  ∀ (γ : garden), P γ.
Proof.
  intros. move: γ. fix IH 1. induction γ.
  elim: Φ => [|ϕ Φ IHΦ].
  by apply: IHnil.
  apply: IHcons.
  - elim: ϕ => [p args |γ Δ].
    + apply IHatom. apply In_Forall. intros. by apply IHt.
    + apply IHflower.
        exact: IH.
        decompose_Forall.
  - exact: IHΦ.
Qed.

Definition flower_induction	:
  ∀ (P : flower -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHatom : ∀ p args, P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⊢ Δ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. eapply flower_induction_full; eauto.
  exact (fun _ => I).
Qed.

Definition garden_induction	:
  ∀ (P : garden -> Prop)
  (IHatom : ∀ p args, P (Atom p args))
  (IHflower : ∀ (γ : garden) (Δ : list garden),
    P γ -> Forall P Δ -> P (γ ⊢ Δ))
  (IHnil : ∀ n, P (n ⋅ []))
  (IHcons : ∀ (ϕ : flower) (n : nat) (Φ : list flower),
    P ϕ -> P (n ⋅ Φ) -> P (n ⋅ ϕ :: Φ)),
  ∀ (γ : garden), P γ.
Proof.
  intros; eapply garden_induction_full; eauto.
  exact (fun _ => I).
Qed.

(** ** Operations on De Bruijn indices *)

Fixpoint fshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tshift n c <$> args)
  | m ⋅ Φ ⊢ Δ => m ⋅ fshift n (c + m) <$> Φ ⊢ gshift n (c + m) <$> Δ
  end
with gshift (n : nat) (c : nat) (γ : garden) : garden :=
  match γ with
  | m ⋅ Φ => m ⋅ fshift n (c + m) <$> Φ
  end.

Fixpoint funshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tunshift n c <$> args)
  | m ⋅ Φ ⊢ Δ => m ⋅ funshift n (c + m) <$> Φ ⊢ gunshift n (c + m) <$> Δ
  end
with gunshift (n : nat) (c : nat) (γ : garden) : garden :=
  match γ with
  | m ⋅ Φ => m ⋅ funshift n (c + m) <$> Φ
  end.

Lemma fshift_zero c : ∀ ϕ,
  fshift 0 c ϕ = ϕ.
Admitted.

Fixpoint fsubst (n : nat) (t : term) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tsubst n t <$> args)
  | m ⋅ Φ ⊢ Δ => m ⋅ fsubst (n+m) (tshift m 0 t) <$> Φ ⊢ gsubst (n+m) (tshift m 0 t) <$> Δ
  end
with gsubst (n : nat) (t : term) (γ : garden) : garden :=
  match γ with
  | m ⋅ Φ => m ⋅ fsubst (n+m) (tshift m 0 t) <$> Φ
  end.

(** ** Juxtaposition of gardens *)

Definition juxt '(n ⋅ Φ) '(m ⋅ Ψ) :=
  (n + m) ⋅ (fshift m 0 <$> Φ) ++ (fshift n m <$> Ψ).

Definition Juxt : list garden -> garden :=
  foldr juxt ∅.

Infix "∪" := juxt.
Notation "⋃ Δ" := (Juxt Δ).

Lemma juxt_empty γ :
  ∅ ∪ γ = γ.
Proof.
  case γ => n Φ //=.
  pose proof (eq_map (fshift 0 n) id Φ (fshift_zero n)).
  by rewrite H list_fmap_id.
Qed.

(** * Contexts *)

Inductive ggctx :=
| GHole
| GPlanter (n : nat) (Φ : list flower) (gf : gfctx) (Φ' : list flower)
with gfctx :=
| GPistil (gg : ggctx) (Δ : list garden)
| GPetal (γ : garden) (Δ : list garden) (gg : ggctx) (Δ' : list garden).

Inductive fgctx :=
| FPlanter (n : nat) (Φ : list flower) (ff : ffctx) (Φ' : list flower)
with ffctx :=
| FHole
| FPistil (fg : fgctx) (Δ : list garden)
| FPetal (γ : garden) (Δ : list garden) (fg : fgctx) (Δ' : list garden).

(** ** Induction principles *)

Section Induction.

Scheme gg_ctx_ind := Induction for ggctx Sort Prop
  with gf_ctx_ind := Induction for gfctx Sort Prop.

Scheme fg_ctx_ind := Induction for fgctx Sort Prop
  with ff_ctx_ind := Induction for ffctx Sort Prop.

Section GG.

Context (P : ggctx -> Prop).

Definition Pgf gf :=
  match gf with
  | GPistil gg _
  | GPetal _ _ gg _ => P gg
  end.

Context
  (IHHole : P GHole)
  (IHPlanter : ∀ gf, Pgf gf -> ∀ n Φ Φ', P (GPlanter n Φ gf Φ')).

Definition gg_ind : ∀ gg, P gg.
Proof.
  eapply gg_ctx_ind; eauto.
Qed.

End GG.

Section GF.

Context (P : gfctx -> Prop).

Definition Pgg gg :=
  match gg with
  | GHole => True
  | GPlanter _ _ gf _ => P gf
  end.

Context
  (IHHole : Pgg GHole)
  (IHPistil : ∀ gg, Pgg gg -> ∀ Δ, P (GPistil gg Δ))
  (IHPetal : ∀ gg, Pgg gg -> ∀ γ Δ Δ', P (GPetal γ Δ gg Δ')).

Definition gf_ind : ∀ gf, P gf.
Proof.
  eapply gf_ctx_ind; eauto.
Qed.

End GF.

Section FG.

Context (P : fgctx -> Prop).

Definition Pff ff :=
  match ff with
  | FHole => True
  | FPistil fg _
  | FPetal _ _ fg _ => P fg
  end.

Context
  (IHHole : Pff FHole)
  (IHPlanter : ∀ ff, Pff ff -> ∀ n Φ Φ', P (FPlanter n Φ ff Φ')).

Definition fg_ind : ∀ fg, P fg.
Proof.
  eapply fg_ctx_ind; eauto.
Qed.

End FG.

Section FF.

Context (P : ffctx -> Prop).

Definition Pfg fg :=
  match fg with
  | FPlanter _ _ ff _ => P ff
  end.

Context
  (IHPlanter : ∀ ff, P ff -> ∀ n Φ Φ', Pfg (FPlanter n Φ ff Φ'))
  (IHHole : P FHole)
  (IHPistil : ∀ fg, Pfg fg -> ∀ Δ, P (FPistil fg Δ))
  (IHPetal : ∀ fg, Pfg fg -> ∀ γ Δ Δ', P (FPetal γ Δ fg Δ')).

Definition ff_ind : ∀ ff, P ff.
Proof.
  eapply ff_ctx_ind; eauto. intros. by apply IHPlanter.
Qed.

End FF.

End Induction.

(** ** Filling operations *)

Fixpoint ggfill (δ : garden) (gg : ggctx) : garden :=
  match gg with
  | GHole => δ
  | GPlanter n Φ gf Φ' => n ⋅ Φ ++ [gffill δ gf] ++ Φ'
  end
with gffill (δ : garden) (gf : gfctx) : flower :=
  match gf with
  | GPistil gg Δ => (ggfill δ gg) ⊢ Δ
  | GPetal γ Δ gg Δ' => γ ⊢ Δ ++ [ggfill δ gg] ++ Δ'
  end.

Fixpoint fgfill (Ψ : list flower) (fg : fgctx) : garden :=
  match fg with
  | FPlanter n Φ ff Φ' => n ⋅ Φ ++ (fffill Ψ ff) ++ Φ'
  end
with fffill (Ψ : list flower) (ff : ffctx) : list flower :=
  match ff with
  | FHole => Ψ
  | FPistil fg Δ => [(fgfill Ψ fg) ⊢ Δ]
  | FPetal γ Δ fg Δ' => [γ ⊢ Δ ++ [fgfill Ψ fg] ++ Δ']
  end.

(** ** Path operations *)

(** A path is simply a list of integers *)

Definition path := list nat.

(** Path operations may fail if the specified path has no denotation in the
    corresponding tree. Thus they live in the Option monad.

    In the setting of a pointing-based proving GUI, this becomes useless because
    the user can only select meaningful paths. *)

(** *** Compute the context and subobject associated to a path *)

Fixpoint ggpath (p : path) (γ : garden) : option (ggctx * garden) :=
  match p with
  | [] => Some (GHole, γ)
  | i :: p => match γ with
      | n ⋅ Φ =>
          lr ← split_at i Φ;
          let '(Φ, Ψ) := lr in
          match Ψ with
          | ψ :: Ψ =>
              gfδ ← gfpath p ψ;
              let '(gf, δ) := gfδ in
              Some (GPlanter n Φ gf Ψ, δ)
          | _ => None
          end
      end
  end
with gfpath (p : path) (ϕ : flower) : option (gfctx * garden) :=
  match p with
  | [] => None
  | i :: p => match ϕ with
      | γ ⊢ Δ => match i with
          | 0 =>
              ggδ ← ggpath p γ;
              let '(gg, δ) := ggδ in
              Some (GPistil gg Δ, δ)
          | _ =>
              lr ← split_at (i - 1) Δ;
              let '(Δ, Δ') := lr in
              match Δ' with
              | δ :: Δ' =>
                  ggσ ← ggpath p δ;
                  let '(gg, σ) := ggσ in
                  Some (GPetal γ Δ gg Δ', σ)
              | _ => None
              end
          end
      | _ => None
      end
  end.

Fixpoint fgpath (p : path) (γ : garden) : option (fgctx * flower) :=
  match p with
  | [] => None
  | i :: p => match γ with
      | n ⋅ Φ =>
          lr ← split_at i Φ;
          let '(Φ, Ψ) := lr in
          match Ψ with
          | ψ :: Ψ =>
              ffϕ ← ffpath p ψ;
              let '(ff, ϕ) := ffϕ in
              Some (FPlanter n Φ ff Ψ, ϕ)
          | _ => None
          end
      end
  end
with ffpath (p : path) (ϕ : flower) : option (ffctx * flower) :=
  match p with
  | [] => Some (FHole, ϕ)
  | i :: p => match ϕ with
      | γ ⊢ Δ => match i with
          | 0 =>
              fgψ ← fgpath p γ;
              let '(fg, ψ) := fgψ in
              Some (FPistil fg Δ, ψ)
          | _ =>
              lr ← split_at (i - 1) Δ;
              let '(Δ, Δ') := lr in
              match Δ' with
              | δ :: Δ' =>
                  fgψ ← fgpath p δ;
                  let '(fg, ψ) := fgψ in
                  Some (FPetal γ Δ fg Δ', ψ)
              | _ => None
              end
          end
      | _ => None
      end
  end.

(** *** Retrieve subobjects *)

Definition ggget (p : path) (γ : garden) : option garden :=
  X ← ggpath p γ;
  let '(_, δ) := X in
  Some δ.

Definition gfget (p : path) (ϕ : flower) : option garden :=
  X ← gfpath p ϕ;
  let '(_, δ) := X in
  Some δ.

Definition fgget (p : path) (γ : garden) : option flower :=
  X ← fgpath p γ;
  let '(_, ϕ) := X in
  Some ϕ.

Definition ffget (p : path) (ϕ : flower) : option flower :=
  X ← ffpath p ϕ;
  let '(_, ψ) := X in
  Some ψ.

(** *** Modify subobjects *)

Definition ggset (δ : garden) (p : path) (γ : garden) : option garden :=
  X ← ggpath p γ;
  let '(gg, _) := X in
  Some (ggfill δ gg).

Definition gfset (δ : garden) (p : path) (ϕ : flower) : option flower :=
  X ← gfpath p ϕ;
  let '(gf, _) := X in
  Some (gffill δ gf).

Definition fgset (Ψ : list flower) (p : path) (γ : garden) : option garden :=
  X ← fgpath p γ;
  let '(fg, _) := X in
  Some (fgfill Ψ fg).

Definition ffset (Ψ : list flower) (p : path) (ϕ : flower) : option (list flower) :=
  X ← ffpath p ϕ;
  let '(ff, _) := X in
  Some (fffill Ψ ff).

Open Scope string_scope.
Compute λ ϕ : flower, fgset [] [0; 1; 0] (0 ⋅ [(∅ ⊢ [0 ⋅ [ϕ]]); Atom "c" []]).
Close Scope string_scope.

(** ** De Bruijn operations *)

(** *** Compute the number of variables bound in a given context *)

Fixpoint ggbv (gg : ggctx) : nat :=
  match gg with
  | GHole => 0
  | GPlanter n _ gf _ => n + gfbv gf
  end
with gfbv (gf : gfctx) : nat :=
  match gf with
  | GPistil gg _ => ggbv gg
  | GPetal (n ⋅ _) _ gg _ => n + ggbv gg
  end.

Fixpoint fgbv (fg : fgctx) : nat :=
  match fg with
  | FPlanter n _ ff _ => n + ffbv ff
  end
with ffbv (ff : ffctx) : nat :=
  match ff with
  | FHole => 0
  | FPistil fg _ => fgbv fg
  | FPetal (n ⋅ _) _ fg _ => n + fgbv fg
  end.

(** * Rules *)

(** ** Assumptions available in a context *)

Fixpoint ggassums (gg : ggctx) : list flower :=
  match gg with
  | GHole => []
  | GPlanter _ Φ gf Φ' => Φ ++ Φ' ++ gfassums gf
  end
with gfassums (gf : gfctx) : list flower :=
  match gf with
  | GPistil gg _ => ggassums gg
  | GPetal (_ ⋅ Φ) _ gg _ => Φ ++ ggassums gg
  end.

Fixpoint fgassums (fg : fgctx) : list flower :=
  match fg with
  | FPlanter _ Φ ff Φ' => Φ ++ Φ' ++ ffassums ff
  end
with ffassums (ff : ffctx) : list flower :=
  match ff with
  | FHole => []
  | FPistil fg _ => fgassums fg
  | FPetal (_ ⋅ Φ) _ fg _ => Φ ++ fgassums fg
  end.

(** ** Flower rules *)

Reserved Infix "-f->" (at level 80).

Inductive fstep : list flower -> list flower -> Prop :=

(** *** Pollination *)

| R_wpol_l ϕ ff Φ :
  [ϕ] ++ Φ ++ fffill ff [fshift (ffbv ff) 0 ϕ] -f->
  [ϕ] ++ Φ ++ fffill ff []

| R_co_wpol_l ϕ ff Φ :
  [F] ++ Φ ++ fffill ff [] -f->
  [F] ++ Φ ++ fffill ff [fshift (ffbv ff) 0 F]

| R_wpol_r ϕ ff Φ :
  fffill ff [fshift (ffbv ff) 0 F] ++ Φ ++ [F] -f->
  fffill ff [] ++ Φ ++ [F]

| R_co_wpol_r ϕ ff Φ :
  fffill ff [] ++ Φ ++ [F] -f->
  fffill ff [fshift (ffbv ff) 0 F] ++ Φ ++ [F]

| R_spol ϕ γ n Φ Φ' Δ Δ' :
  [n ⋅ Φ ++ [F] ++ Φ' ⊢ Δ ++ [gffill γ [fshift (gfbv γ) 0 F]] ++ Δ'] -f->
  [n ⋅ Φ ++ [F] ++ Φ' ⊢ Δ ++ [gffill γ []] ++ Δ']

| R_co_spol ϕ γ n Φ Φ' Δ Δ' :
  [n ⋅ Φ ++ [F] ++ Φ' ⊢ Δ ++ [gffill γ []] ++ Δ'] -f->
  [n ⋅ Φ ++ [F] ++ Φ' ⊢ Δ ++ [gffill γ [fshift (gfbv γ) 0 F]] ++ Δ']

(** *** Reproduction *)

| R_rep δs n Φ Φ' Δ :
  [n ⋅ Φ ++ [⊢ δs] ++ Φ' ⊢ Δ] -f->
  [n ⋅ Φ ++ Φ' ⊢ [0 ⋅ (λ δ, δ ⊢ Δ) <$> δs]]

(** *** Empty petal *)

| R_pet	n γ Δ Δ' :
  [γ ⊢ Δ ++ [n ⋅ []] ++ Δ'] -f->
  []

(** *** Instantiation *)

| R_ipis i t n Φ Δ :
  [n ⋅ Φ ⊢ Δ] -f->
  [n-1 ⋅ funshift 1 i <$> (fsubst i (tshift n 0 t) <$> Φ) ⊢ gunshift 1 i <$> (gsubst i (tshift n 0 t) <$> Δ); n ⋅ Φ ⊢ Δ]

| R_ipet i t n Φ γ Δ Δ' :
  [γ ⊢ Δ ++ [n ⋅ Φ] ++ Δ] -f->
  [γ ⊢ Δ ++ [n-1 ⋅ funshift 1 i <$> (fsubst i (tshift n 0 t) <$> Φ); n ⋅ Φ] ++ Δ']

where "γ -f-> δ" := (fstep γ δ).

(** ** Garden rules *)

Reserved Infix "-g->" (at level 80).

Inductive gstep : garden -> garden -> Prop :=

(** *** Empty pistil *)

| R_epis m Ψ n Φ Φ' :
  n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' -g->
  n + m ⋅ (fshift m 0 <$> Φ) ++ Ψ ++ (fshift m 0 <$> Φ')

| R_co_epis m Ψ n Φ Φ' :
  n + m ⋅ (fshift m 0 <$> Φ) ++ Ψ ++ (fshift m 0 <$> Φ') -g->
  n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'

where "γ -g-> δ" := (gstep γ δ).

(** ** Contextual closure *)

Reserved Infix "~>" (at level 80).

Inductive cstep : garden -> garden -> Prop :=

| R_gfctx (γ : gfctx) (Φ Ψ : list flower) :
  Φ -f-> Ψ ->
  gffill γ Φ ~> gffill γ Ψ

| R_ggctx (γs : ggctx) (γ δ : garden) :
  γ -g-> δ ->
  ggfill γs γ ~> ggfill γs δ

where "γ ~> δ" := (cstep γ δ).

(** ** Transitive closure *)

Infix "~>*" := (rtc cstep) (at level 80).

Notation "γ <~> δ" := (γ ~>* δ /\ δ ~>* γ) (at level 80).

Lemma rtc_cstep_ctx γs γ δ :
  γ ~>* δ ->
  ggfill γs γ ~>* ggfill γs δ.
Proof.
  elim; clear γ δ.
  * move => γ. reflexivity.
  * move => γ δ Σ.
    elim => [γ Φ Ψ H _ IH |γs' γ' δ' _ H IH].
    - induction γs as [|γ' ϕ γs].
      + apply (R_gfctx γ) in H.
        eapply rtc_l; eauto.
      + admit.
    - admit.
Admitted.

(** * Basic proof search *)

Ltac sub_at p :=
  match goal with
  | |- ?γ ~>* _ => eval cbn in (ggget p γ)
  end.

Ltac rstep δ :=
  apply (rtc_l cstep _ δ).

Ltac rstepm p δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γ' := eval cbn in (ggset p δ γ) in
      rstep γ'; list_simplifier
  end.

Ltac rstepm_cons p i δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γΣ := eval cbn in (ggpath p γ) in
      match γΣ with
      | Some (?γ, ?n ⋅ ?Σ1 :: ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ δ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 :: δ)
          end
      end
  end.

Ltac rstepm_app p i δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γΣ := eval cbn in (ggpath p γ) in
      match γΣ with
      | Some (?γ, ?n ⋅ ?Σ1 ++ ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ δ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 ++ δ)
          end
      end
  end.

Ltac rtransm p δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let γ' := eval cbn in (ggset p δ γ) in
      transitivity γ'; list_simplifier
  end.

Lemma fill_hole γ :
  ggfill GHole γ = γ.
Proof.
  reflexivity.
Qed.

Ltac rctx γ γ δ :=
  let H := fresh "H" in
  pose proof (H := R_ggctx γ γ δ);
  repeat rewrite fill_hole/= in H; list_simplifier;
  apply H; clear H.

Ltac rctxm p :=
  match goal with
  | |- ?γ ~> ?δ =>
      let spγ := eval cbn in (ggpath p γ) in
      let spδ := eval cbn in (ggpath p δ) in
      match spγ with
      | Some (?γ, ?γ0) =>
          match spδ with
          | Some (_, ?δ0) =>
              rctx γ γ0 δ0
          end
      end
  end.

Ltac rcstepm p δ :=
  match goal with
  | |- ?γ ~>* _ =>
      let spγ := eval cbn in (ggpath p γ) in
      match spγ with
      | Some (?γ, ?γ0) =>
          rstepm p δ; [> rctx γ γ0 δ | ..]
      end
  end.

Ltac rctxmt p δ0 :=
  match goal with
  | |- ?γ ~>* ?δ =>
      let spγ := eval cbn in (ggpath p γ) in
      let spδ := eval cbn in (ggpath p δ) in
      match spγ with
      | Some (?γ, ?γ0) =>
          let H := fresh "H" in
          pose proof (H := rtc_cstep_ctx γ γ0 δ0);
          repeat rewrite fill_hole/= in H; list_simplifier;
          apply H; clear H
      end
  end.

Ltac rctxmH p H :=
  match type of H with
  | _ ~>* ?δ0 =>
      rtransm p δ0; [> rctxmt p δ0; exact H | ..]
  end.

Ltac rself :=
  match goal with
  | |- ?γ ~> ?δ =>
      rctx GHole γ δ
  end.

Ltac rwpol γ γ :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_wpol_l γ γ);
  pose proof (Hdel := R_co_wpol_l γ γ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rwpolm p :=
  match goal with
  | |- ?n ⋅ ?γ ++ ?δ -f-> _ =>
      let spδ := eval cbn in (ggpath p (n ⋅ δ)) in
      match spδ with
      | Some (?γ, _) =>
          rwpol γ (n ⋅ γ)
      end
  end.

Ltac rspol γ γ δ Δ :=
  let Hins := fresh "Hins" in
  let Hdel := fresh "Hdel" in
  pose proof (Hins := R_spol γ γ δ Δ);
  pose proof (Hdel := R_co_spol γ γ δ Δ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rspolm p :=
  match goal with
  | |- ?γ -f-> _ =>
      let spγ := eval cbn in (ggpath p γ) in
      match spγ with
      | Some (Planter [] (Petal ?γ' [] ?γ ?Δ') [], ?δ) =>
          rspol γ γ' ∅ Δ'
      end
  end.

Ltac spol p :=
  match goal with
  | |- ?n ⋅ [?γ ⊢ _] ~>* _ =>
      rstepm p γ; [> rself; rspolm p | ..]
  end.

Ltac rrep :=
  match goal with
  | |- ?n ⋅ [?m ⋅ (∅ ⊢ ?δs) :: ?γ ⊢ ?Δ] -f-> _ =>
      let H := fresh "H" in
      pose proof (H := R_rep (?m ⋅ γ) δs Δ);
      repeat rewrite fill_hole/= in H; list_simplifier;
      exact H; clear H
  end.

Ltac rpis :=
  apply R_epis.

Ltac rcopis :=
  apply R_co_epis.

Ltac rpism p :=
  match sub_at p with
  | Some (fg (⊢ [?δ])) =>
      rcstepm p δ; [> rpis | ..]
  end.

Ltac rcopism p :=
  match sub_at p with
  | Some ?δ => 
      rcstepm p (0 ⋅ [⊢ [δ]]); [> rcopis | ..]
  end.

Ltac rpet :=
  apply R_pet.

Ltac rpetm p :=
  rcstepm p ∅; [> rpet | ..].

(** ** Generalized rewriting *)

(* Add Parametric Relation : garden itr
  reflexivity proved by (rtc_refl cstep)
  transitivity proved by rtc_transitive
  as itr_preorder.

Add Parametric Morphism : Flower with signature
  itr ==> Forall2 itr ==> itr
  as proper_itr_Flower.
Proof.
  intros γ δ Hpis Δ Δ' Hpet.
  induction Hpis, Hpet; auto.
Admitted.

Add Parametric Morphism : Garden with signature
  Forall2 (λ F G : flower, F ~>* G) ==> itr
  as proper_itr_Garden.
Proof.
Admitted. *)

(** ** Examples *)

Open Scope string_scope.

Example deriv_contraction :
  0 ⋅ [Atom "a" []; Atom "b" []] ~>* 0 ⋅ [Atom "a" []; Atom "b" []; Atom "b" []].
Proof.
  apply rtc_once.
Admitted.