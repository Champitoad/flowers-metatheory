Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Terms Flowers.Utils.

(** * Flowers *)

Inductive flower :=
| Atom (p : name) (args : list term)
| Flower (Γ : garden) (Π : list garden)
with garden :=
| Garden (n : nat) (Fs : list flower).

Definition fg : flower -> garden := fun f => Garden 0 [f].
Coercion fg : flower >-> garden.

(* Definition gl : garden -> list flower := fun '(Garden _ Fs) => Fs.
Coercion gl : garden >-> list. *)

Notation "∅" := (Garden 0 nil).
Notation "n ⋅ Fs" := (Garden n Fs) (format "n  ⋅  Fs", at level 63).

Notation "Γ ⊢ Π" := (Flower Γ Π) (at level 65).
Notation "Γ ⊢" := (Flower Γ nil) (at level 65).
Notation "⊢ Π" := (Flower ∅ Π) (at level 65).

(** ** Induction principles *)

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pt : term -> Prop),
  let PΓ '(n ⋅ Fs) := Forall P Fs in
  ∀ (IHt : ∀ (t : term), Pt t)
    (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
    (IHflower : ∀ (Γ : garden) (Π : list garden),
      PΓ Γ -> Forall PΓ Π -> P (Γ ⊢ Π))
    (IHgarden : ∀ (n : nat) (Fs : list flower),
      Forall P Fs -> PΓ (n ⋅ Fs)),
  ∀ (F : flower), P F.
Proof.
  intros. move: F. fix IH 1. induction F.
  * apply IHatom. apply In_Forall. intros. by apply IHt.
  * apply IHflower.
    - case: Γ => n Fs.
      apply IHgarden.
      elim: Fs => [|F Fs IHFs] //.
      decompose_Forall; auto.
    - elim: Π => [|Δ Π IHΠ] //.
      decompose_Forall; auto.
      case Δ => n Fs. apply IHgarden; auto.
      decompose_Forall; auto.
Qed.

Definition garden_induction_full :
  ∀ (P : garden -> Prop)
    (Pt : term -> Prop)
  (IHt : ∀ (t : term), Pt t)
  (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
  (IHflower : ∀ (Γ : garden) (Π : list garden),
    P Γ -> Forall P Π -> P (Γ ⊢ Π))
  (IHnil : ∀ n, P (n ⋅ []))
  (IHcons : ∀ (F : flower) (n : nat) (Fs : list flower),
    P F -> P (n ⋅ Fs) -> P (n ⋅ F :: Fs)),
  ∀ (Γ : garden), P Γ.
Proof.
  intros. move: Γ. fix IH 1. induction Γ.
  elim: Fs => [|F Fs IHFs].
  by apply: IHnil.
  apply: IHcons.
  - elim: F => [p args |Γ Π].
    + apply IHatom. apply In_Forall. intros. by apply IHt.
    + apply IHflower.
        exact: IH.
        decompose_Forall.
  - exact: IHFs.
Qed.

Definition flower_induction	:
  ∀ (P : flower -> Prop),
  let PΓ '(n ⋅ Fs) := Forall P Fs in
  ∀ (IHatom : ∀ p args, P (Atom p args))
    (IHflower : ∀ (Γ : garden) (Π : list garden),
      PΓ Γ -> Forall PΓ Π -> P (Γ ⊢ Π)),
  ∀ (F : flower), P F.
Proof.
  intros. eapply flower_induction_full; eauto.
  exact (fun _ => I).
Qed.

Definition garden_induction	:
  ∀ (P : garden -> Prop)
  (IHatom : ∀ p args, P (Atom p args))
  (IHflower : ∀ (Γ : garden) (Π : list garden),
    P Γ -> Forall P Π -> P (Γ ⊢ Π))
  (IHnil : ∀ n, P (n ⋅ []))
  (IHcons : ∀ (F : flower) (n : nat) (Fs : list flower),
    P F -> P (n ⋅ Fs) -> P (n ⋅ F :: Fs)),
  ∀ (Γ : garden), P Γ.
Proof.
  intros; eapply garden_induction_full; eauto.
  exact (fun _ => I).
Qed.

(** ** Operations on De Bruijn indices *)

Fixpoint fshift (n : nat) (c : nat) (F : flower) : flower :=
  match F with
  | Atom p args => Atom p (tshift n c <$> args)
  | m ⋅ Fs ⊢ Π => m ⋅ fshift n (c + m) <$> Fs ⊢ gshift n (c + m) <$> Π
  end
with gshift (n : nat) (c : nat) (Γ : garden) : garden :=
  match Γ with
  | m ⋅ Fs => m ⋅ fshift n (c + m) <$> Fs
  end.

Fixpoint funshift (n : nat) (c : nat) (F : flower) : flower :=
  match F with
  | Atom p args => Atom p (tunshift n c <$> args)
  | m ⋅ Fs ⊢ Π => m ⋅ funshift n (c + m) <$> Fs ⊢ gunshift n (c + m) <$> Π
  end
with gunshift (n : nat) (c : nat) (Γ : garden) : garden :=
  match Γ with
  | m ⋅ Fs => m ⋅ funshift n (c + m) <$> Fs
  end.

Lemma fshift_zero c : ∀ F,
  fshift 0 c F = F.
Admitted.

Fixpoint fsubst (n : nat) (t : term) (F : flower) : flower :=
  match F with
  | Atom p args => Atom p (tsubst n t <$> args)
  | m ⋅ Fs ⊢ Π => m ⋅ fsubst (n+m) (tshift m 0 t) <$> Fs ⊢ gsubst (n+m) (tshift m 0 t) <$> Π
  end
with gsubst (n : nat) (t : term) (Γ : garden) : garden :=
  match Γ with
  | m ⋅ Fs => m ⋅ fsubst (n+m) (tshift m 0 t) <$> Fs
  end.

(** ** Juxtaposition of gardens *)

Definition juxt '(n ⋅ Fs) '(m ⋅ Gs) :=
  (n + m) ⋅ (fshift m 0 <$> Fs) ++ (fshift n m <$> Gs).

Definition Juxt : list garden -> garden :=
  foldr juxt ∅.

Infix "∪" := juxt.
Notation "⋃ Π" := (Juxt Π).

Lemma juxt_empty Γ :
  ∅ ∪ Γ = Γ.
Proof.
  case Γ => n Fs //=.
  pose proof (eq_map (fshift 0 n) id Fs (fshift_zero n)).
  by rewrite H list_fmap_id.
Qed.

(** * Contexts *)

Inductive fgctx :=
| Pistil (γs : ggctx) (Π : list garden)
| Petal (Γ : garden) (Π : list garden) (γs : ggctx) (Π' : list garden)
with gfctx :=
| Planter (n : nat) (Fs : list flower) (ϕs : ffctx) (Gs : list flower)
with ffctx :=
| FHole
| FComp (ϕ : fgctx) (γ : gfctx) (ϕs : ffctx)
with ggctx :=
| GHole
| GComp (γ : gfctx) (ϕ : fgctx) (γs : ggctx).

(** ** Induction principles *)

Section Induction.

Scheme fg_ctx_ind := Induction for fgctx Sort Prop
  with gf_ctx_ind := Induction for gfctx Sort Prop
  with ff_ctx_ind := Induction for ffctx Sort Prop
  with gg_ctx_ind := Induction for ggctx Sort Prop.

Section FG.

Context (P : fgctx -> Prop).

Fixpoint FG_Pgf γ :=
  match γ with
  | Planter _ _ ϕs _ => FG_Pff ϕs
  end
with FG_Pff ϕs :=
  match ϕs with
  | FHole => True
  | FComp ϕ γ ϕs => P ϕ /\ FG_Pgf γ /\ FG_Pff ϕs
  end.

Fixpoint FG_Pgg γs :=
  match γs with
  | GHole => True
  | GComp γ ϕ γs => FG_Pgf γ /\ P ϕ /\ FG_Pgg γs
  end.

Context
  (IHpistil : ∀ γs, FG_Pgg γs -> ∀ Π, P (Pistil γs Π))
  (IHpetal : ∀ γs, FG_Pgg γs -> ∀ Γ Π Π', P (Petal Γ Π γs Π'))
  (IHplanter : ∀ ϕs, FG_Pff ϕs -> ∀ n Fs Gs, FG_Pgf (Planter n Fs ϕs Gs)).

Definition fgctx_induction : ∀ ϕ, P ϕ.
Proof.
  eapply fg_ctx_ind; eauto.
  intros. apply IHplanter. eauto.
  all: easy.
Qed.

End FG.

Section GF.

Context (P : gfctx -> Prop).

Fixpoint GF_Pfg ϕ :=
  match ϕ with
  | Pistil γs _
  | Petal _ _ γs _ => GF_Pgg γs
  end
with GF_Pgg γs :=
  match γs with
  | GHole => True
  | GComp γ ϕ γs => P γ /\ GF_Pfg ϕ /\ GF_Pgg γs
  end.

Fixpoint GF_Pff (ϕs : ffctx) :=
  match ϕs with
  | FHole => True
  | FComp ϕ γ ϕs => GF_Pfg ϕ /\ P γ /\ GF_Pff ϕs
  end.

Context
  (IHpistil : ∀ γs, GF_Pgg γs -> ∀ Π, GF_Pfg (Pistil γs Π))
  (IHplanter : ∀ ϕs, GF_Pff ϕs -> ∀ n Fs Gs, P (Planter n Fs ϕs Gs)).

Definition gfctx_induction : ∀ γ, P γ.
Proof.
  eapply gf_ctx_ind; eauto; easy.
Qed.

End GF.

Section FF.

Context (P : ffctx -> Prop).

Definition FF_Pgf γ :=
  match γ with
  | Planter _ _ ϕs _ => P ϕs
  end.

Fixpoint FF_Pfg ϕ :=
  match ϕ with
  | Pistil γs _
  | Petal _ _ γs _ => FF_Pgg γs
  end
with FF_Pgg γs :=
  match γs with
  | GHole => True
  | GComp γ ϕ γs => FF_Pgf γ /\ FF_Pfg ϕ /\ FF_Pgg γs
  end.

Context
  (IHnil : P FHole)
  (IHcons : ∀ ϕ γ ϕs, FF_Pfg ϕ -> FF_Pgf γ -> P ϕs -> P (FComp ϕ γ ϕs))
  (IHpistil : ∀ γs, FF_Pgg γs -> ∀ Π, FF_Pfg (Pistil γs Π))
  (IHplanter : ∀ ϕs, P ϕs -> ∀ n Fs Gs, FF_Pgf (Planter n Fs ϕs Gs)).

Definition ffctx_induction : ∀ ϕs, P ϕs.
Proof.
  eapply ff_ctx_ind; eauto.
  intros. apply IHplanter. auto.
  all: easy.
Qed.

End FF.

Section GG.

Context (P : ggctx -> Prop).

Definition GG_Pfg ϕ :=
  match ϕ with
  | Pistil γs _
  | Petal _ _ γs _ => P γs
  end.

Fixpoint GG_Pgf γ :=
  match γ with
  | Planter _ _ ϕs _ => GG_Pff ϕs
  end
with GG_Pff ϕs :=
  match ϕs with
  | FHole => True
  | FComp ϕ γ ϕs => GG_Pfg ϕ /\ GG_Pgf γ /\ GG_Pff ϕs
  end.

Context
  (IHnil : P GHole)
  (IHcons : ∀ γ ϕ γs, GG_Pgf γ -> GG_Pfg ϕ -> P γs -> P (GComp γ ϕ γs))
  (IHpistil : ∀ γs, P γs -> ∀ Π, GG_Pfg (Pistil γs Π))
  (IHplanter : ∀ ϕs, GG_Pff ϕs -> ∀ n Fs Gs, GG_Pgf (Planter n Fs ϕs Gs)).

Definition ggctx_induction : ∀ γs, P γs.
Proof.
  eapply gg_ctx_ind; eauto.
  intros. apply IHplanter. eauto.
  all: easy.
Qed.

End GG.

End Induction.

(** ** Filling operations *)

Fixpoint fgfill (ϕ : fgctx) (Δ : garden) : flower :=
  match ϕ with
  | Pistil γs Π => ggfill γs Δ ⊢ Π
  | Petal Γ Π γs Π' => Γ ⊢ Π ++ [ggfill γs Δ] ++ Π'
  end
with gffill (γ : gfctx) (Hs : list flower) : garden :=
  match γ with
  | Planter n Fs ϕs Gs => n ⋅ Fs ++ fffill ϕs Hs ++ Gs
  end
with fffill (ϕs : ffctx) (Hs : list flower) : list flower :=
  match ϕs with
  | FHole => Hs
  | FComp ϕ γ ϕs => [fgfill ϕ (gffill γ (fffill ϕs Hs))]
  end
with ggfill (γs : ggctx) (Δ : garden) : garden :=
  match γs with
  | GHole => Δ
  | GComp γ ϕ γs => gffill γ [fgfill ϕ (ggfill γs Δ)]
  end.

(** ** Path operations *)

(** A path is simply a list of integers *)

Definition path := list nat.

(** Path operations may fail if the specified path has no denotation in the
    corresponding tree. Thus they live in the Option monad.

    In the setting of a pointing-based proving GUI, this becomes useless because
    the user can only select meaningful paths. *)

(** *** Compute the context and subobject associated to a path *)

Fixpoint fgpath (p : path) (F : flower) : option (fgctx * garden) :=
  match p with
  | [] => None
  | i :: p => match F with
      | Γ ⊢ Π => match i with
          | 0 =>
              γsΣ ← ggpath p Γ;
              let '(γs, Σ) := γsΣ in
              Some (Pistil γs Π, Σ)
          | _ =>
              lr ← split_at (i - 1) Π;
              let '(Π, Π') := lr in
              match Π' with
              | Δ :: Π' =>
                  γsΣ ← ggpath p Δ;
                  let '(γs, Σ) := γsΣ in
                  Some (Petal Γ Π γs Π', Σ)
              | _ => None
              end
          end
      | _ => None
      end
  end
with ggpath (p : path) (Γ : garden) : option (ggctx * garden) :=
  match p with
  | [] => Some (GHole, Γ)
  | i :: p => match Γ with
      | n ⋅ Fs =>
          lr ← split_at i Fs;
          let '(Fs, Gs) := lr in
          match Gs with
          | G :: Gs =>
              ϕΣ ← fgpath p G;
              let '(ϕ, Σ) := ϕΣ in
              Some (GComp (Planter n Fs FHole Gs) ϕ GHole, Σ)
          | _ => None
          end
      end
  end.

Fixpoint gfpath (p : path) (Γ : garden) : option (gfctx * flower) :=
  match p with
  | [] => None
  | i :: p => match Γ with
      | n ⋅ Fs =>
          lr ← split_at i Fs;
          let '(Fs, Gs) := lr in
          match Gs with
          | G :: Gs =>
              ϕsH ← ffpath p G;
              let '(ϕs, H) := ϕsH in
              Some (Planter n Fs ϕs Gs, H)
          | _ => None
          end
      end
  end
with ffpath (p : path) (F : flower) : option (ffctx * flower) :=
  match p with
  | [] => Some (FHole, F)
  | i :: p => match F with
      | Γ ⊢ Π => match i with
          | 0 =>
              γH ← gfpath p Γ;
              let '(γ, H) := γH in
              Some (FComp (Pistil GHole Π) γ FHole, H)
          | _ =>
              lr ← split_at (i - 1) Π;
              let '(Π, Π') := lr in
              match Π' with
              | Δ :: Π' =>
                  γH ← gfpath p Δ;
                  let '(γ, H) := γH in
                  Some (FComp (Petal Γ Π GHole Π') γ FHole, H)
              | _ => None
              end
          end
      | _ => None
      end
  end.

(** *** Retrieve subobjects *)

Definition fgget (p : path) (F : flower) : option garden :=
  X ← fgpath p F;
  let '(_, Σ) := X in
  Some Σ.

Definition gfget (p : path) (Γ : garden) : option flower :=
  X ← gfpath p Γ;
  let '(_, H) := X in
  Some H.

Definition ffget (p : path) (F : flower) : option flower :=
  X ← ffpath p F;
  let '(_, H) := X in
  Some H.

Definition ggget (p : path) (Γ : garden) : option garden :=
  X ← ggpath p Γ;
  let '(_, Σ) := X in
  Some Σ.

(** *** Modify subobjects *)

Definition fgset (Δ : garden) (p : path) (F : flower) : option flower :=
  X ← fgpath p F;
  let '(ϕ, _) := X in
  Some (fgfill ϕ Δ).

Definition gfset (Gs : list flower) (p : path) (Γ : garden) : option garden :=
  X ← gfpath p Γ;
  let '(γ, _) := X in
  Some (gffill γ Gs).

Definition ffset (Gs : list flower) (p : path) (F : flower) : option (list flower) :=
  X ← ffpath p F;
  let '(ϕs, _) := X in
  Some (fffill ϕs Gs).

Definition ggset (Δ : garden) (p : path) (Γ : garden) : option garden :=
  X ← ggpath p Γ;
  let '(γs, _) := X in
  Some (ggfill γs Δ).

Open Scope string_scope.
Compute λ F : flower, gfset [] [0; 1; 0] (0 ⋅ [(∅ ⊢ [0 ⋅ [F]]); Atom "c" []]).
Close Scope string_scope.

(** ** De Bruijn operations *)

(** *** Compute the number of variables bound in a given context *)

Fixpoint fgbv (ϕ : fgctx) : nat :=
  match ϕ with
  | Pistil γs _ => ggbv γs
  | Petal (n ⋅ _) _ γs _ => n + ggbv γs
  end
with gfbv (γ : gfctx) : nat :=
  match γ with
  | Planter n _ ϕs _ => n + ffbv ϕs
  end
with ffbv (ϕs : ffctx) : nat :=
  match ϕs with
  | FHole => 0
  | FComp ϕ γ ϕs => fgbv ϕ + gfbv γ + ffbv ϕs
  end
with ggbv (γs : ggctx) : nat :=
  match γs with
  | GHole => 0
  | GComp γ ϕ γs => gfbv γ + fgbv ϕ + ggbv γs
  end.

(** * Rules *)

(** ** Flower rules *)

Reserved Infix "-f->" (at level 80).

Inductive fstep : list flower -> list flower -> Prop :=

(** *** Pollination *)

| R_wpol_l F ϕs Fs :
  [F] ++ Fs ++ fffill ϕs [fshift (ffbv ϕs) 0 F] -f->
  [F] ++ Fs ++ fffill ϕs []

| R_co_wpol_l F ϕs Fs :
  [F] ++ Fs ++ fffill ϕs [] -f->
  [F] ++ Fs ++ fffill ϕs [fshift (ffbv ϕs) 0 F]

| R_wpol_r F ϕs Fs :
  fffill ϕs [fshift (ffbv ϕs) 0 F] ++ Fs ++ [F] -f->
  fffill ϕs [] ++ Fs ++ [F]

| R_co_wpol_r F ϕs Fs :
  fffill ϕs [] ++ Fs ++ [F] -f->
  fffill ϕs [fshift (ffbv ϕs) 0 F] ++ Fs ++ [F]

| R_spol F γ n Fs Fs' Π Π' :
  [n ⋅ Fs ++ [F] ++ Fs' ⊢ Π ++ [gffill γ [fshift (gfbv γ) 0 F]] ++ Π'] -f->
  [n ⋅ Fs ++ [F] ++ Fs' ⊢ Π ++ [gffill γ []] ++ Π']

| R_co_spol F γ n Fs Fs' Π Π' :
  [n ⋅ Fs ++ [F] ++ Fs' ⊢ Π ++ [gffill γ []] ++ Π'] -f->
  [n ⋅ Fs ++ [F] ++ Fs' ⊢ Π ++ [gffill γ [fshift (gfbv γ) 0 F]] ++ Π']

(** *** Reproduction *)

| R_rep Δs n Fs Fs' Π :
  [n ⋅ Fs ++ [⊢ Δs] ++ Fs' ⊢ Π] -f->
  [n ⋅ Fs ++ Fs' ⊢ [0 ⋅ (λ Δ, Δ ⊢ Π) <$> Δs]]

(** *** Empty petal *)

| R_pet	n Γ Π Π' :
  [Γ ⊢ Π ++ [n ⋅ []] ++ Π'] -f->
  []

(** *** Instantiation *)

| R_ipis i t n Fs Π :
  [n ⋅ Fs ⊢ Π] -f->
  [n-1 ⋅ funshift 1 i <$> (fsubst i (tshift n 0 t) <$> Fs) ⊢ gunshift 1 i <$> (gsubst i (tshift n 0 t) <$> Π); n ⋅ Fs ⊢ Π]

| R_ipet i t n Fs Γ Π Π' :
  [Γ ⊢ Π ++ [n ⋅ Fs] ++ Π] -f->
  [Γ ⊢ Π ++ [n-1 ⋅ funshift 1 i <$> (fsubst i (tshift n 0 t) <$> Fs); n ⋅ Fs] ++ Π']

where "Γ -f-> Δ" := (fstep Γ Δ).

(** ** Garden rules *)

Reserved Infix "-g->" (at level 80).

Inductive gstep : garden -> garden -> Prop :=

(** *** Empty pistil *)

| R_epis m Gs n Fs Fs' :
  n ⋅ Fs ++ [⊢ [m ⋅ Gs]] ++ Fs' -g->
  n + m ⋅ (fshift m 0 <$> Fs) ++ Gs ++ (fshift m 0 <$> Fs')

| R_co_epis m Gs n Fs Fs' :
  n + m ⋅ (fshift m 0 <$> Fs) ++ Gs ++ (fshift m 0 <$> Fs') -g->
  n ⋅ Fs ++ [⊢ [m ⋅ Gs]] ++ Fs'

where "Γ -g-> Δ" := (gstep Γ Δ).

(** ** Contextual closure *)

Reserved Infix "~>" (at level 80).

Inductive cstep : garden -> garden -> Prop :=

| R_gfctx (γ : gfctx) (Fs Gs : list flower) :
  Fs -f-> Gs ->
  gffill γ Fs ~> gffill γ Gs

| R_ggctx (γs : ggctx) (Γ Δ : garden) :
  Γ -g-> Δ ->
  ggfill γs Γ ~> ggfill γs Δ

where "Γ ~> Δ" := (cstep Γ Δ).

(** ** Transitive closure *)

Infix "~>*" := (rtc cstep) (at level 80).

Notation "Γ <~> Δ" := (Γ ~>* Δ /\ Δ ~>* Γ) (at level 80).

Lemma rtc_cstep_ctx γs Γ Δ :
  Γ ~>* Δ ->
  ggfill γs Γ ~>* ggfill γs Δ.
Proof.
  elim; clear Γ Δ.
  * move => Γ. reflexivity.
  * move => Γ Δ Σ.
    elim => [γ Fs Gs H _ IH |γs' Γ' Δ' _ H IH].
    - induction γs as [|γ' ϕ γs].
      + apply (R_gfctx γ) in H.
        eapply rtc_l; eauto.
      + admit.
    - admit.
Admitted.

(** * Basic proof search *)

Ltac sub_at p :=
  match goal with
  | |- ?Γ ~>* _ => eval cbn in (ggget p Γ)
  end.

Ltac rstep Δ :=
  apply (rtc_l cstep _ Δ).

Ltac rstepm p Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let Γ' := eval cbn in (ggset p Δ Γ) in
      rstep Γ'; list_simplifier
  end.

Ltac rstepm_cons p i Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let γΣ := eval cbn in (ggpath p Γ) in
      match γΣ with
      | Some (?γ, ?n ⋅ ?Σ1 :: ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ Δ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 :: Δ)
          end
      end
  end.

Ltac rstepm_app p i Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let γΣ := eval cbn in (ggpath p Γ) in
      match γΣ with
      | Some (?γ, ?n ⋅ ?Σ1 ++ ?Σ2) =>
          match i with
          | 0 => rstepm p (n ⋅ Δ ++ Σ2)
          | 1 => rstepm p (n ⋅ Σ1 ++ Δ)
          end
      end
  end.

Ltac rtransm p Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let Γ' := eval cbn in (ggset p Δ Γ) in
      transitivity Γ'; list_simplifier
  end.

Lemma fill_hole Γ :
  ggfill GHole Γ = Γ.
Proof.
  reflexivity.
Qed.

Ltac rctx γ Γ Δ :=
  let H := fresh "H" in
  pose proof (H := R_ggctx γ Γ Δ);
  repeat rewrite fill_hole/= in H; list_simplifier;
  apply H; clear H.

Ltac rctxm p :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      let spΓ := eval cbn in (ggpath p Γ) in
      let spΔ := eval cbn in (ggpath p Δ) in
      match spΓ with
      | Some (?γ, ?Γ0) =>
          match spΔ with
          | Some (_, ?Δ0) =>
              rctx γ Γ0 Δ0
          end
      end
  end.

Ltac rcstepm p Δ :=
  match goal with
  | |- ?Γ ~>* _ =>
      let spΓ := eval cbn in (ggpath p Γ) in
      match spΓ with
      | Some (?γ, ?Γ0) =>
          rstepm p Δ; [> rctx γ Γ0 Δ | ..]
      end
  end.

Ltac rctxmt p Δ0 :=
  match goal with
  | |- ?Γ ~>* ?Δ =>
      let spΓ := eval cbn in (ggpath p Γ) in
      let spΔ := eval cbn in (ggpath p Δ) in
      match spΓ with
      | Some (?γ, ?Γ0) =>
          let H := fresh "H" in
          pose proof (H := rtc_cstep_ctx γ Γ0 Δ0);
          repeat rewrite fill_hole/= in H; list_simplifier;
          apply H; clear H
      end
  end.

Ltac rctxmH p H :=
  match type of H with
  | _ ~>* ?Δ0 =>
      rtransm p Δ0; [> rctxmt p Δ0; exact H | ..]
  end.

Ltac rself :=
  match goal with
  | |- ?Γ ~> ?Δ =>
      rctx GHole Γ Δ
  end.

Ltac rwpol γ Γ :=
  let Hins := fresh "H" in
  let Hdel := fresh "H" in
  pose proof (Hins := R_wpol_l γ Γ);
  pose proof (Hdel := R_co_wpol_l γ Γ);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rwpolm p :=
  match goal with
  | |- ?n ⋅ ?Γ ++ ?Δ -f-> _ =>
      let spΔ := eval cbn in (ggpath p (n ⋅ Δ)) in
      match spΔ with
      | Some (?γ, _) =>
          rwpol γ (n ⋅ Γ)
      end
  end.

Ltac rspol γ Γ Δ Π :=
  let Hins := fresh "Hins" in
  let Hdel := fresh "Hdel" in
  pose proof (Hins := R_spol γ Γ Δ Π);
  pose proof (Hdel := R_co_spol γ Γ Δ Π);
  repeat rewrite fill_hole/= in Hins, Hdel; list_simplifier;
  (exact Hins || exact Hdel);
  clear Hins Hdel.

Ltac rspolm p :=
  match goal with
  | |- ?Γ -f-> _ =>
      let spΓ := eval cbn in (ggpath p Γ) in
      match spΓ with
      | Some (Planter [] (Petal ?Γ' [] ?γ ?Π') [], ?Δ) =>
          rspol γ Γ' ∅ Π'
      end
  end.

Ltac spol p :=
  match goal with
  | |- ?n ⋅ [?Γ ⊢ _] ~>* _ =>
      rstepm p Γ; [> rself; rspolm p | ..]
  end.

Ltac rrep :=
  match goal with
  | |- ?n ⋅ [?m ⋅ (∅ ⊢ ?Δs) :: ?Γ ⊢ ?Π] -f-> _ =>
      let H := fresh "H" in
      pose proof (H := R_rep (?m ⋅ Γ) Δs Π);
      repeat rewrite fill_hole/= in H; list_simplifier;
      exact H; clear H
  end.

Ltac rpis :=
  apply R_epis.

Ltac rcopis :=
  apply R_co_epis.

Ltac rpism p :=
  match sub_at p with
  | Some (fg (⊢ [?Δ])) =>
      rcstepm p Δ; [> rpis | ..]
  end.

Ltac rcopism p :=
  match sub_at p with
  | Some ?Δ => 
      rcstepm p (0 ⋅ [⊢ [Δ]]); [> rcopis | ..]
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
  intros Γ Δ Hpis Π Π' Hpet.
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