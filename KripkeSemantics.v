Require Import ssreflect stdpp.boolset stdpp.propset stdpp.vector.

Require Import Flowers.Utils Flowers.Terms Flowers.Syntax.

(** * Well-formed terms with respect to a signature *)

Record sig : Type := {
  funs : boolset name;
  preds : boolset name;
  farity : ∀ f, f ∈ funs -> nat;
  parity : ∀ p, p ∈ preds -> nat;
}.

Context (Σ : sig).

(* Fixpoint twf (t : term) : bool :=
  match t with
  | TVar _ => true
  | TFun f args =>
      match decide (f ∈ Σ.(funs)) with
      | left w => (length args =? Σ.(farity) f w) && forallb (twf <$> args)
      | right _ => false
      end
  end. *)

Inductive twf : term -> Type :=
| twf_var n :
    twf (TVar n)
| twf_fun f args :
    ∀ (Hf : f ∈ Σ.(funs)), ltwf args -> length args = Σ.(farity) f Hf ->
    twf (TFun f args)
with ltwf : list term -> Type :=
| ltwf_nil :
    ltwf []
| ltwf_cons t l :
    twf t -> ltwf l ->
    ltwf (t :: l).

Definition wfterm :=
  { t : term & twf t }.

(* Fixpoint wf (ϕ : flower) :=
  match ϕ with
  | Atom p args =>
      match decide (p ∈ Σ.(preds)) with
      | left w => (length args =? Σ.(parity) p w) && forallb (twf <$> args)
      | right _ => false
      end
  | γ ⫐ Δ =>
      let gwf '(n ⋅ Φ) := forallb (wf <$> Φ) in
      gwf γ && forallb (gwf <$> Δ)
  end. *)

Inductive fwf : flower -> Type :=
| fwf_atom p args :
    ∀ (Hp : p ∈ Σ.(preds)), ltwf args -> length args = Σ.(parity) p Hp ->
    fwf (Atom p args)
| fwf_flower n Φ Δ :
    wf Φ -> pwf Δ ->
    fwf (n ⋅ Φ ⫐ Δ)
with wf : bouquet -> Type :=
| wf_nil : wf []
| wf_cons ϕ Φ : fwf ϕ -> wf Φ -> wf (ϕ :: Φ)
with pwf : list garden -> Type :=
| pwf_nil : pwf []
| pwf_cons n Φ Δ : wf Φ -> pwf Δ -> pwf ((n ⋅ Φ) :: Δ).

Definition wfflower :=
  { ϕ : flower & fwf ϕ }.

Definition wfbouquet :=
  { Φ : bouquet & wf Φ }.

Definition wfctx :=
  { X : ctx & wf X }.

Definition wfpctx :=
  { P : pctx & wf P }. 

Definition ffgt : wfflower -> flower := projT1.
Definition bfgt : wfbouquet -> bouquet := projT1.
Definition cfgt : wfctx -> ctx := projT1.
Definition pfgt : wfpctx -> pctx := projT1.
Coercion ffgt : wfflower >-> flower.
Coercion bfgt : wfbouquet >-> bouquet.
Coercion cfgt : wfctx >-> ctx.
(* Coercion pfgt : wfpctx >-> pctx. *)

Definition wfpctx_to_wfctx : wfpctx -> wfctx := λ '(P ⇂ H), (pctx_to_ctx P) ⇂ H.
Coercion wfpctx_to_wfctx : wfpctx >-> wfctx.

Lemma wf_app (Φ Ψ : bouquet) :
  wf Φ -> wf Ψ -> wf (Φ ++ Ψ).
Proof.
  elim => {Φ} [|ϕ Φ Hϕ HΦ IH] H //=.
  econs.
Qed.

Lemma pwf_app (Γ Δ : list garden) :
  pwf Γ -> pwf Δ -> pwf (Γ ++ Δ).
Proof.
  elim => {Γ} [|γ Γ Hγ HΓ IH] H //=.
  econs.
Qed.

Lemma wf_app_inv : ∀ (Φ Ψ : bouquet),
  wf (Φ ++ Ψ) -> wf Φ * wf Ψ.
Proof.
  elim => [|ϕ Φ IH] /= Ψ H; split.
  econs. done.
  econs. inv H.
  inv H. by apply (IH Ψ).
  inv H. by apply (IH Ψ).
Qed.

Lemma pwf_app_inv : ∀ (Γ Δ : list garden),
  pwf (Γ ++ Δ) -> pwf Γ * pwf Δ.
Proof.
  elim => [|γ Γ IH] /= Δ H; split.
  econs. done. destruct γ as [n Φ].
  econs. inv H.
  inv H. by apply (IH Δ).
  inv H. by apply (IH Δ).
Qed.

Lemma wf_Planter_inv {X : ctx} {Φl Φr} :
  wf (Planter Φl X Φr) -> wf Φl * wf X * wf Φr.
Proof.
  cbn. move => H.
  case (wf_app_inv _ _ H) => {H} [Hl H];
  case (wf_app_inv _ _ H) => {H} [HX Hr].
  done.
Qed.

Lemma wf_Pistil_inv {X : ctx} {n Δ} :
  wf (Pistil n X Δ) -> wf X * pwf Δ.
Proof.
  cbn. move => H. inv H. inv X0. done.
Qed.

Lemma wf_Petal_inv {X : ctx} {n Φ Δ m Δ'} :
  wf (Petal (n ⋅ Φ) Δ m X Δ') -> wf Φ * pwf Δ * wf X * pwf Δ'.
Proof.
  cbn. move => H. inv H. inv X0.
  case (pwf_app_inv _ _ X3) => HΔ H. rewrite cons_app in H.
  case (pwf_app_inv _ _ H) => HX HΔ'. inv HX.
  done.
Qed.

Lemma wf_fill : ∀ (X : wfctx) (Φ : wfbouquet),
  wf (X ⋖ Φ).
Proof.
  move => []/=.
  elim => [|Φl X IH Φr |n X IH Δ |γ Δ n X IH Δ'] H [Φ HΦ] //=.

  case (wf_Planter_inv H); move => [Hl HX] Hr.
  repeat apply wf_app. done. by apply (IH HX (Φ ⇂ HΦ)). done.

  case (wf_Pistil_inv H); move => HX HΔ.
  econs; econs. apply (IH HX (Φ ⇂ HΦ)).

  destruct γ as [m Ψ].
  case (wf_Petal_inv H); move => [[HΨ HΔ] HX] HΔ'.
  econs; econs. rewrite cons_app. repeat apply pwf_app.
  done. econs. apply (IH HX (Φ ⇂ HΦ)). econs. done.
Qed.

(** ** Theories are sets of well-formed flowers *)

Definition theory := propset wfflower.

Definition ftot (ϕ : wfflower) : theory :=
  {[ ϕ ]}.

Definition btot (Φ : wfbouquet) : theory :=
  {[ ϕ | ffgt ϕ ∈ bfgt Φ ]}.

#[global] Coercion ftot : wfflower >-> theory.
#[global] Coercion btot : wfbouquet >-> theory.

(** * Pre-models are just domains with interpretation functions for well-formed
      terms *)

Definition elem {A C} `{Set_ A C} (X : C) :=
  { x | x ∈ X }.

Class premodel (D : Type) := {
  domain : propset D;
  interp_fun : ∀ (f : name) (H : f ∈ Σ.(funs)),
    vec (elem domain) (Σ.(farity) f H) -> elem domain;
  interp_pred : ∀ (p : name) (H : p ∈ Σ.(preds)),
    propset (vec (elem domain) (Σ.(parity) p H));
}.

Definition elem_subseteq {A : Type} (X Y : propset A) :
  X ⊆ Y -> elem X -> elem Y.
Proof.
  move => H [x Hx]. exists x. exact (H x Hx).
Defined.

Definition elem_subseteq_vec {A : Type} (X Y : propset A) :
  X ⊆ Y -> ∀ n, vec (elem X) n -> vec (elem Y) n.
Proof.
  move => H. elim => [|n IH] xs.
  * exact [#].
  * inversion xs using (@vec_S_inv (elem X)).
    move => {xs} [x Hx] xs.
    constructor.
    - exists x. exact (H x Hx).
    - exact (IH xs).
Defined.

(* Pre-model inclusion is domain and interpretation inclusion *)

Definition premodel_incl {D} (M1 M2 : premodel D) : Prop.
Proof.
  refine { H : M1.(domain) ⊆ M2.(domain) | _ }.
  refine (_ /\ _).
  * refine (∀ (f : name) (Hf : f ∈ Σ.(funs)) (args : vec (elem M1.(domain)) (Σ.(farity) f Hf)), _ =@{elem M2.(domain)} _).
    refine (elem_subseteq _ _ H (M1.(interp_fun) f Hf args)).
    refine (M2.(interp_fun) f Hf (elem_subseteq_vec _ _ H _ args)).
  * refine (∀ (p : name) (Hp : p ∈ Σ.(preds)) (args : vec (elem M1.(domain)) (Σ.(parity) p Hp)), impl _ _).
    refine (args ∈ M1.(interp_pred) p Hp).
    refine ((elem_subseteq_vec _ _ H _ args) ∈ M2.(interp_pred) p Hp).
Defined.

(** * Term evaluation in a given pre-model *) 

Section Eval.

Context {D} (M : premodel D).

Let dom := elem M.(domain).

Definition eval := nat -> dom.

Definition update (n : nat) (e1 e2 : eval) :=
  fun m => if m <? n then e1 m else e2 (m - n).

Fixpoint lapply_eval (e : eval) (l : list term) (H : ltwf l) {struct H} : vec dom (length l) :=
  match H with
  | ltwf_nil => vnil
  | ltwf_cons x l Hx Hl =>
      vcons (tapply_eval e x Hx) (lapply_eval e l Hl)
  end
with tapply_eval (e : eval) (t : term) (H : twf t) {struct H} : dom :=
  match H with
  | twf_var n => e n
  | twf_fun f args Hf Hargs Hlen =>
      interp_fun f Hf (vec_resize Hlen (lapply_eval e args Hargs))
  end.

End Eval.

(** * A Kripke model is a pre-order with pre-models at each node, with pre-model
      inclusion respecting the pre-order *)

Definition monotone {A B : Type} (RA : relation A) (RB : relation B) (f : A -> B) :=
  ∀ x y, RA x y -> RB (f x) (f y).

Class KModel (D : Type) : Type := {
  world : Type;
  accessible : relation world;
  accessible_po : PreOrder accessible;
  model : world -> premodel D;
  model_mono : monotone accessible premodel_incl model;
}.

Infix "≤" := accessible.

(** * Given a Kripke model K, a world α ∈ K and an evaluation e in the domain of
      α, forcing evaluates a flower into a (Coq) proposition. *)

Section Forcing.

Context {D} {K : KModel D}.

Lemma eval_incl {α β} :
  α ≤ β -> eval (model α) -> eval (model β).
Proof.
  move => H e.
  refine (fun n => _).
  case (model_mono α β H) => [Hincl _].
  case (e n) => [a Ha].
  exists a. by apply Hincl.
Defined.

(* Reserved Notation "α : e ⊩f ϕ" (at level 20, e at level 0).
Reserved Notation "α : e ⊩ Φ" (at level 20, e at level 0).
Reserved Notation "α : e ⊩p Δ" (at level 20, e at level 0).

Inductive forces (α : world) (e : eval (model α)) : flower -> Prop :=

| forces_atom p args Hp Hargs Hlen :
    (vec_resize Hlen (lapply_eval (model α) e args Hargs)) ∈ interp_pred p Hp ->
    α : e ⊩f Atom p args

| forces_flower n Φ Δ :
    (∀ β (H : α ≤ β), ∀ (en : eval (model β)),
     let e' := update (model β) n en (eval_incl H e) in
     β : e' ⊩ Φ -> β : e' ⊩p Δ) ->
    α : e ⊩f (n ⋅ Φ ⫐ Δ)

with bforces (α : world) (e : eval (model α)) : bouquet -> Prop :=

with pforces (α : world) (e : eval (model α)) : list garden -> Prop :=

where "α : e ⊩f ϕ" := (forces α e ϕ)
  and "α : e ⊩ Φ" := (bforces α e Φ)
  and "α : e ⊩p Δ" := (pforces α e Δ). *)

Reserved Notation "α : e ⊩f ϕ ! H" (at level 20, e at level 0).
Reserved Notation "α : e ⊩b Φ ! H" (at level 20, e at level 0).
Reserved Notation "α : e ⊩p Δ ! H" (at level 20, e at level 0).

Fixpoint fforces (α : world) (e : eval (model α)) (ϕ : flower) (H : fwf ϕ) : Prop :=
  match H with
  | fwf_atom p args Hp Hargs Hlen =>
      (vec_resize Hlen (lapply_eval (model α) e args Hargs)) ∈ interp_pred p Hp
  | fwf_flower n Φ Δ HΦ HΔ =>
      ∀ β (H : α ≤ β), ∀ (en : eval (model β)),
      let e' := update (model β) n en (eval_incl H e) in
      β : e' ⊩b Φ ! HΦ -> β : e' ⊩p Δ ! HΔ
  end

with bforces (α : world) (e : eval (model α)) (Φ : bouquet) (H : wf Φ) : Prop :=
  match H with
  | wf_nil =>
      True
  | wf_cons ϕ Φ Hϕ HΦ =>
      α : e ⊩f ϕ ! Hϕ /\ α : e ⊩b Φ ! HΦ
  end

with pforces (α : world) (e : eval (model α)) (Δ : list garden) (H : pwf Δ) : Prop :=
  match H with
  | pwf_nil =>
      False
  | pwf_cons n Φ Δ HΦ HΔ =>
      (∃ (en : eval (model α)), α : (update (model α) n en e) ⊩b Φ ! HΦ) \/
      α : e ⊩p Δ ! HΔ
  end

where "α : e ⊩f ϕ ! H" := (fforces α e ϕ H)
  and "α : e ⊩b Φ ! H" := (bforces α e Φ H)
  and "α : e ⊩p Δ ! H" := (pforces α e Δ H).

Definition forces α e (T : theory) :=
  ∀ ϕ, ϕ ∈ T -> let 'ϕ ⇂ H := ϕ in α : e ⊩f ϕ ! H.

Notation "α : e ⊩ T" := (forces α e T) (at level 20, e at level 0).

Definition entails (T U : theory) :=
  ∀ α e, α : e ⊩ T -> α : e ⊩ U.

Definition eqentails T U := entails T U /\ entails U T.

#[export] Instance equiv_eqentails : Equivalence eqentails.
Proof.
  econs; repeat red.
  * move => A. split; done.
  * move => A B [HAB HBA]; done.
  * move => A B C [HAB HBA] [HBC HCB]. split; red; intros.
    apply HBC. by apply HAB.
    apply HBA. by apply HCB.
Qed.

#[export] Instance : Equiv wfbouquet := eqentails.

End Forcing.

Infix "⊨" := entails (at level 40).
Infix "⫤⊨" := eqentails (at level 40).