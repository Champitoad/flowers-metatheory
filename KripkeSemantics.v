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

Definition ffgt : wfflower -> flower := projT1.
Definition bfgt : wfbouquet -> bouquet := projT1.
Coercion ffgt : wfflower >-> flower.
Coercion bfgt : wfbouquet >-> bouquet.

(** ** Theories are sets of well-formed flowers *)

Definition theory := propset wfflower.

Definition ftot (ϕ : wfflower) : theory := {[ ϕ ]}.

Definition btot (Φ : wfbouquet) : theory :=
  let fix aux Φ (HΦ : wf Φ) {struct HΦ} : propset wfflower :=
    match HΦ with
    | wf_nil => propset_empty
    | wf_cons ϕ Φ Hϕ HΦ => {[ ψ | ψ = ϕ ⇂ Hϕ \/ ψ ∈ aux Φ HΦ ]}
    end in
  let 'Φ ⇂ HΦ := Φ in
  aux Φ HΦ.

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

End Forcing.

Infix "⊨" := entails (at level 40).
Infix "⫤⊨" := eqentails (at level 40).