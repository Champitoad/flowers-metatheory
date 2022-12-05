Require Import ssreflect stdpp.boolset stdpp.propset stdpp.vector.

Require Import Flowers.Utils Flowers.Terms Flowers.Syntax.

(** ** Theories are sets of flowers *)

Definition theory := propset flower.

Definition btot (Φ : bouquet) : theory :=
  {[ ϕ | ϕ ∈ Φ ]}.

Coercion btot : bouquet >-> theory.

Lemma empty_bouquet_theory :
  btot [] ≡@{theory} ∅.
Proof.
  repeat red. move => ϕ. split; move => H; inv H.
Qed.

Lemma btot_equiv_empty (Φ : bouquet) :
  Φ ≡@{theory} ∅ -> Φ = [].
Proof.
  move => H. repeat red in H.
  apply equiv_nil. repeat red. move => ϕ.
  case (H ϕ) => {H} [H1 H2]. split; move => Hϕ.
  * specialize (H1 Hϕ). inv H1.
  * inv Hϕ.
Qed.

(** * Pre-models are just domains with interpretation functions for terms and
      predicates *)

Class premodel (D : Type) := {
  domain : propset D;
  interp_fun : name -> list (elem domain) -> elem domain;
  interp_pred : name -> propset (list (elem domain))
}.

(* Pre-model inclusion is domain and interpretation inclusion *)

Definition premodel_incl {D} (M1 M2 : premodel D) : Prop.
Proof.
  refine { H : M1.(domain) ⊆ M2.(domain) | _ }.
  refine (_ /\ _).
  * refine (∀ (f : name) (args : list (elem M1.(domain))), _ =@{elem M2.(domain)} _).
    refine (elem_subseteq H (M1.(interp_fun) f args)).
    refine (M2.(interp_fun) f (elem_subseteq_list H args)).
  * refine (∀ (p : name) (args : list (elem M1.(domain))), impl _ _).
    refine (args ∈ M1.(interp_pred) p).
    refine ((elem_subseteq_list H args) ∈ M2.(interp_pred) p).
Defined.

(** * Term evaluation in a given pre-model *) 

Section Eval.

Context {D} (M : premodel D).

Let dom := elem M.(domain).

Definition eval := nat -> dom.

Definition update (n : nat) (e1 e2 : eval) :=
  fun m => if m <? n then e1 m else e2 (m - n).

Fixpoint tapply_eval (e : eval) (t : term) {struct t} : dom :=
  match t with
  | TVar n => e n
  | TFun f args =>
      interp_fun f (tapply_eval e <$> args)
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

Lemma eval_incl {w w'} :
  w ≤ w' -> eval (model w) -> eval (model w').
Proof.
  move => H e.
  refine (fun n => _).
  case (model_mono w w' H) => [Hincl _].
  case (e n) => [a Ha].
  exists a. by apply Hincl.
Defined.

Fixpoint fforces (w : world) (e : eval (model w)) (ϕ : flower) {struct ϕ} : Prop :=
  let fix bforces w e Φ :=
    match Φ with
    | [] => True
    | ϕ :: Φ =>
        fforces w e ϕ /\ bforces w e Φ
    end in
  let fix pforces w e Δ :=
    match Δ with
    | [] => False
    | (n ⋅ Φ) :: Δ =>
        (∃ (en : eval (model w)), bforces w (update (model w) n en e) Φ) \/
        pforces w e Δ
    end in
  match ϕ with
  | Atom p args =>
      tapply_eval (model w) e <$> args ∈ interp_pred p
  | Flower (n ⋅ Φ) Δ =>
      ∀ w' (H : w ≤ w'), ∀ (en : eval (model w')),
      let e' := update (model w') n en (eval_incl H e) in
      bforces w' e' Φ -> pforces w' e' Δ
  end.

Definition forces α e (T : theory) :=
  ∀ ϕ, ϕ ∈ T -> fforces α e ϕ.

Notation "α : e ⊩ T" := (forces α e T) (at level 20, e at level 0).

Definition entails (T U : theory) :=
  ∀ α e, α : e ⊩ T -> α : e ⊩ U.

Definition eqentails T U := entails T U /\ entails U T.

#[export] Instance preorder_entails : PreOrder entails.
Proof.
  econs; red.
  * move => T. done.
  * move => T1 T2 T3. rewrite /entails. move => H1 H2 α e H.
    apply H2. by apply H1.
Qed.

#[export] Instance equiv_eqentails : Equivalence eqentails.
Proof.
  econs; repeat red.
  * move => A. split; done.
  * move => A B [HAB HBA]; done.
  * move => A B C [HAB HBA] [HBC HCB]. split; red; intros.
    apply HBC. by apply HAB.
    apply HBA. by apply HCB.
Qed.

#[export] Instance : Equiv bouquet := eqentails.

End Forcing.

#[export] Hint Extern 1 (entails _ _) => reflexivity : core.
#[export] Hint Extern 1 (eqentails _ _) => reflexivity : core.

Infix "⊨" := entails (at level 40).
Infix "⫤⊨" := eqentails (at level 40).

Add Parametric Morphism {A} (K : KModel A) : entails with signature
  equiv ==> equiv ==> impl
  as equiv_entails.
Proof.
  rewrite /entails/forces.
  move => T T' HT U U' HU H α e Hf ϕ Hϕ.
  apply H. move => ϕ' Hϕ'. apply Hf. by apply HT.
  by apply HU.
Qed.