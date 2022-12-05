Require Import ssreflect stdpp.propset stdpp.relations.
Require Import Classical ProofIrrelevance.

Require Import Flowers.Terms Flowers.Syntax Flowers.KripkeSemantics Flowers.Utils.

(** * Soundness *)

Section Soundness.

Context A (K : KModel A).

Lemma local_soundness (Φ Ψ : bouquet) :
  Φ ⇀ Ψ -> Φ ⫤⊨ Ψ.
Admitted.

Lemma grounding : ∀ (X : ctx) (Φ Ψ : bouquet),
  Φ ⫤⊨ Ψ -> X ⋖ Φ ⫤⊨ X ⋖ Ψ.
Admitted.

Lemma pgrounding : ∀ (P : pctx) (Φ Ψ : bouquet),
  Φ ⊨ Ψ -> P ⋖ Φ ⊨ P ⋖ Ψ.
Admitted.

Lemma soundness_sstep (Φ Ψ : bouquet) :
  Φ ≈>* Ψ -> Ψ ⊨ Φ.
Proof.
  elim => {Φ Ψ} [? |Φ1 Φ2 Φ3 H1 H2 IH] //.
  etransitivity. eapply IH.
  induction H1 as [X Φ Ψ H |P Φ].
  * apply grounding. by apply local_soundness.
  * apply pgrounding.
    red. intros * _.
    red. intros ? H. inv H.
Qed.

Theorem soundness (Φ : bouquet) :
  sprov Φ -> ∅ ⊨ Φ.
Proof.
  move => H. red in H.
  rewrite -empty_bouquet_theory.
  by apply soundness_sstep.
Qed.

End Soundness.

(** * Completeness *)

Section Completeness.

(** ** Properties of theories *)

Definition tderiv (T : theory) (ϕ : flower) :=
  ∃ (Φ : bouquet), btot Φ ⊆ T /\ Φ ⊢ ϕ.

Definition tnderiv (T : theory) (ϕ : flower) :=
  ∀ (Φ : bouquet), btot Φ ⊆ T -> ~ (Φ ⊢ ϕ).

Infix "!⊢" := tderiv (at level 70).
Infix "!⊬" := tnderiv (at level 70).

Definition consistent (ϕ : flower) (T : theory) :=
  T !⊬ ϕ.

Definition complete (ϕ : flower) (T : theory) :=
  ∀ (ψ : flower), T ∪ ψ !⊢ ϕ \/ ψ ∈ T.

(** ** Canonical Kripke model *)

Lemma eq_sig {A} (P : A -> Prop) (t : A) (Ht : P t) (u : A) (Hu : P u) :
  t = u -> t ↾ Ht = u ↾ Hu.
Proof.
  move => H. destruct H. by rewrite (proof_irrelevance _ Ht Hu).
Qed.

Section Canonical.

Context (ϕ : flower).

Let world : Type :=
  { T | consistent ϕ T /\ complete ϕ T }.

Let accessible : relation world :=
  λ '(T ↾ _) '(U ↾ _), T ⊆ U.

Let accessible_po : PreOrder accessible.
Proof.
  econs; red.
  * move => [??]. red. reflexivity.
  * move => [??][??][??]??/=. etransitivity; eauto.
Qed.

Let model (w : world) : premodel term.
Proof.
  refine (let '(T ↾ _) := w in _).
  refine {| domain := {[ t | cst t ]}; interp_fun := _; interp_pred := _ |}.
  * intros f args. exists (TFun f (proj1_sig <$> args)).
    apply elem_of_PropSet. constructor. by apply list_elem_Forall.
  * intros p. constructor. intros args.
    exact (Atom p (proj1_sig <$> args) ∈ T).
Defined.

Let model_mono : monotone accessible premodel_incl model.
Proof.
  move => [T HT] [U HU] /= Hsub. red.
  exists (PreOrder_Reflexive domain). split; intros.
  * simpl. apply eq_sig. f_equal.
    by rewrite proj1_elem_subseteq_list.
  * repeat rewrite elem_of_PropSet. move => H. apply Hsub.
    by rewrite proj1_elem_subseteq_list.
Qed.

Instance KCanon : KModel term :=
  {| KripkeSemantics.world := world;
     KripkeSemantics.accessible := accessible;
     KripkeSemantics.accessible_po := accessible_po;
     KripkeSemantics.model := model;
     KripkeSemantics.model_mono := model_mono |}.

End Canonical.

(** ** Completeness *)

Lemma completeness_contra T ϕ :
  T !⊬ ϕ -> ∃ A (K : KModel A), ~ (T ⊨ ϕ).
Admitted.

Lemma contra_recip (P Q : Prop) :
  (~ Q -> ~ P) -> P -> Q.
Proof.
  tauto.
Qed.

Lemma not_prov_tnderiv (ϕ : flower) :
  ~ prov ϕ -> ∅ !⊬ ϕ.
Proof.
  move => H Φ HΦ Hderiv. apply H.
  apply equiv_empty in HΦ. apply btot_equiv_empty in HΦ.
  rewrite HΦ in Hderiv. by apply prov_deriv.
Qed.

Theorem completeness (ϕ : flower) :
  (∀ A (K : KModel A), ∅ ⊨ ϕ) -> prov ϕ.
Proof.
  apply contra_recip. move => H H'. apply not_prov_tnderiv in H.
  apply completeness_contra in H. move: H => [A' [K' H]].
  apply H. apply H'.
Qed.

End Completeness.

(** * Then we trivially get structural admissibility *)

Theorem structural_admissibility (ϕ : flower) :
  sprov ϕ -> prov ϕ.
Proof.
  intros. apply completeness. intros.
  by apply soundness.
Qed.