Require Import ssreflect stdpp.propset stdpp.relations.
Require Import Classical ClassicalFacts ProofIrrelevance.

Require Import Flowers.Terms Flowers.Syntax Flowers.KripkeSemantics Flowers.Utils.

(** Useful intuitionistic reasoning principles *)

Lemma demorgan_or {P Q} :
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  intuition.
Qed.

Lemma demorgan_exists {A} {P : A -> Prop} :
  (~ ∃ x, P x) <-> ∀ x, ~ P x.
Proof.
  firstorder.
Qed.

(** Useful classical reasoning principles *)

Lemma contra_recip {P Q : Prop} :
  (~ Q -> ~ P) -> P -> Q.
Proof.
  tauto.
Qed.

Lemma demorgan_impl {P Q} :
  ~ (impl P Q) <-> P /\ ~ Q.
Proof.
  split; intro H.
  * split.
    - apply NNPP. intro H1. apply H. intro H2. destruct H1. exact H2.
    - intro H1. apply H. intros _. exact H1.
  * intuition.
Qed.

Lemma demorgan_forall {A} {P : A -> Prop} :
  (~ ∀ x, P x) <-> ∃ x, ~ P x.
Proof.
  split; intro H.
  * apply NNPP. intro H1. destruct H. intros x.
    apply NNPP. intro H2. destruct H1. exists x. exact H2.
  * destruct H as [x H]. intro H1. destruct H. apply H1.
Qed.

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

Lemma tderiv_tnderiv {T} {ϕ} :
  ~ (T !⊢ ϕ) <-> T !⊬ ϕ.
Proof.
  firstorder.
Qed.

Add Parametric Morphism {ϕ} : (consistent ϕ) with signature
  equiv ==> iff
  as proper_consistent_equiv.
Proof.
  intros T U Hequiv. rewrite /consistent/tnderiv.
  split; intros H Φ HΦ HH.
  * rewrite -Hequiv in HΦ. apply (H Φ); auto.
  * rewrite Hequiv in HΦ. apply (H Φ); auto.
Qed.

Add Parametric Morphism {ϕ} : (consistent ϕ) with signature
  subseteq --> impl
  as proper_consistent_subseteq.
Admitted.

Add Parametric Morphism : tderiv with signature
  equiv ==> eq ==> iff
  as proper_tderiv_equiv.
Admitted.

Lemma tderiv_weakening {T T' : theory} {ϕ : flower} :
  T ⊆ T' -> T !⊢ ϕ -> T' !⊢ ϕ.
Admitted.

Lemma deriv_tderiv Φ (ϕ : flower) :
  Φ ⊢ ϕ -> Φ !⊢ ϕ.
Proof.
  by exists Φ.
Qed.

(** ** Completion of a theory *)

Section Completion.

Context (T : theory) (ϕ : flower) (Hcon : consistent ϕ T).

Axiom enum_flower : nat -> flower.
Axiom enum_flower_bij : bijective enum_flower.

Fixpoint ncompletion (n : nat) : theory :=
  match n with
  | 0 => T
  | S m =>
      let C := ncompletion m in
      C ∪ {[ ψ | ψ = enum_flower m /\ (consistent ϕ (C ∪ ψ)) ]}
  end.

Definition completion : theory :=
  {[ ψ | ∃ n, ψ ∈ ncompletion n ]}.

Lemma subseteq_ncompletion_completion : ∀ n,
  ncompletion n ⊆ completion.
Proof.
  intros n ψ H. by exists n.
Qed.

Lemma subset_completion {U} :
  U ⊆ completion -> ∃ n, U ⊆ ncompletion n.
Proof.
  intros H. do 2 red in H.
  rewrite /completion in H. setoid_rewrite elem_of_PropSet in H.
Admitted.

Lemma enum_consistent_singl {n} :
  consistent ϕ (ncompletion n ∪ enum_flower n) ->
  {[ ψ | ψ = enum_flower n ∧ consistent ϕ (ncompletion n ∪ ψ) ]}
  ≡@{theory}
  enum_flower n.
Admitted.

Lemma enum_nconsistent_empty {n} :
  ~ consistent ϕ (ncompletion n ∪ enum_flower n) ->
  {[ ψ | ψ = enum_flower n ∧ consistent ϕ (ncompletion n ∪ ψ) ]}
  ≡@{theory}
  ∅.
Admitted.

Lemma ncompletion_consistent : ∀ n,
  consistent ϕ (ncompletion n).
Proof.
  elim => [|n IH] //=.
  repeat red. intros Φ HΦ H.
  apply deriv_tderiv in H.
  apply (tderiv_weakening HΦ) in H.
  destruct (classic (consistent ϕ (ncompletion n ∪ enum_flower n))) as [Hc | Hc].
  * rewrite (enum_consistent_singl Hc) in H.
    by rewrite /consistent -tderiv_tnderiv in Hc.
  * rewrite (enum_nconsistent_empty Hc) in H.
    rewrite union_empty_r in H.
    by rewrite /consistent -tderiv_tnderiv in IH.
Qed.

Lemma completion_consistent :
  consistent ϕ completion.
Proof.
  red. rewrite -tderiv_tnderiv. rewrite /completion. intros [Ψ [HΨ H]].
  case (subset_completion HΨ) => {HΨ} [n HΨ].
  pose proof (Hc := proper_consistent_subseteq  _ _ _ HΨ (ncompletion_consistent n)).
  rewrite /consistent -tderiv_tnderiv in Hc.
  by apply deriv_tderiv in H.
Qed.

Lemma completion_complete :
  complete ϕ completion.
Proof.
  red. apply NNPP. intro H. rewrite demorgan_forall in H.
  case: H => [ψ H]. rewrite demorgan_or in H.
  case: H => [H1 H2]. destruct H2.
  rewrite tderiv_tnderiv -/(consistent _ _) in H1.
  rewrite /completion elem_of_PropSet.
  case enum_flower_bij => _ Hsur. red in Hsur.
  case (Hsur ψ) => {Hsur} n ?; subst.
  exists (S n). rewrite /= elem_of_PropSet. right.
  apply elem_of_PropSet. split; auto.
  pose proof (subseteq_ncompletion_completion n).
  epose proof (H' := proper_union_subseteq _ _ _ _ (btot (ftob (enum_flower n))) (btot (ftob (enum_flower n)))) .
  apply (proper_consistent_subseteq _ (completion ∪ enum_flower n)). eapply H'.
  reflexivity. done. Unshelve. done.
Qed.

End Completion.

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