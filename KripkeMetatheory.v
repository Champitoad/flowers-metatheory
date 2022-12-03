Require Import ssreflect stdpp.propset stdpp.relations.
Require Import Classical.

Require Import Flowers.Syntax Flowers.KripkeSemantics Flowers.Utils.

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

Theorem soundness : ∀ (Φ Ψ : bouquet),
  Φ ≈>* Ψ -> Φ ⫤⊨ Ψ.
Proof.
Admitted.

End Soundness.

(** * Completeness *)

Section Completeness.

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
Admitted.

Theorem completeness (ϕ : flower) :
  (∀ A (K : KModel A), ∅ ⊨ ϕ) -> prov ϕ.
Proof.
  apply contra_recip. move => H H'. apply not_prov_tnderiv in H.
  apply completeness_contra in H. move: H => [A' [K' H]].
  apply H. apply H'.
Qed.

End Completeness.

Theorem structural_admissibility (ϕ : flower) :
  sprov ϕ -> prov ϕ.
Proof.
  intros. apply completeness. intros.
Admitted.