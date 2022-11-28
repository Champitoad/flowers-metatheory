Require Import ssreflect stdpp.propset.
Require Import Classical.

Require Import Flowers.Syntax Flowers.KripkeSemantics Flowers.Utils.

Context (Σ : sig).

(** * Soundness *)

Section Soundness.

Theorem soundness (ϕ : wfflower) :
  sprov ϕ -> ∀ A (K : KModel A), ∅ ⊨ ϕ.
Proof.
Admitted.

End Soundness.

(** * Completeness *)

Section Completeness.

Definition tderiv (T : theory) (ϕ : wfflower) :=
  ∃ (Φ : wfbouquet), btot Φ ⊆ T /\ let 'Φ ⇂ _ := Φ in Φ ⊢ ϕ.

Definition tnderiv (T : theory) (ϕ : wfflower) :=
  ∀ (Φ : wfbouquet), btot Φ ⊆ T -> let 'Φ ⇂ _ := Φ in ~ (Φ ⊢ ϕ).

Infix "!⊢" := tderiv (at level 70).
Infix "!⊬" := tnderiv (at level 70).

Definition consistent (ϕ : wfflower) (T : theory) :=
  T !⊬ ϕ.

Definition complete (ϕ : wfflower) (T : theory) :=
  ∀ (ψ : wfflower), T ∪ ψ !⊢ ϕ \/ ψ ∈ T.

Lemma completeness_contra T ϕ :
  T !⊬ ϕ -> ∃ A (K : KModel A), ~ (T ⊨ ϕ).
Admitted.

Lemma contra_recip (P Q : Prop) :
  (~ Q -> ~ P) -> P -> Q.
Proof.
  tauto.
Qed.

Lemma not_prov_tnderiv (ϕ : wfflower) :
  ~ prov ϕ -> ∅ !⊬ ϕ.
Admitted.

Theorem completeness (ϕ : wfflower) :
  (∀ A (K : KModel A), ∅ ⊨ ϕ) -> prov ϕ.
Proof.
  apply contra_recip. move => H H'. apply not_prov_tnderiv in H.
  apply completeness_contra in H. move: H => [A' [K' H]].
  apply H. apply H'.
Qed.

End Completeness.

Theorem structural_admissibility (ϕ : wfflower) :
  sprov ϕ -> prov ϕ.
Proof.
  intros. apply completeness. intros.
  by apply soundness.
Qed.