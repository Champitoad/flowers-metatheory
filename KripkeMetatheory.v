Require Import ssreflect stdpp.propset stdpp.relations.
Require Import Classical.

Require Import Flowers.Syntax Flowers.KripkeSemantics Flowers.Utils.

Context (Σ : sig).

(** * Soundness *)

Section Soundness.

Context A (K : KModel A).

Lemma local_soundness (Φ Ψ : wfbouquet) :
  Φ ⇀ Ψ -> Φ ⫤⊨ Ψ.
Admitted.

Lemma grounding : ∀ (X : wfctx) (Φ Ψ : wfbouquet),
  Φ ⫤⊨ Ψ -> btot (X ⋖ Φ ⇂ wf_fill X Φ) ⫤⊨ btot (X ⋖ Ψ ⇂ wf_fill X Ψ).
Admitted.

Lemma pgrounding : ∀ (P : wfpctx) (Φ Ψ : wfbouquet),
  Φ ⊨ Ψ -> btot (P ⋖ Φ ⇂ wf_fill P Φ) ⊨ btot (P ⋖ Ψ ⇂ wf_fill P Ψ).
Admitted.

Lemma in_bouquet : ∀ (Φ : bouquet) (H H' : wf Φ) ϕ,
  ϕ ∈ btot (Φ ⇂ H) <-> ϕ ∈ btot (Φ ⇂ H').
Proof.
  done.
Qed.

Lemma entails_refl (Φ : bouquet) (H H' : wf Φ) :
  btot (Φ ⇂ H) ⊨ btot (Φ ⇂ H').
Proof.
  intros ?? Hf ϕ. by apply (Hf ϕ).
Qed.

Lemma eqentails_refl (Φ : bouquet) (H H' : wf Φ) :
  btot (Φ ⇂ H) ⫤⊨ btot (Φ ⇂ H').
Proof.
  split; by apply entails_refl.
Qed.

Lemma wf_cstep {Φ Ψ : bouquet} :
  Φ ≈> Ψ -> wf Φ -> wf Ψ.
Admitted.

Theorem soundness : ∀ (Φ Ψ : wfbouquet),
  Φ ≈>* Ψ -> Φ ⫤⊨ Ψ.
Proof.
  move => [Φ HΦ] [Ψ HΨ]. do 2 rewrite [bfgt _]/=.
  induction 1 as [Φ |Φ1 Φ2 Φ3 Hstep H IH].
  * by apply eqentails_refl.
  * rewrite -(IH (wf_cstep Hstep HΦ) HΨ). admit.
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
Admitted.