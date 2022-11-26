Require Import ssreflect stdpp.propset.

Require Import Flowers.Syntax Flowers.Utils.

Definition theory : Type := propset flower.

Definition bouquet_to_theory (Φ : bouquet) : theory :=
  {| propset_car := λ ϕ, In ϕ Φ |}.

Coercion bouquet_to_theory : bouquet >-> theory.

Definition tentails (T : theory) (Ψ : bouquet) :=
  ∃ Φ, (bouquet_to_theory Φ) ⊂ T /\ Φ ⊢ Ψ.

Definition tnentails (T : theory) (Ψ : bouquet) :=
  ∀ Φ, (bouquet_to_theory Φ) ⊂ T -> ~ Φ ⊢ Ψ.

Infix "!⊢" := tentails (at level 70).
Infix "!⊬" := tnentails (at level 70).

Definition consistent (Θ : bouquet) (T : theory) :=
  T !⊬ Θ.

Definition complete (Θ : bouquet) (T : theory) :=
  ∀ Φ, T ∪ Φ !⊢ Θ \/ Φ ⊂ T.