Require Import String.
Open Scope string_scope.
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
    red. intros e ?? H. inv H.
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

Lemma not_prov_tnderiv (ϕ : flower) :
  ~ prov ϕ -> ∅ !⊬ ϕ.
Proof.
  move => H Φ HΦ Hderiv. apply H.
  apply equiv_empty in HΦ. apply btot_equiv_empty in HΦ.
  rewrite HΦ in Hderiv. by apply prov_deriv.
Qed.

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
  split; intros H Φ HΦ HH; set_solver.
Qed.

Add Parametric Morphism {ϕ} : (consistent ϕ) with signature
  subseteq --> impl
  as proper_consistent_subseteq.
Proof.
  intros T U Hincl. rewrite /consistent/tnderiv. intros H Φ HΦ.
  set_solver.
Qed.

Add Parametric Morphism : tderiv with signature
  equiv ==> eq ==> iff
  as proper_tderiv_equiv.
Proof.
  intros T U Hequiv ϕ. rewrite /tderiv. split; intros [Ψ [Hincl H]];
  by (exists Ψ; set_solver).
Qed.

Lemma tderiv_weakening {T T' : theory} {ϕ : flower} :
  T ⊆ T' -> T !⊢ ϕ -> T' !⊢ ϕ.
Proof.
  intros Hincl. rewrite /tderiv. set_solver.
Qed.

Lemma deriv_tderiv Φ (ϕ : flower) :
  Φ ⊢ ϕ -> Φ !⊢ ϕ.
Proof.
  by exists Φ.
Qed.

(** ** Inversion principles for consistent and complete theories *)

Section Inversion.

Definition has_dom (n : nat) (σ : nat -> term) :=
  ∀ m, m >= n -> σ m = TVar m.

Context (T : theory) (ϕ : flower).
Context (Hcon : consistent ϕ T) (Hcom : complete ϕ T).

Lemma inversion_flower_elem_of n Φ Δ :
  (n ⋅ Φ ⫐ Δ) ∈ T -> ∀ σ, has_dom n σ ->
  (∃ m Ψ τ, (m ⋅ Ψ) ∈ Δ /\ has_dom m τ /\ btot (subst τ <$> (subst σ <$> Ψ)) ⊆ T) \/
  ∃ ψ, ψ ∈ Φ /\ T !⊬ subst σ ψ.
Admitted.

Lemma inversion_tnderiv_atom p args :
  T !⊬ (Atom p args) -> Atom p args ∉ T.
Proof.
  intros H HT. red in H. specialize (H (ftob (Atom p args))).
  apply H. set_solver. reflexivity.
Qed.

Lemma inversion_tnderiv_flower n Φ Δ :
  T !⊬ (n ⋅ Φ ⫐ Δ) -> ∃ σ, has_dom n σ /\
  ∀ m Ψ τ, (m ⋅ Ψ) ∈ Δ -> has_dom m τ ->
  ∀ ψ, ψ ∈ Ψ -> T ∪ btot (subst σ <$> Φ) !⊬ subst τ (subst σ ψ).
Admitted.

End Inversion.

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

Axiom subset_completion : ∀ (Φ : bouquet),
  btot Φ ⊆ completion -> ∃ n, btot Φ ⊆ ncompletion n.

(* Lemma subset_completion {Φ : bouquet} :
  btot Φ ⊆ completion -> ∃ n, btot Φ ⊆ ncompletion n.
Proof.
  intros H. do 2 red in H.
  rewrite /completion in H. setoid_rewrite elem_of_PropSet in H.
  assert (ns : list nat).
  { induction Φ as [|ψ Ψ]. exact [].
    refine (_ :: _).
    * assert (Hψ : ψ ∈ ψ :: Ψ) by left.
      specialize (H ψ Hψ).
      (* case: H => n Hn. *)
      admit.
    * apply IHΨ. intros. apply H. by right. }
Admitted. *)

Lemma enum_consistent_singl {n} :
  consistent ϕ (ncompletion n ∪ enum_flower n) ->
  {[ ψ | ψ = enum_flower n ∧ consistent ϕ (ncompletion n ∪ ψ) ]}
  ≡@{theory}
  enum_flower n.
Proof.
  set_solver.
Qed.

Lemma enum_nconsistent_empty {n} :
  ~ consistent ϕ (ncompletion n ∪ enum_flower n) ->
  {[ ψ | ψ = enum_flower n ∧ consistent ϕ (ncompletion n ∪ ψ) ]}
  ≡@{theory}
  ∅.
Proof.
  set_solver.
Qed.

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
  case (subset_completion Ψ HΨ) => {HΨ} [n HΨ].
  pose proof (Hc := proper_consistent_subseteq _ _ _ HΨ (ncompletion_consistent n)).
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

Section KCompleteness.

Context (T : theory) (ϕ : flower) (Hϕ : closed 0 ϕ) (Hcon : consistent ϕ T).

Let K := KCanon ϕ.

Lemma tapply_eval_TFun (w : K.(world)) e f args :
  tapply_eval (model w) e (TFun f args) =
  interp_fun f (tapply_eval (model w) e <$> args).
Proof.
  done.
Qed.

Lemma proj1_interp_fun (w : K.(world)) f args :
  proj1_sig ((K.(model) w).(interp_fun) f args) =
  TFun f (proj1_sig <$> args).
Proof.
  by destruct w as [U [HUcon HUcom]].
Qed.

Lemma proj1_tapply_eval (w : K.(world)) e : ∀ t,
  tclosed 0 t ->
  proj1_sig (tapply_eval (model w) e t) = t.
Proof.
  elim/term_induction => [n /= |f args IH] H; inv H.
  * lia.
  * apply (Forall_impl args H1) in IH. apply Forall_eq_map in IH.
    rewrite map_id_ext in IH.
    rewrite -{2}IH tapply_eval_TFun proj1_interp_fun -list_fmap_compose.
    done.
Qed.

Lemma proj1_tapply_eval_fmap (w : K.(world)) e : ∀ (ts : list term),
  Forall (tclosed 0) ts ->
  proj1_sig <$> (tapply_eval (model w) e <$> ts) = ts.
Proof.
  intros ts H. rewrite -list_fmap_compose -{2}[ts]list_fmap_id.
  apply Forall_eq_map. induction H; auto. econs.
  rewrite /compose proj1_tapply_eval; done.
Qed.

Definition dummy_eval (w : K.(world)) : eval (model w).
Proof.
  destruct w. intros n. by exists (TFun "dummy" []).
Defined.

Lemma atom_elem_of_forces (w : K.(world)) p args :
  let '(exist _ U (conj Hcon Hcom)) := w in
  Forall (tclosed 0) args ->
  Atom p args ∈ U <-> (∀ e, w ∷ e ⊩ Atom p args).
Proof.
  destruct w as [U [HUcon HUcom]] eqn:Hw.
  set W : K.(world) := U ↾ conj HUcon HUcom.
  intros Hclosed; split; intros H.
  * intros e. red. intros ψ _ Hψ.
    assert (Heq : ψ = Atom p args) by set_solver; rewrite Heq; clear Heq Hψ.
    red. rewrite [interp_pred _]/=. apply elem_of_PropSet.
    rewrite (proj1_tapply_eval_fmap W); done.
  * specialize (H (dummy_eval W)). cbn in H.
    rewrite /forces/= in H.
    specialize (H (Atom p args)).
    rewrite /fforces [interp_pred _]/= in H.
    apply elem_of_PropSet in H.
    - rewrite (proj1_tapply_eval_fmap W) in H; done.
    - by constructor.
    - set_solver.
Qed.

Lemma adequacy_forcing (w : K.(world)) :
  let '(exist _ U (conj Hcon Hcom)) := w in
  ∀ (ψ : flower), closed 0 ψ ->
  (ψ ∈ U -> ∀ e, w ∷ e ⊩ ψ) /\ (U !⊬ ψ -> ∃ e, ~ w ∷ e ⊩ ψ).
Proof.
  destruct w as [U [HUcon HUcom]] eqn:Hw.
  set W : K.(world) := U ↾ conj HUcon HUcom.
  elim/flower_induction => [p args |[n Φ] Δ IHΦ IHΔ] Hclosed;
  inv Hclosed; split; intros H.
  * apply (atom_elem_of_forces W); done.
  * assert (HU : Atom p args ∉ U) by (apply (inversion_tnderiv_atom _ ϕ); auto).
    rewrite (atom_elem_of_forces W) in HU; auto.
    by rewrite demorgan_forall in HU.
  * admit.
  * admit.
Admitted.

Let C : K.(world).
Proof.
  exists (completion T ϕ). split.
  by apply completion_consistent.
  by apply completion_complete.
Defined.

Lemma completeness_contra :
  T !⊬ ϕ -> ∃ A (K : KModel A), ~ (T ⊨ ϕ).
Proof.
  intros H. exists term. exists K.
  rewrite /entails. apply demorgan_forall.
  exists C. apply demorgan_impl.
  split.
  * intros e. red. intros ψ Hclosed Hψ.
    case (adequacy_forcing C ψ Hclosed) => HC1 HC2.
    apply HC1; [> |auto |set_solver].
    by apply (subseteq_ncompletion_completion _ _ 0).
  * apply demorgan_forall.
    case (adequacy_forcing C ϕ Hϕ) => HC1 HC2.
    apply HC2. by apply completion_consistent.
Qed.

End KCompleteness.

Theorem completeness (ϕ : flower) (Hclosed : closed 0 ϕ) :
  (∀ A (K : KModel A), ∅ ⊨ ϕ) -> prov ϕ.
Proof.
  apply contra_recip. move => H H'. apply not_prov_tnderiv in H.
  apply completeness_contra in H; auto. move: H => [A' [K' H]].
  apply H; auto.
Qed.

End Completeness.

(** * Then we trivially get structural admissibility *)

Theorem structural_admissibility (ϕ : flower) (Hclosed : closed 0 ϕ) :
  sprov ϕ -> prov ϕ.
Proof.
  intros. apply completeness; auto. intros.
  by apply soundness.
Qed.