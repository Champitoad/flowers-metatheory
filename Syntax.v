Require Import stdpp.list stdpp.relations stdpp.list_numbers.
Require Import ssreflect.
Require Import String.
Require Import ZifyBool.

Require Import Flowers.Terms Flowers.Utils.

(** * Flowers *)

Inductive flower :=
| Atom (p : name) (args : list term)
| Flower (γ : nat * list flower) (Δ : list (nat * list flower)).

Definition garden : Type := nat * list flower.
Definition bouquet := list flower.
Definition petals := list garden.

Definition ftog : flower -> garden := λ ϕ, (0, [ϕ]).
Coercion ftog : flower >-> garden.

Definition ftob : flower -> bouquet := λ ϕ, [ϕ].
Coercion ftob : flower >-> bouquet.

Definition btog : bouquet -> garden := λ Φ, (0, Φ).
Coercion btog : bouquet >-> garden.

#[global] Instance empty_garden : Empty garden := (0, nil).
Notation "n ⋅ Φ" := (n, Φ) (format "n  ⋅  Φ", at level 63).

Notation "γ ⫐ Δ" := (Flower γ Δ) (at level 65).
Notation "γ ⫐" := (Flower γ nil) (at level 65).
Notation "⫐ Δ" := (Flower ∅ Δ) (at level 65).

(** ** Closed flowers *)

Inductive tclosed (c : nat) : term -> Prop :=

| tclosed_var n :
  n < c ->
  tclosed c (TVar n)

| tclosed_fun f args :
  Forall (tclosed c) args ->
  tclosed c (TFun f args).

Inductive closed (c : nat) : flower -> Prop :=

| closed_atom p args :
  Forall (tclosed c) args ->
  closed c (Atom p args)

| closed_flower n Φ Δ :
  Forall (closed (c + n)) Φ ->
  Forall (gclosed (c + n)) Δ ->
  closed c (n ⋅ Φ ⫐ Δ)

with gclosed (c : nat) : garden -> Prop :=

| closed_garden n Φ :
  Forall (closed (c + n)) Φ ->
  gclosed c (n ⋅ Φ).

Definition cflower := { ϕ : flower | closed 0 ϕ }.

Lemma tclosed_cst : ∀ t,
  tclosed 0 t <-> cst t.
Proof.
  elim/term_induction => [n |f args IH]; split; intros H; inv H;
  inv H1; econs; apply Forall_equiv in IH; intuition.
Qed.

Lemma tsubst_cst σ : ∀ t,
  cst t ->
  tsubst σ t = t.
Proof.
  elim/term_induction => [n |f args IH] H //=; inv H.
  apply Forall_impl in IH; auto.
  apply Forall_eq_map in IH.
  by rewrite IH list_fmap_id.
Qed.

Lemma tshift_cst n c : ∀ t,
  cst t ->
  tshift n c t = t.
Proof.
  elim/term_induction => [i |f args IH] H //=; inv H.
  apply Forall_impl in IH; auto.
  apply Forall_eq_map in IH.
  by rewrite IH list_fmap_id.
Qed.

(** ** Induction principles *)

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pt : term -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHt : ∀ (t : term), Pt t)
    (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⫐ Δ))
    (IHgarden : ∀ (n : nat) (Φ : bouquet),
      Forall P Φ -> Pγ (n ⋅ Φ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. move: ϕ. fix IH 1. induction ϕ.
  * apply IHatom. apply In_Forall. intros. by apply IHt.
  * apply IHflower.
    - case: γ => n Φ.
      apply IHgarden.
      elim: Φ => [|ϕ Φ IHΦ] //.
    - elim: Δ => [|δ Δ IHΔ] //.
      decompose_Forall; auto.
      case δ => n Φ. apply IHgarden; auto.
      decompose_Forall; auto.
Qed.

Definition flower_induction	:
  ∀ (P : flower -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHatom : ∀ p args, P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⫐ Δ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. eapply flower_induction_full; eauto.
  exact (λ _, I).
Qed.

Definition flower_recursion_full :
  ∀ (P : flower -> Type)
    (Pt : term -> Type),
  let Pγ '(n ⋅ Φ) := ForallT P Φ in
  ∀ (IHt : ∀ (t : term), Pt t)
    (IHatom : ∀ p args, ForallT Pt args -> P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> ForallT Pγ Δ -> P (γ ⫐ Δ))
    (IHgarden : ∀ (n : nat) (Φ : bouquet),
      ForallT P Φ -> Pγ (n ⋅ Φ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. move: ϕ. fix IH 1. induction ϕ.
  * apply IHatom. apply In_ForallT. intros. by apply IHt.
  * apply IHflower.
    - case: γ => n Φ.
      apply IHgarden.
      elim: Φ => [|ϕ Φ IHΦ]; constructor.
      apply IH. exact IHΦ.
    - elim: Δ => [|δ Δ IHΔ]; constructor.
      case δ => n Φ. apply IHgarden.
      elim: Φ => [|ϕ Φ IHΦ]; constructor.
      apply IH. exact IHΦ.
      exact IHΔ.
Qed.

Definition flower_recursion	:
  ∀ (P : flower -> Type),
  let Pγ '(n ⋅ Φ) := ForallT P Φ in
  ∀ (IHatom : ∀ p args, P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> ForallT Pγ Δ -> P (γ ⫐ Δ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. eapply flower_recursion_full; eauto.
  exact (λ _, I).
Qed.

(** *** Depth induction *)

Fixpoint depth (ϕ : flower) {struct ϕ} : nat :=
  let bdepth := max_list_with depth in
  let gdepth '(_ ⋅ Φ) := bdepth Φ in
  match ϕ with
  | Atom _ _ => 0
  | _ ⋅ Φ ⫐ Δ => S (max (bdepth Φ) (max_list_with gdepth Δ))
  end.

Lemma inv_depth_zero : ∀ ϕ,
  depth ϕ = 0 -> ∃ p args, ϕ = Atom p args.
Proof.
  case => [p args |[??]?] H. by exists p, args. inv H.
Qed.

Lemma inv_depth_succ : ∀ ϕ n,
  depth ϕ = S n -> ∃ γ Δ, ϕ = γ ⫐ Δ.
Proof.
  case => [?? |γ Δ] n H. inv H. by exists γ, Δ.
Qed.

Lemma flower_depth_ind :
  ∀ (P : flower -> Prop), 
  (∀ p args, P (Atom p args)) ->
  (∀ γ Δ, (∀ ψ, depth ψ < depth (γ ⫐ Δ) -> P ψ) -> P (γ ⫐ Δ)) ->
  ∀ ϕ, P ϕ.
Proof.
  intros P Hatom Hflower ϕ.
  assert (H : ∃ n, depth ϕ <= n) by (by exists (depth ϕ)).
  case: H => n H; move: n ϕ H.
  elim => [|n IHn] ϕ H.
  * assert (H' : depth ϕ = 0) by lia.
    case (inv_depth_zero _ H') => p [args ?]; subst.
    by apply Hatom.
  * case (depth ϕ =? S n) eqn:?Hϕn.
    - apply Nat.eqb_eq in Hϕn.
      case (inv_depth_succ _ _ Hϕn) => γ [Δ ?]; subst.
      apply Hflower. rewrite Hϕn. intros ψ Hψ.
      assert (Hψ' : depth ψ <= n) by lia. by apply IHn.
    - assert (Hϕ : depth ϕ <= n) by lia. by apply IHn.
Qed.

Lemma depth_pistil n Φ Δ :
  ∀ ϕ, ϕ ∈ Φ -> depth ϕ < depth (n ⋅ Φ ⫐ Δ).
Admitted.

Lemma depth_petal n Φ Δ :
  ∀ m Ψ, (m ⋅ Ψ) ∈ Δ -> ∀ ψ, ψ ∈ Ψ -> depth ψ < depth (n ⋅ Φ ⫐ Δ).
Admitted.

(** ** Operations on De Bruijn indices *)

Fixpoint shift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tshift n c <$> args)
  | m ⋅ Φ ⫐ Δ =>
      m ⋅ shift n (c + m) <$> Φ ⫐
        ((λ '(k ⋅ Ψ), k ⋅ shift n (c + m + k) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gshift n c '(m ⋅ Φ) : garden :=
  m ⋅ shift n (c + m) <$> Φ.

Fixpoint unshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tunshift n c <$> args)
  | m ⋅ Φ ⫐ Δ =>
      m ⋅ unshift n (c + m) <$> Φ ⫐
        ((λ '(k ⋅ Ψ), k ⋅ unshift n (c + m + k) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gunshift n c '(m ⋅ Φ) : garden :=
  m ⋅ unshift n (c + m) <$> Φ.

Fixpoint subst (σ : sbt) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tsubst σ <$> args)
  | m ⋅ Φ ⫐ Δ =>
      m ⋅ subst (sshift m σ) <$> Φ ⫐
        ((λ '(k ⋅ Ψ), k ⋅ subst (sshift (m + k) σ) <$> Ψ) : garden -> garden) <$> Δ
  end.

Lemma depth_subst : ∀ ϕ σ,
  depth (subst σ ϕ) = depth ϕ.
Admitted.

Definition bsubst σ (Φ : bouquet) : bouquet :=
  subst σ <$> Φ.

Definition gsubst σ '(m ⋅ Φ) : garden :=
  m ⋅ subst (sshift m σ) <$> Φ.

Lemma subst_id :
  subst idsubst = id.
Admitted.

Lemma bsubst_id :
  bsubst idsubst = id.
Admitted.

Lemma gsubst_id :
  gsubst idsubst = id.
Admitted.

Lemma shift_zero : ∀ ϕ c,
  shift 0 c ϕ = ϕ.
Proof.
  elim/flower_induction => [p args |[m Φ] Δ IHγ IHΔ] c /=.

  * pose proof (H := eq_map (tshift 0 c) id args (tshift_zero c)).
    by rewrite H list_fmap_id.

  * rewrite Forall_forall in IHγ; specialize (IHγ (c + m)).
    apply Forall_eq_map in IHγ; rewrite IHγ map_id_ext.

    elim: {Δ} IHΔ => [|[n Ψ] Δ IHΨ IHΔ IH] //=; inv IH.
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + m + n)).
    apply Forall_eq_map in IHΨ; rewrite IHΨ map_id_ext.
    by repeat f_equal.
Qed.

Lemma shift_add : ∀ ϕ c n m,
  shift (n + m) c ϕ = shift n c (shift m c ϕ).
Proof.
  elim/flower_induction => [p args |[k Φ] Δ IHγ IHΔ] c n m /=.

  * pose proof (H := eq_map (tshift (n + m) c) _ args (tshift_add c n m)).
    by rewrite H list_fmap_compose.

  * rewrite Forall_forall in IHγ; specialize (IHγ (c + k));
    rewrite Forall_forall in IHγ; specialize (IHγ n);
    rewrite Forall_forall in IHγ; specialize (IHγ m).
    apply Forall_eq_map in IHγ; rewrite IHγ list_fmap_compose.

    elim: {Δ} IHΔ => [|[l Ψ] Δ IHΨ IHΔ IH]//=; inv IH.
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + k + l));
    rewrite Forall_forall in IHΨ; specialize (IHΨ n);
    rewrite Forall_forall in IHΨ; specialize (IHΨ m).
    apply Forall_eq_map in IHΨ; rewrite IHΨ.
    f_equal. f_equal.
    by rewrite list_fmap_compose.
    done.
Qed.

Lemma shift_comm c n m ϕ :
  shift n c (shift m c ϕ) = shift m c (shift n c ϕ).
Proof.
  by rewrite -shift_add Nat.add_comm shift_add.
Qed.

Lemma bshift_zero : ∀ (Φ : bouquet) c,
  shift 0 c <$> Φ = Φ.
Proof.
  intros. rewrite -{2}[Φ]map_id_ext. apply eq_map.
  intros. by apply shift_zero.
Qed.

Lemma unshift_zero : ∀ (ϕ : flower) c,
  unshift 0 c ϕ = ϕ.
Proof.
  elim/flower_induction => [p args |[m Φ] Δ IHγ IHΔ] c /=.

  * pose proof (H := eq_map (tunshift 0 c) id args (tunshift_zero c)).
    by rewrite H list_fmap_id.

  * rewrite Forall_forall in IHγ; specialize (IHγ (c + m)).
    apply Forall_eq_map in IHγ; rewrite IHγ map_id_ext.

    elim: {Δ} IHΔ => [|[n Ψ] Δ IHΨ IHΔ IH] //=; inv IH.
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + m + n)).
    apply Forall_eq_map in IHΨ; rewrite IHΨ map_id_ext.
    by repeat f_equal.
Qed.

Lemma unshift_shift : forall (ϕ : flower) m n c, 
  unshift (m + n) c (shift n c ϕ) = unshift m c ϕ.
Proof.
  elim/flower_induction => [p args |[k Φ] Δ IHγ IHΔ] m n c /=.

  * pose proof (H := eq_map _ _ args (tunshift_tshift m n c)).
    f_equal. rewrite -list_fmap_compose.
    by rewrite H.

  * rewrite Forall_forall in IHγ; specialize (IHγ m);
    rewrite Forall_forall in IHγ; specialize (IHγ n);
    rewrite Forall_forall in IHγ; specialize (IHγ (c + k)).
    apply Forall_eq_map in IHγ.
    rewrite -list_fmap_compose IHγ.

    elim: {Δ} IHΔ => [|[l Ψ] Δ IHΨ IHΔ IH] //.

    rewrite Forall_forall in IHΨ; specialize (IHΨ m);
    rewrite Forall_forall in IHΨ; specialize (IHΨ n);
    rewrite Forall_forall in IHΨ; specialize (IHΨ (c + k + l));
    apply Forall_eq_map in IHΨ. rewrite list_fmap_compose in IHΨ.
    cbn. f_equal. rewrite IHΨ.

    inv IH.
Qed.

Lemma bunshift_zero : ∀ (Φ : bouquet) c,
  unshift 0 c <$> Φ = Φ.
Proof.
  intros. rewrite -{2}[Φ]map_id_ext. apply eq_map.
  intros. by apply unshift_zero.
Qed.

Lemma bunshift_shift m n c (Φ : bouquet) :
  unshift (m + n) c <$> (shift n c <$> Φ) = unshift m c <$> Φ.
Proof.
  intros. rewrite -list_fmap_compose. apply eq_map.
  intros. by apply unshift_shift.
Qed.

Lemma gshift_zero : ∀ (γ : garden) c,
  gshift 0 c γ = γ.
Proof.
  intros. rewrite /gshift. case γ => m Φ.
  by rewrite bshift_zero.
Qed.

Lemma pshift_zero : ∀ (Δ : list garden) c,
  gshift 0 c <$> Δ = Δ.
Proof.
  intros. rewrite -{2}[Δ]map_id_ext. apply eq_map.
  intros. rewrite /gshift. by apply gshift_zero.
Qed.

Lemma bshift_add : ∀ (Φ : bouquet) c n m,
  shift (n + m) c <$> Φ = shift n c <$> (shift m c <$> Φ).
Proof.
  intros. rewrite -list_fmap_compose. apply eq_map.
  intros. by apply shift_add.
Qed.

Lemma bshift_comm : ∀ (Φ : bouquet) c n m,
  shift n c <$> (shift m c <$> Φ) = shift m c <$> (shift n c <$> Φ).
Proof.
  intros. do 2 rewrite -list_fmap_compose. apply eq_map.
  intros. by apply shift_comm.
Qed.

(** * Contexts *)

Inductive ctx :=
| Hole
| Planter (Φ : bouquet) (X : ctx) (Φ' : bouquet)
| Pistil (n : nat) (X : ctx) (Δ : list garden)
| Petal (γ : garden) (Δ : list garden) (n : nat) (X : ctx) (Δ' : list garden).

Notation "□" := Hole.

(** ** De Bruijn operations *)

(** *** Compute the number of variables bound in a given context *)

Fixpoint bv (X : ctx) : nat :=
  match X with
  | Hole => 0
  | Planter _ X _ => bv X
  | Pistil n X _ => n + bv X
  | Petal (n ⋅ _) _  m X _ => n + m + bv X
  end.

(** *** Check if a flower is closed *)

(* Fixpoint closed (c : nat) (ϕ : flower) : bool :=
  match ϕ with
  | Atom p args => forallb (tclosed c <$> args)
  | n ⋅ Φ ⫐ Δ =>
      forallb (closed (c + n) <$> Φ) &&
      forallb ((λ '(m ⋅ Ψ), forallb (closed (c + n + m) <$> Ψ)) <$> Δ)
  end.

Definition cflower := { ϕ : flower | closed 0 ϕ }. *)

(** ** Context operations *)

Reserved Notation "X ⋖ Ψ" (at level 15).

Fixpoint fill (Ψ : bouquet) (X : ctx) : bouquet :=
  match X with
  | Hole => Ψ
  | Planter Φ X Φ' => Φ ++ X ⋖ Ψ ++ Φ'
  | Pistil n X Δ => [n ⋅ X ⋖ Ψ ⫐ Δ]
  | Petal γ Δ n X Δ' => [γ ⫐ Δ ++ [n ⋅ X ⋖ Ψ] ++ Δ']
  end
where "X ⋖ Ψ" := (fill Ψ X).

Definition btoc X := X ⋖ [].
Coercion btoc : ctx >-> bouquet.

Reserved Infix "⪡" (at level 15).

Fixpoint comp (X : ctx) (Y : ctx) : ctx :=
  match X with
  | Hole => Y
  | Planter Φ X Φ' => Planter Φ (X ⪡ Y) Φ'
  | Pistil n X Δ => Pistil n (X ⪡ Y) Δ
  | Petal γ Δ n X Δ' => Petal γ Δ n (X ⪡ Y) Δ'
  end
where "X ⪡ Y" := (comp X Y).

Lemma comp_assoc : ∀ X Y Z,
  (X ⪡ Y) ⪡ Z = X ⪡ (Y ⪡ Z).
Proof.
  elim => [|Φ X IHX Φ' |n X IHX Δ |γ Δ n X IHX Δ'] Y Z //=;
  by rewrite IHX.
Qed.

Lemma fill_comp : ∀ X Y Φ,
  X ⋖ (Y ⋖ Φ) = (X ⪡ Y) ⋖ Φ.
Proof.
  elim => [|Φl X IH Φr |n X IH Δ |γ Δ n X IH Δ'] Y Φ //=;
  by rewrite IH.
Qed.

Lemma bv_comp : ∀ X Y,
  bv (X ⪡ Y) = bv X + bv Y.
Proof.
  elim =>//=; intros; rewrite H. lia.
  destruct γ. lia.
Qed.

(** ** Path operations *)

(** A path is simply a list of integers *)

Definition path := list nat.

(** Path operations may fail if the specified path has no denotation in the
    corresponding tree. Thus they live in the Option monad.

    In the setting of a pointing-based proving GUI, this becomes useless because
    the user can only select meaningful paths. *)

(** *** Compute the context and subobject associated to a path *)

Fixpoint bpath p Φ : option (ctx * bouquet) :=
  match p with
  | [] => Some (Hole, Φ)
  | i :: p =>
      lr ← split_at i Φ;
      let '(Φ, Φ') := lr in
      match Φ' with
      | ϕ :: Φ' =>
          XΨ ← fpath p ϕ;
          let '(X, Ψ) := XΨ in
          Some (Planter Φ X Φ', Ψ)
      | _ => None
      end
  end
with fpath p ϕ :=
  match p with
  | [] => Some (Hole, [ϕ])
  | i :: p =>
      match ϕ with
      | γ ⫐ Δ =>
          match i with
          | 0 =>
              let '(n ⋅ Φ) := γ in
              XΨ ← bpath p Φ;
              let '(X, Ψ) := XΨ in
              Some (Pistil n X Δ, Ψ)
          | _ =>
              lr ← split_at (i - 1) Δ;
              let '(Δ, Δ') := lr in
              match Δ' with
              | (n ⋅ Φ) :: Δ' =>
                  XΨ ← bpath p Φ;
                  let '(X, Ψ) := XΨ in
                  Some (Petal γ Δ n X Δ', Ψ)
              | _ => None
              end
          end
      | _ => None
      end
  end.

(** *** Retrieve subobjects *)

Definition bget (p : path) (Φ : bouquet) : option bouquet :=
  _Ψ ← bpath p Φ;
  let '(_, Ψ) := _Ψ in
  Some Ψ.

(** *** Modify subobjects *)

Definition bset (Ψ : bouquet) (p : path) (Φ : bouquet) : option bouquet :=
  X_ ← bpath p Φ;
  let '(X, _) := X_ in
  Some (X ⋖ Ψ).

(** * Rules *)

(** ** Pollination predicate *)

Reserved Notation "Ψ ≺ n 'in' X" (at level 80).

Inductive pollin : bouquet -> nat -> ctx -> Prop :=
| P_self Ψ X n Φ Φ' Δ m Δ' :
  Ψ ≺ (m + bv X) in (Petal (n ⋅ Φ ++ Ψ ++ Φ') Δ m X Δ')
| P_wind_l Ψ X Φ Φ' Φ'' :
  Ψ ≺ (bv X) in (Planter Φ'' X (Φ ++ Ψ ++ Φ'))
| P_wind_r Ψ X Φ Φ' Φ'' :
  Ψ ≺ (bv X) in (Planter (Φ ++ Ψ ++ Φ') X Φ'')
where "Ψ ≺ n 'in' X" := (pollin Ψ n X).

Lemma pollin_comp_out Ψ n Y Z :
  Ψ ≺ n in Y ->
  Ψ ≺ n + (bv Z) in Y ⪡ Z.
Proof.
  move => H. inv H; simpl.
  * epose proof (P_self _ (X ⪡ Z) _ _ _ _ _ _).
    rewrite bv_comp Nat.add_assoc in H.
    eapply H.
  * epose proof (P_wind_l _ (X ⪡ Z)).
    rewrite bv_comp in H.
    eapply H.
  * epose proof (P_wind_r _ (X ⪡ Z)).
    rewrite bv_comp in H.
    eapply H.
Qed.

Lemma bv_comp_pollin_self {Y Ψ k n Φ Δ m X Δ'} :
  let Z := Petal (n ⋅ Φ) Δ m X Δ' in
  Ψ ≺ k in Z ->
  bv (Y ⪡ Z) = bv Y + n + k.
Proof.
  move => Z H. inv H.
  by rewrite bv_comp /=; lia.
Qed.

Lemma bv_comp_pollin_wind {Y Ψ k Φ X Φ'} :
  let Z := Planter Φ X Φ' in
  Ψ ≺ k in Z ->
  bv (Y ⪡ Z) = bv Y + k.
Proof.
  move => Z H. inv H;
  by rewrite bv_comp /=; lia.
Qed.

(** ** Assumptions *)

Definition nassum (n : nat) (Ψ : bouquet) (X : ctx) :=
  ∃ Y Z, unshift n 0 <$> Ψ ≺ n in Z /\ X = Y ⪡ Z.

Lemma nassum_comp_in n Ψ X Y :
  nassum n Ψ Y ->
  nassum n Ψ (X ⪡ Y).
Proof.
  rewrite /nassum.
  move => [Y0 [Z [Hpol Hcomp]]]. subst.
  exists (X ⪡ Y0). exists Z.
  split; [> |by rewrite comp_assoc].
  done.
Qed.

Lemma nassum_comp_out n Ψ X Y :
  nassum n Ψ X ->
  nassum (n + bv Y) (shift (bv Y) 0 <$> Ψ) (X ⪡ Y).
Proof.
  rewrite /nassum.
  move => [Y0 [Z [Hpol Hcomp]]]. subst.
  exists Y0. exists (Z ⪡ Y).
  split; [> |by rewrite comp_assoc].
  rewrite bunshift_shift.
  by apply pollin_comp_out.
Qed.

(** *** Assumptions scattered in a context *)

Definition is_shifted (n : nat) (ϕ : flower) : Prop :=
  exists ψ, ϕ = shift n 0 ψ.

Definition subctx (Φ : bouquet) (X : ctx) : Prop :=
  forall ϕ, ϕ ∈ Φ -> exists n, is_shifted n ϕ /\ nassum n ϕ X.

Infix "⪽" := subctx (at level 70).

Lemma is_shifted_zero ϕ :
  is_shifted 0 ϕ.
Proof.
  exists ϕ. by rewrite shift_zero.
Qed.

Lemma is_shifted_shift_unshift n ϕ :
  is_shifted n ϕ ->
  shift n 0 (unshift n 0 ϕ) = ϕ.
Proof.
  move => H.
  case: H => [B H]. rewrite H.
  by rewrite (unshift_shift _ 0) unshift_zero.
Qed.

Lemma subctx_nil X :
  [] ⪽ X.
Proof.
  red. move => ϕ Hϕ. inv Hϕ.
Qed.

Lemma subctx_singl X (ϕ : flower) :
  ϕ ⪽ X -> ∃ n, is_shifted n ϕ /\ nassum n ϕ X.
Proof.
  move => H. red in H.
  case (H ϕ (elem_of_singl ϕ)) => {H}.
  firstorder.
Qed.

Lemma subctx_comp_out Φ X Y :
  Φ ⪽ X ->
  (shift (bv Y) 0 <$> Φ) ⪽ X ⪡ Y.
Proof.
  rewrite /subctx.
  move => H ϕ Hϕ.
  apply elem_of_map in Hϕ.
  case: Hϕ => [E [HE1 HE2]].
  case (H E HE1) => m [Hshift Hassum].
  exists (m + bv Y). split.
  { red. case: Hshift => F ?; subst.
    exists F. by rewrite -shift_add Nat.add_comm. }
  pose proof (Hass := nassum_comp_out _ _ X Y Hassum).
  rewrite HE2.
  by rewrite /= in Hass.
Qed.

Ltac subctxout H :=
  match goal with
  | |- _ ⪽ _ ⪡ ?Y =>
      let Hsub := fresh "Hsub" in
      pose proof (Hsub := subctx_comp_out _ _ Y H);
      rewrite /= in Hsub;
      repeat rewrite fmap_app in Hsub;
      repeat rewrite bshift_zero in Hsub;
      done
  end.

Lemma subctx_comp_in Φ X Y :
  Φ ⪽ Y ->
  Φ ⪽ X ⪡ Y.
Proof.
  rewrite /subctx.
  move => H ϕ Hϕ.
  case (H ϕ Hϕ) => n [Hs Ha].
  exists n. split; auto.
  by apply nassum_comp_in.
Qed.

Lemma subctx_subset Φ Φ' X :
  Φ ⊆ Φ' -> Φ' ⪽ X -> Φ ⪽ X.
Proof.
  rewrite /subctx.
  move => Hsubset H ϕ Hϕ.
  case (H ϕ (Hsubset ϕ Hϕ)) => n Ha.
  by exists n.
Qed.

Lemma subctx_app Φ Φ' X :
  Φ ⪽ X -> Φ' ⪽ X ->
  (Φ ++ Φ') ⪽ X.
Proof.
  rewrite /subctx.
  move => H H' ϕ Hϕ.
  decompose_elem_of_list.
  * case (H ϕ H0) => n Ha. by exists n.
  * case (H' ϕ H0) => n Ha. by exists n.
Qed.

Global Instance subctx_Permutation :
  Proper ((≡ₚ) ==> (=) ==> (↔)) (subctx).
Proof.
  repeat red. move => Φ Φ' Hperm X Y Heq; subst.
  rewrite /subctx. split; move => H ϕ Hϕ.
  * rewrite -Hperm in Hϕ. by apply H.
  * rewrite Hperm in Hϕ. by apply H.
Qed.

Lemma move_cons_right {A} (l l' : list A) (x : A) :
  l ++ x :: l' ≡ₚ (l ++ l') ++ [x].
Proof.
  by solve_Permutation.
Qed.

Lemma subctx_petal_skip A X γ Δ Δ' :
  [A] ⪽ X ->
  [A] ⪽ Petal γ Δ 0 X Δ'.
Proof.
  move => H.
  by apply (subctx_comp_in _ (Petal γ Δ 0 □ Δ') _ H).
Qed.

Lemma subctx_petal Φ n Φl Φr Δ Δ' :
  Φ ⪽ Petal (n ⋅ Φl ++ Φ ++ Φr) Δ 0 □ Δ'.
Proof.
  move => ϕ Hϕ; move: Hϕ Φl Φr.
  elim => {ϕ Φ} [ϕ Φ |ϕ ψ Φ Hϕ IH] Φl Φr.
  * exists 0. split; [> by apply is_shifted_zero |].
    red. rewrite bunshift_zero.
    exists □. exists (Petal (n ⋅ Φl ++ (ϕ :: Φ) ++ Φr) Δ 0 □ Δ').
    split; auto.
    epose proof (Hp := P_self ϕ □ _ Φl (Φ ++ Φr) _ 0 _).
    eapply Hp.
  * case (IH (Φl ++ [ψ]) Φr) => {IH} m [Hshift Hassum].
    rewrite -app_assoc/= in Hassum.
    exists m. split; auto.
Qed.

Ltac subctxpet Φl Φr Δ Δ' :=
  let Hs := fresh "Hs" in
  epose proof (Hs := subctx_petal _ _ Φl Φr Δ Δ');
  list_simplifier; eapply Hs.

Ltac apply_deriv H X X0 :=
  specialize (H (X ⪡ X0));
  repeat rewrite -fill_comp /= in H;
  etransitivity; [> apply H |].

(** ** Local rules *)

Reserved Infix "⇀" (at level 80).

Inductive step : bouquet -> bouquet -> Prop :=

(** *** Pollination *)

| R_pol (Ψ : bouquet) n X :
  Ψ ≺ n in X ->
  X ⋖ (shift n 0 <$> Ψ) ⇀
  X ⋖ []

| R_copol (Ψ : bouquet) n X :
  Ψ ≺ n in X ->
  X ⋖ [] ⇀
  X ⋖ (shift n 0 <$> Ψ)

(** *** Empty pistil *)

| R_epis_pis m Ψ n Φ Φ' Δ :
  n ⋅ Φ ++ [⫐ [m ⋅ Ψ]] ++ Φ' ⫐ Δ ⇀
  n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ') ⫐ gshift m 0 <$> Δ

| R_epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  γ ⫐ Δ ++ [n ⋅ Φ ++ [⫐ [m ⋅ Ψ]] ++ Φ'] ++ Δ' ⇀
  γ ⫐ Δ ++ [n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ')] ++ Δ'

| R_coepis (Φ : bouquet) :
  Φ ⇀
  ⫐ [0 ⋅ Φ]

(** *** Empty petal *)

| R_pet	γ Δ Δ' :
  γ ⫐ Δ ++ [∅] ++ Δ' ⇀
  []

(** *** Reproduction *)

| R_rep Δ n Φ Φ' Δ' :
  n ⋅ Φ ++ [⫐ Δ] ++ Φ' ⫐ Δ' ⇀
  n ⋅ Φ ++ Φ' ⫐ [0 ⋅ (λ '(m ⋅ Ψ), m ⋅ Ψ ⫐ gshift m 0 <$> Δ') <$> Δ]

(** *** Instantiation *)

| R_ipis i t n Φ Δ :
  0 <= i <= n ->
  S n ⋅ Φ ⫐ Δ ⇀
  [n ⋅ unshift 1 i <$> (subst (i ↦ tshift (S n) 0 t) <$> Φ) ⫐ gunshift 1 i <$> (gsubst (i ↦ tshift (S n) 0 t) <$> Δ); S n ⋅ Φ ⫐ Δ]

| R_ipet i t n Φ γ Δ Δ' :
  0 <= i <= n ->
  γ ⫐ Δ ++ [S n ⋅ Φ] ++ Δ' ⇀
  γ ⫐ Δ ++ [n ⋅ unshift 1 i <$> (subst (i ↦ tshift (S n) 0 t) <$> Φ); S n ⋅ Φ] ++ Δ'

where "Φ ⇀ Ψ" := (step Φ Ψ).

(** ** Contextual closure *)

Reserved Infix "~>" (at level 80).

Inductive cstep : bouquet -> bouquet -> Prop :=

(** *** Congruence *)

| R_ctx (X : ctx) (Φ Ψ : bouquet) :
  Φ ⇀ Ψ ->
  X ⋖ Φ ~> X ⋖ Ψ

where "Φ ~> Ψ" := (cstep Φ Ψ).

(** ** Transitive closure *)

Infix "~>*" := (rtc cstep) (at level 80).

#[export] Hint Extern 1 (rtc _ _ _) => reflexivity : core.

Notation "Φ <~> Ψ" := (Φ ~>* Ψ /\ Ψ ~>* Φ) (at level 80).

Lemma cstep_congr X Φ Ψ :
  Φ ~>* Ψ ->
  X ⋖ Φ ~>* X ⋖ Ψ.
Proof.
  elim {Φ Ψ} => [Φ |Φ Ψ Θ Hstep H IH]; [> reflexivity |].
  apply (rtc_l _ _ (X ⋖ Ψ)); [> |by apply IH].
  elim: Hstep => X0 Φ0 Ψ0 H0.
  rewrite fill_comp fill_comp.
  by apply (R_ctx (X ⪡ X0) Φ0 Ψ0).
Qed.

(** * Variant with the grow rule *)

(** ** Polarized contexts *)

Inductive pctx :=
| PHole
| PPlanter (Φ : bouquet) (P : pctx) (Φ' : bouquet)
| PPistil (n : nat) (N : nctx) (Δ : list garden)
| PPetal (γ : garden) (Δ : list garden) (n : nat) (P : pctx) (Δ' : list garden)
with nctx :=
| NPistil (n : nat) (P : pctx) (Δ : list garden).

Fixpoint pctx_to_ctx (P : pctx) : ctx :=
  match P with
  | PHole => Hole
  | PPlanter Φ P Φ' => Planter Φ (pctx_to_ctx P) Φ'
  | PPistil n N Δ => Pistil n (nctx_to_ctx N) Δ
  | PPetal γ Δ n P Δ' => Petal γ Δ n (pctx_to_ctx P) Δ'
  end
with nctx_to_ctx (N : nctx) : ctx :=
  match N with
  | NPistil n P Δ => Pistil n (pctx_to_ctx P) Δ
  end.

Coercion pctx_to_ctx : pctx >-> ctx.
Coercion nctx_to_ctx : nctx >-> ctx.

Scheme pctx_nctx_ind := Induction for pctx Sort Prop
  with nctx_pctx_ind := Induction for nctx Sort Prop.

Reserved Infix "⪡p" (at level 15).
Reserved Infix "⪡n" (at level 15).

Fixpoint pcomp (P : pctx) (Q : pctx) : pctx :=
  match P with
  | PHole => Q
  | PPlanter Φ P Φ' => PPlanter Φ (P ⪡p Q) Φ'
  | PPistil n N Δ => PPistil n (N ⪡n Q) Δ
  | PPetal γ Δ n P Δ' => PPetal γ Δ n (P ⪡p Q) Δ'
  end
with ncomp (N : nctx) (Q : pctx) : nctx :=
  match N with
  | NPistil n P Δ => NPistil n (P ⪡p Q) Δ
  end
where "P ⪡p Q" := (pcomp P Q)
  and "N ⪡n Q" := (ncomp N Q).

Section PComp.

Let P0 P := forall Q, pctx_to_ctx (P ⪡p Q) = P ⪡ Q.
Let N0 N := forall Q, nctx_to_ctx (N ⪡n Q) = N ⪡ Q.

Lemma pcomp_comp : forall P, P0 P.
Proof.
  apply: (pctx_nctx_ind P0 N0) => //;
  try rewrite /P0/=; try rewrite /N0/=;
  intros; by rewrite H.
Qed.

End PComp.

(** ** Contextual closure + structural rules *)

Reserved Infix "≈>" (at level 80).

Inductive sstep : bouquet -> bouquet -> Prop :=

(** *** Congruence *)

| Rs_ctx (X : ctx) (Φ Ψ : bouquet) :
  Φ ⇀ Ψ ->
  X ⋖ Φ ≈> X ⋖ Ψ

| Rs_grow (P : pctx) (Φ : bouquet) :
  P ⋖ [] ≈> P ⋖ Φ

where "Φ ≈> Ψ" := (sstep Φ Ψ).

(** ** Transitive closure *)

Infix "≈>*" := (rtc sstep) (at level 80).

Notation "Φ <≈> Ψ" := (Φ ≈>* Ψ /\ Ψ ≈>* Φ) (at level 80).

Lemma sstep_congr (P : pctx) Φ Ψ :
  Φ ≈>* Ψ ->
  P ⋖ Φ ≈>* P ⋖ Ψ.
Proof.
  elim {Φ Ψ} => [Φ |Φ Ψ Θ Hstep H IH]; [> reflexivity |].
  apply (rtc_l _ _ (P ⋖ Ψ)); [> |by apply IH].
  elim: Hstep => {Φ} [X0 Φ0 Ψ0 |P0 Φ].
  * rewrite fill_comp fill_comp.
    by apply (Rs_ctx (P ⪡ X0) Φ0 Ψ0).
  * rewrite fill_comp fill_comp -pcomp_comp.
    by apply (Rs_grow (P ⪡p P0) Φ).
Qed.

(** * Basic proof search *)

Ltac sub_at p :=
  match goal with
  | |- ?Φ ~>* _ => eval cbn in (bget p Φ)
  end.

Ltac rstep Ψ :=
  apply (rtc_l cstep _ Ψ).

Ltac rstepm p Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let Φ' := eval cbn in (bset Ψ p Φ) in
      match Φ' with
      | None => idtac
      | Some ?Φ' => rstep Φ'; list_simplifier
      end
  end.

Ltac rstepm_app p i Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      match XΦ0 with
      | Some (_, ?Φl ++ ?Φr) =>
          match i with
          | 0 => rstepm p (Ψ ++ Φr)
          | 1 => rstepm p (Φl ++ Ψ)
          end
      | Some (_, ?ϕ :: ?Φr) =>
          match i with
          | 0 => rstepm p (Ψ ++ Φr)
          | 1 => rstepm p (ϕ :: Ψ)
          end
      end
  end.

Ltac rtransm p Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let Φ' := eval cbn in (bset Ψ p Φ) in
      match Φ' with
      | Some ?Φ' => apply (rtc_transitive Φ Φ'); list_simplifier
      end
  end.

Ltac rctx X Φ Ψ :=
  apply (R_ctx X Φ Ψ).

Ltac rctxm p :=
  match goal with
  | |- ?Φ ~> ?Ψ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      let _Ψ0 := eval cbn in (bpath p Ψ) in
      match XΦ0 with
      | Some (?X, ?Φ0) =>
          match _Ψ0 with
          | Some (_, ?Ψ0) =>
              rctx X Φ0 Ψ0
          end
      end
  end.

Ltac rctxt p :=
  match goal with
  | |- ?Φ ~>* ?Ψ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      let _Ψ0 := eval cbn in (bpath p Ψ) in
      match XΦ0 with
      | Some (?X, ?Φ0) =>
          match _Ψ0 with
          | Some (_, ?Ψ0) =>
              apply (cstep_congr X Φ0 Ψ0)
          end
      end
  end.

Ltac rctxt_app p i :=
  match goal with
  | |- ?Φ ~>* ?Ψ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      let _Ψ0 := eval cbn in (bpath p Ψ) in

      match XΦ0 with
      | Some (?X, ?Φ0) =>
          match _Ψ0 with
          | Some (_, ?Ψ0) =>
              let Φ0lr :=
                match Φ0 with
                | ?Φ0l ++ ?Φ0r => constr:((Φ0l, Φ0r))
                | ?ϕ0l :: ?Φ0r => constr:(([ϕ0l], Φ0r))
                end in
              let Ψ0lr :=
                match Ψ0 with
                | ?Ψ0l ++ ?Ψ0r => constr:((Ψ0l, Ψ0r))
                | ?Ψ0l :: ?Ψ0r => constr:(([Ψ0l], Ψ0r))
                end in    
              match Φ0lr with
              | (?Φ0l, ?Φ0r) =>
                  match Ψ0lr with
                  | (?Ψ0l, ?Ψ0r) =>
                      let XΦΨ0 :=
                        match i with               
                        | 0 => constr:((Planter [] □ Φ0r, Φ0l, Ψ0l))
                        | 1 => constr:((Planter Φ0l □ [], Φ0r, Ψ0r))
                        end in
                      match XΦΨ0 with
                      | (?X0, ?Φ0, ?Ψ0) =>
                          let Y := eval cbn in (X ⪡ X0) in
                          let H := fresh "H" in
                          pose proof (H := cstep_congr Y Φ0 Ψ0); list_simplifier;
                          apply H; clear H
                      end
                  end
              end
          end
      end
  end.

Ltac rctxm_app p i :=
  match goal with
  | |- ?Φ ~> ?Ψ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      let _Ψ0 := eval cbn in (bpath p Ψ) in
      match XΦ0 with
      | Some (?X, ?Φl ++ ?Φr) =>
          let Y :=
            match i with
            | 0 => let X' := eval cbn in (X ⪡ (Planter [] □ Φr)) in X'
            | 1 => let X' := eval cbn in (X ⪡ (Planter Φl □ [])) in X'
            end in
          let Φ0 :=
            match i with
            | 0 => Φl
            | 1 => Φr
            end in
          let Ψ0 :=
            match i with 
            | 0 =>
                match _Ψ0 with
                | Some (_, ?Ψl ++ _) => Ψl
                | Some (_, ?ψ :: _) => constr:([ψ])
                end
            | 1 =>
                match _Ψ0 with
                | Some (_, _ ++ ?Ψr) => Ψr
                | Some (_, _ :: ?Ψr) => Ψr
                end
            end in
          rctx Y Φ0 Ψ0
      end
  end.

Ltac rcstepm p Ψ :=
  match goal with
  | |- ?Φ ~>* _ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      match XΦ0 with
      | Some (?X, ?Φ0) =>
          rstepm p Ψ; [> rctx X Φ0 Ψ |]
      end
  end.

Ltac rctransm p Ψ0 :=
  rtransm p Ψ0; [> rctxt p |].

Ltac rctxmt p Ψ0 :=
  match goal with
  | |- ?Φ ~>* _ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      match XΦ0 with
      | Some (?X, ?Φ0) =>
          let H := fresh "H" in
          pose proof (H := cstep_congr X Φ0 Ψ0); list_simplifier;
          apply H; clear H
      end
  end.

Ltac rectxmt p :=
  rewrite /ftob;
  match goal with
  | |- ?Φ ~>* _ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      match XΦ0 with
      | Some (?X, ?Φ0) =>
          let H := fresh "H" in
          etransitivity; [>
            epose proof (H := cstep_congr X Φ0 _); list_simplifier;
            eapply H; clear H
          |]
      end
  end.

Ltac rctxmH p H :=
  match type of H with
  | _ ~>* ?Ψ0 =>
      rtransm p Ψ0; [> rctxmt p Ψ0; exact H |]
  end.

Ltac rself :=
  match goal with
  | |- ?Φ ~> ?Ψ =>
      rctx □ Φ Ψ
  end.

Ltac rspol p Φl Φr :=
  match goal with
  | |- ftob ?ϕ ⇀ _ =>
      let XΨ := eval cbn in (fpath p ϕ) in
      match XΨ with
      | Some (?X, ?Ψ) =>
          let H := fresh "H" in
          pose proof (H := R_pol Ψ 0 X);
          rewrite bshift_zero /= in H;
          apply H;
          match X with
          | Petal _ _ _ ?Y _ =>
              let H := fresh "H" in
              epose proof (H := P_self _ Y 0 Φl Φr _ 0 _);
              list_simplifier; apply H
          end
      end
  end.

Ltac rspolm p Φl Φr :=
  rstepm (0 :: p) (@nil flower); [>
    rself;
    rspol p Φl Φr
  |].

(* Ltac rscopol Y n Φl Ψ Φr :=
  let H := fresh "H" in
  pose proof (H := R_co_pol Ψ n Y); list_simplifier;
  repeat rewrite bshift_zero/= in H;
  repeat rewrite bshift_zero/=;
  apply H;
  match Y with
  | Petal _ _ _ ?Y0 _ =>
      let H := fresh "H" in
      epose proof (H := P_self _ Y0 _ Φl Φr _ 0 _); list_simplifier;
      repeat rewrite bshift_zero/= in H;
      eapply H
  end.

Ltac rwcopol Y Φl Ψ Φr :=
  let H := fresh "H" in
  pose proof (H := R_co_pol Ψ 0 Y); list_simplifier;
  rewrite bshift_zero /= in H;
  apply H;
  match Y with
  | Planter (_ ++ _ ++ _) ?Y0 _ =>
      let H := fresh "H" in
      epose proof (H := P_wind_r _ Y0 Φl Φr _); list_simplifier;
      apply H
  | Planter _ ?Y0 (_ ++ _ ++ _) =>
      let H := fresh "H" in
      epose proof (H := P_wind_l _ Y0 Φl Φr _); list_simplifier;
      apply H
  end.

Ltac rscopolm p i n Φl Ψ Φr :=
  rewrite /ftob;
  match goal with
  | |- [?ϕ] ~>* _ =>
      let XΦ := eval cbn in (fpath p ϕ) in
      match XΦ with
      | Some (?X, ?Φ) =>
          let X0 :=
            match i with
            | 0 => constr:(Planter [] □ Φ)
            | 1 => constr:(Planter Φ □ [])
            end in
          let Y := eval cbn in (X ⪡ X0) in
          let Ψ' := eval cbn in (X0 ⋖ (shift n 0 <$> Ψ)) in
          rstepm (0 :: p) Ψ'; [>
            rself;
            rscopol Y n Φl Ψ Φr
          | repeat rewrite bshift_zero/=]
      end
  end.

Ltac rwcopolm p i Φl Ψ Φr :=
  match goal with
  | |- ?Φ1 ++ ?Φ ++ ?Φ2 ~>* _ =>
      let XΦ0 := eval cbn in (bpath p Φ) in
      match XΦ0 with
      | Some (?X, ?Φ0) =>
          let X0 :=
            match i with
            | 0 => constr:(Planter [] □ Φ0)
            | 1 => constr:(Planter Φ0 □ [])
            end in
          let Y := eval cbn in (X ⪡ X0) in
          let Ψ' := eval cbn in (X0 ⋖ Ψ) in
          let Φ' := eval cbn in (bset Ψ' p Φ) in
          match Φ' with
          | Some ?Φ' =>
              rstep (Φ1 ++ Φ' ++ Φ2); [>
                rself;
                rwcopol (Planter Φ1 Y Φ2) Φl Ψ Φr
              |]
          end
      end
  end.

Ltac rcoepispet n m Φl Φr Δl Δr :=
  rewrite /ftob;
  match goal with
  | |- [?γ ⫐ _] ~>* _ =>
      let H := fresh "H" in
      epose proof (H := R_co_epis_pet m _ n Φl Φr γ Δl Δr);
      list_simplifier;
      repeat rewrite bshift_zero in H;
      etransitivity; [> eapply rtc_once; rself; eapply H |];
      clear H
  end. *)

Ltac repispet n m Φl Φr Δl Δr :=
  rewrite /ftob;
  match goal with
  | |- [?γ ⫐ _] ~>* _ =>
      let H := fresh "H" in
      epose proof (H := R_epis_pet m _ n Φl Φr γ Δl Δr);
      list_simplifier;
      repeat rewrite bshift_zero in H;
      etransitivity; [> eapply rtc_once; rself; eapply H |];
      clear H
  end.

(* Ltac rcoepispis n m Φl Φr :=
  rewrite /ftob;
  match goal with
  | |- [_ ⫐ ?Δ] ~>* _ =>
      let H := fresh "H" in
      epose proof (H := R_co_epis_pis m _ n Φl Φr Δ);
      list_simplifier;
      repeat rewrite bshift_zero in H;
      repeat rewrite pshift_zero in H;
      etransitivity; [> eapply rtc_once; rself; eapply H |];
      clear H
  end. *)

Ltac repispis n m Φl Φr :=
  rewrite /ftob;
  match goal with
  | |- [_ ⫐ ?Δ] ~>* _ =>
      let H := fresh "H" in
      epose proof (H := R_epis_pis m _ n Φl Φr Δ);
      list_simplifier;
      repeat rewrite bshift_zero in H;
      repeat rewrite pshift_zero in H;
      etransitivity; [> eapply rtc_once; rself; eapply H |];
      clear H
  end.

Ltac rrep Φl Φr :=
  match goal with
  | |- [?n ⋅ _ ⫐ ?Δ] ~>* _ =>
      let H := fresh "H" in
      epose proof (H := R_rep _ n Φl Φr Δ);
      list_simplifier;
      etransitivity; [> eapply rtc_once; rself; eapply H |];
      clear H
  end.

Ltac rpet Δ Δ' :=
  apply (R_pet _ Δ Δ').

Ltac rpetm p Δ Δ' :=
  rcstepm p (@nil flower); [> rpet Δ Δ' |].

Ltac bypet Δ Δ' :=
  repeat rewrite fill_comp; eapply cstep_congr;
  rpetm (@nil nat) Δ Δ';
  reflexivity.

Ltac estep := etransitivity; [> eapply rtc_once |].

(** * Useful derivable rules *)

Lemma subcopol : ∀ Φ X,
  Φ ⪽ X ->
  X ⋖ [] ~>* X ⋖ Φ.
Proof.
  elim => [|ϕ Φ IH] X H //.
  etransitivity. apply IH.
  apply (subctx_subset _ (ϕ :: Φ)); auto. by right.

  apply (subctx_subset ϕ) in H.
  2: { red. red. intros. rewrite cons_app. solve_elem_of_list. }
  case (subctx_singl _ _ H) => {H} n [Hshift [Y [Z [Hpol ?]]]]; subst.
  rewrite -fill_comp/=.
  
  estep. apply R_ctx.
  set X0 := Planter [] □ Φ.
  epose proof (Hp := R_copol (unshift n 0 ϕ) n (Z ⪡ X0)).
  repeat rewrite -fill_comp/= in Hp. eapply Hp.
  rewrite fmap_singl in Hpol. rewrite /ftob.
  epose proof (Hp' := pollin_comp_out _ _ _ X0).
  rewrite /= Nat.add_0_r in Hp'. by eapply Hp'.

  rewrite is_shifted_shift_unshift. done.
  by rewrite -fill_comp.
Qed.

Lemma subcopolepis X Φ Ψ :
  Φ ⪽ X ->
  X ⋖ Ψ ~>* X ⋖ [0 ⋅ Φ ⫐ [0 ⋅ Ψ]]. 
Proof.
  move => H.
  estep. apply R_ctx. apply R_coepis.
  set Y := Pistil 0 □ [0 ⋅ Ψ].
  epose proof (Hp := subcopol _ (X ⪡ Y)).
  repeat rewrite -fill_comp/= in Hp. eapply Hp.
  subctxout H.
Qed.

Lemma contraction Φ :
  Φ ~>* Φ ++ Φ.
Proof.
  pose proof (Hp := R_copol Φ 0 (Planter Φ □ [])).
  list_simplifier. rewrite bshift_zero in Hp.
  apply rtc_once. rself. apply Hp.
  epose proof (Hpol := P_wind_r Φ □ [] [] []).
  by list_simplifier.
Qed.

Lemma cocontraction Φ :
  Φ ++ Φ ~>* Φ.
Proof.
  pose proof (Hp := R_pol Φ 0 (Planter Φ □ [])).
  list_simplifier. rewrite bshift_zero in Hp.
  apply rtc_once. rself. apply Hp.
  epose proof (Hpol := P_wind_r Φ □ [] [] []).
  by list_simplifier.
Qed.

Lemma nipis : ∀ n Φ Δ σ,
  n ⋅ Φ ⫐ Δ ~>*
  list_init (S n) (λ i, i ⋅ bsubst (σ/(n-i)) Φ ⫐ gsubst (σ/(n-i)) <$> Δ).
Proof.
  elim => [|n IH] Φ Δ σ /=.
  * rewrite on_range_zero bsubst_id gsubst_id map_id_ext /=.
    reflexivity.
  * estep. rself.
    apply (R_ipis 0 (σ 0)). by lia.
    assert (H : n - n = 0) by lia; rewrite H; clear H.
    rewrite on_range_zero bsubst_id gsubst_id map_id_ext /=.
    simpl in IH.
    etransitivity.
    set ϕ := (x in [x; _]).
    epose proof (cstep_congr (Planter [] □ (S n ⋅ Φ ⫐ Δ)) ϕ _). simpl in H.
    apply H. eapply (IH _ _ σ).
Admitted.

(** * Provability *)

Definition prov Φ := Φ ~>* [].
Definition eqprov Φ Ψ := prov Φ <-> prov Ψ.

Infix "≡" := eqprov.

Definition sprov Φ := Φ ≈>* [].
Definition eqsprov Φ Ψ := sprov Φ <-> sprov Ψ.

Infix "≣" := eqsprov (at level 70).

#[export] Instance equiv_eqprov : Equivalence eqprov.
Proof.
  econs; red; rewrite /eqprov; intros.
  by reflexivity.
  by symmetry.
  etransitivity; eauto.
Qed.

Lemma cstep_sstep Φ Ψ :
  Φ ~>* Ψ -> Φ ≈>* Ψ.
Proof.
  elim => [Φ1 |Φ1 Φ2 Φ3 Hstep _ IH]. reflexivity.
  apply (rtc_l _ _ Φ2).
  { case: Hstep => {Φ Ψ} [X Φ Ψ Hstep]. by apply Rs_ctx. }
  exact IH.
Qed.

Definition deriv (Φ Ψ : bouquet) := ∀ X, Φ ⪽ X -> X ⋖ Ψ ~>* X ⋖ [].
Definition sderiv (Φ Ψ : bouquet) := ∀ X, Φ ⪽ X -> X ⋖ Ψ ≈>* X ⋖ [].

Infix "⊢" := deriv (at level 70).
Infix "⊢s" := sderiv (at level 70).

Lemma subpol : ∀ Φ X,
  Φ ⪽ X ->
  X ⋖ Φ ~>* X ⋖ [].
Proof.
  elim => [|ϕ Φ IH] X H //.

  epose proof (Hϕ := subctx_subset ϕ _ _ _ H). Unshelve. 2: { set_solver. }
  epose proof (HΦ := subctx_subset Φ _ _ _ H). Unshelve. 2: { set_solver. }

  case (subctx_singl _ _ Hϕ) => {H} n [Hshift [Y [Z [Hpol ?]]]]; subst.
  rewrite -fill_comp/=.
  
  estep. apply R_ctx.
  set X0 := Planter [] □ Φ.
  epose proof (Hp := R_pol (unshift n 0 ϕ) n (Z ⪡ X0)).
  repeat rewrite -fill_comp/= is_shifted_shift_unshift in Hp; auto. apply Hp.
  rewrite fmap_singl in Hpol. rewrite /ftob.
  epose proof (Hp' := pollin_comp_out _ _ _ X0).
  rewrite /= Nat.add_0_r in Hp'. by eapply Hp'.

  repeat rewrite -fill_comp/= fill_comp.
  by apply IH.
Qed.

#[export] Instance deriv_refl : Reflexive deriv.
Proof.
  intros ???. by apply subpol.
Qed.

Lemma deriv_sderiv Φ Ψ :
  Φ ⊢ Ψ -> Φ ⊢s Ψ.
Proof.
  intros; red; intros.
  by apply cstep_sstep.
Qed.

Lemma prov_deriv Φ :
  prov Φ <-> [] ⊢ Φ.
Proof.
  rewrite /prov/deriv.
  split; move => H.
  * move => X HX. by apply cstep_congr.
  * apply (H □). red. intros ? Hϕ. inv Hϕ.
Qed.

Definition eqderiv Φ Ψ := (Φ ⊢ Ψ) /\ (Ψ ⊢ Φ).
Definition eqsderiv Φ Ψ := (Φ ⊢s Ψ) /\ (Ψ ⊢s Φ).

Infix "⊣⊢" := eqderiv (at level 70).
Infix "⊣s⊢" := eqsderiv (at level 70).

Lemma cut Φ Ψ :
  Ψ ≈>* Φ ++ [0 ⋅ Φ ⫐ [0 ⋅ Ψ]].
Proof.
  estep.
  apply (Rs_grow (PPlanter [] PHole Ψ) Φ). cbn.
  estep.
  epose proof (Hc := Rs_ctx (PPlanter Φ PHole []) Ψ _).
  list_simplifier. eapply Hc. eapply R_coepis.
  estep.
  epose proof (Hc := Rs_ctx □ _ _).
  list_simplifier. eapply Hc.

  pose proof (Hp := R_copol Φ 0 (Planter Φ (Pistil 0 □ [0 ⋅ Ψ]) [])).
  list_simplifier. apply Hp.
  epose proof (Hpol := P_wind_r Φ (Pistil _ □ _) [] [] []).
  list_simplifier. rewrite Nat.add_0_r in Hpol. eapply Hpol.
  rewrite bshift_zero. reflexivity.
Qed.

Lemma eqsderiv_eqsprov Φ Ψ :
  Φ ⊣s⊢ Ψ -> Φ ≣ Ψ.
Proof.
  move => [H1 H2].
  repeat red. rewrite /sprov. split; move => H.
  repeat red in H1, H2.
  * etransitivity. eapply (cut Φ).
    etransitivity.
    epose proof (Hc := sstep_congr (PPlanter Φ PHole []) [0 ⋅ Φ ⫐ [0 ⋅ Ψ]] _).
    list_simplifier. eapply Hc.
    admit. admit.
  * etransitivity. eapply (cut Ψ).
    etransitivity.
    epose proof (Hc := sstep_congr (PPlanter Ψ PHole []) [0 ⋅ Ψ ⫐ [0 ⋅ Φ]] _).
    list_simplifier. eapply Hc.
    admit. admit.
Admitted.

(* Global Instance sderiv_po : PreOrder sderiv.
Proof.
  econs; red.
  * move => Φ. apply deriv_sderiv. red.
    pose proof (Hpol := R_pol Φ 0 (Petal (0 ⋅ Φ) [] 0 □ [])).
    rewrite /= bshift_zero in Hpol. red.
    estep. rself. eapply Hpol.
    pose proof (Hp := P_self Φ □ 0 [] [] [] 0 []); list_simplifier.
    exact Hp.
    rpetm (@nil nat) (@nil garden) (@nil garden).
    reflexivity.
  * rewrite /sderiv. move => Φ1 Φ2 Φ3 H1 H2.
    admit.
Admitted. *)

(** ** Deduction *)

Theorem deduction Φ Ψ :
  Φ ⊢ Ψ <-> [] ⊢ 0 ⋅ Φ ⫐ [0 ⋅ Ψ].
Proof.
  split; move => H X HX.
  * set Y := Petal (0 ⋅ Φ) [] 0 □ [].
    apply_deriv H X Y.
    { apply subctx_comp_in.
      subctxpet (@nil flower) (@nil flower) (@nil garden) (@nil garden). }
    bypet (@nil garden) (@nil garden).
  * specialize (H X (subctx_nil X)).
    etransitivity; [> |eapply H].
    by apply subcopolepis.
Qed.

(** * Weakening *)

(* Theorem weakening Φ Φ' Ψ :
  Φ ⊆ Φ' -> Φ ⊢ Ψ -> Φ' ⊢ Ψ.
Admitted. *)