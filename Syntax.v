Require Import stdpp.list stdpp.relations.
Require Import ssreflect.
Require Import String.

Require Import Flowers.Terms Flowers.Utils.

(** * Flowers *)

Inductive flower :=
| Atom (p : name) (args : list term)
| Flower (γ : nat * list flower) (Δ : list (nat * list flower)).

Definition garden : Type := nat * list flower.
Definition bouquet := list flower.

Definition ftog : flower -> garden := λ ϕ, (0, [ϕ]).
Coercion ftog : flower >-> garden.

Definition ftob : flower -> bouquet := λ ϕ, [ϕ].
Coercion ftob : flower >-> bouquet.

Definition btog : bouquet -> garden := λ Φ, (0, Φ).
Coercion btog : bouquet >-> garden.

Notation "∅" := (0, nil).
Notation "n ⋅ Φ" := (n, Φ) (format "n  ⋅  Φ", at level 63).

Notation "γ ⊢ Δ" := (Flower γ Δ) (at level 65).
Notation "γ ⊢" := (Flower γ nil) (at level 65).
Notation "⊢ Δ" := (Flower ∅ Δ) (at level 65).

(** ** Induction principles *)

Definition flower_induction_full :
  ∀ (P : flower -> Prop)
    (Pt : term -> Prop),
  let Pγ '(n ⋅ Φ) := Forall P Φ in
  ∀ (IHt : ∀ (t : term), Pt t)
    (IHatom : ∀ p args, Forall Pt args -> P (Atom p args))
    (IHflower : ∀ (γ : garden) (Δ : list garden),
      Pγ γ -> Forall Pγ Δ -> P (γ ⊢ Δ))
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
      Pγ γ -> Forall Pγ Δ -> P (γ ⊢ Δ)),
  ∀ (ϕ : flower), P ϕ.
Proof.
  intros. eapply flower_induction_full; eauto.
  exact (λ _, I).
Qed.

(** ** Operations on De Bruijn indices *)

Fixpoint shift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tshift n c <$> args)
  | m ⋅ Φ ⊢ Δ =>
      m ⋅ shift n (c + m) <$> Φ ⊢
        ((λ '(k ⋅ Ψ), k ⋅ shift n (c + m + k) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gshift n c '(m ⋅ Φ) : garden :=
  m ⋅ shift n (c + m) <$> Φ.

Fixpoint unshift (n : nat) (c : nat) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tunshift n c <$> args)
  | m ⋅ Φ ⊢ Δ =>
      m ⋅ unshift n (c + m) <$> Φ ⊢
        ((λ '(k ⋅ Ψ), k ⋅ unshift n (c + m + k) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gunshift n c '(m ⋅ Φ) : garden :=
  m ⋅ unshift n (c + m) <$> Φ.

Fixpoint subst (n : nat) (t : term) (ϕ : flower) : flower :=
  match ϕ with
  | Atom p args => Atom p (tsubst n t <$> args)
  | m ⋅ Φ ⊢ Δ =>
      m ⋅ subst (n + m) (tshift m 0 t) <$> Φ ⊢
        ((λ '(k ⋅ Ψ), k ⋅ subst (n + m + k) (tshift (m + k) 0 t) <$> Ψ) : garden -> garden) <$> Δ
  end.

Definition gsubst n t '(m ⋅ Φ) : garden :=
  m ⋅ subst (n + m) (tshift m 0 t) <$> Φ.

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

Lemma bunshift_zero : ∀ (Φ : bouquet) c,
  unshift 0 c <$> Φ = Φ.
Proof.
  intros. rewrite -{2}[Φ]map_id_ext. apply eq_map.
  (* intros. by apply unshift_zero. *)
(* Qed. *)
Admitted.

Lemma bunshift_add : ∀ (Φ : bouquet) n m c,
  unshift (n + m) c <$> Φ = unshift n c <$> (unshift m c <$> Φ).
Proof.
Admitted.

Lemma bunshift_shift n c (Φ : bouquet) :
  unshift n c <$> (shift n c <$> Φ) = Φ.
Admitted.

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

(** ** Juxtaposition of gardens *)

(* Definition juxt '(n ⋅ Φ) '(m ⋅ Ψ) :=
  (n + m) ⋅ (shift m 0 <$> Φ) ++ (shift n m <$> Ψ).

Definition Juxt : list garden -> garden :=
  foldr juxt ∅.

Infix "∪" := juxt.
Notation "⋃ Δ" := (Juxt Δ).

Lemma juxt_empty γ :
  ∅ ∪ γ = γ.
Proof.
  case γ => n Φ //=.
  pose proof (eq_map (shift 0 n) id Φ (λ ϕ, shift_zero ϕ n)).
  by rewrite H list_fmap_id.
Qed. *)

Definition juxt (Φ Ψ : bouquet) :=
  Φ ++ Ψ.

Definition Juxt : list bouquet -> bouquet :=
  foldr app [].

Infix "∪" := juxt.
Notation "⋃ Φs" := (Juxt Φs).

Lemma Juxt_Bind : ∀ (Φs : list bouquet),
  ⋃ Φs = Φ ← Φs; Φ.
Proof.
  reflexivity.
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

(** ** Context operations *)

Reserved Notation "X ⋖ Ψ" (at level 15).

Fixpoint fill (Ψ : bouquet) (X : ctx) : bouquet :=
  match X with
  | Hole => Ψ
  | Planter Φ X Φ' => Φ ++ X ⋖ Ψ ++ Φ'
  | Pistil n X Δ => [n ⋅ X ⋖ Ψ ⊢ Δ]
  | Petal γ Δ n X Δ' => [γ ⊢ Δ ++ [n ⋅ X ⋖ Ψ] ++ Δ']
  end
where "X ⋖ Ψ" := (fill Ψ X).

(* Capture-avoiding *)
Definition fill_ca Ψ X :=
  X ⋖ (shift (bv X) 0 <$> Ψ).

Notation "X ⋖! Ψ" := (fill_ca Ψ X) (at level 15).

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
      | γ ⊢ Δ =>
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

Open Scope string_scope.
Compute λ ϕ : flower, bset [] [1] [∅ ⊢ [(0 ⋅ [ϕ; Atom "a" []]); (4 ⋅ [Atom "c" []])]].
Close Scope string_scope.

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

Lemma nassum_comp_out n Ψ X Y :
  nassum n Ψ X ->
  nassum (n + bv Y) (shift (bv Y) 0 <$> Ψ) (X ⪡ Y).
Proof.
  rewrite /nassum.
  move => [Y0 [Z [Hpol Hcomp]]]. subst.
  exists Y0. exists (Z ⪡ Y).
  split; [> |by rewrite comp_assoc].
  rewrite bunshift_add bunshift_shift.
  by apply pollin_comp_out.
Qed.

Definition assum (Ψ : bouquet) (X : ctx) :=
  ∃ n Y Z, unshift n 0 <$> Ψ ≺ n in Z /\ X = Y ⪡ Z.
(* Notation "Ψ ∈ X" := (assum Ψ X). *)

Reserved Notation "Ψ ∈! X" (at level 30).

(* Capture-avoiding *)
Inductive assum_ca Ψ : ctx -> Prop :=
| A_self X k n Φ Δ m Z Δ' :
  let Y := Petal (n ⋅ Φ) Δ m Z Δ' in
  shift (bv X + n) 0 <$> Ψ ≺ k in Y ->
  Ψ ∈! X ⪡ Y
| A_wind X k Φ Z Φ' :
  let Y := Planter Φ Z Φ' in
  shift (bv X) 0 <$> Ψ ≺ k in Y ->
  Ψ ∈! X ⪡ Y
where "Ψ ∈! X" := (assum_ca Ψ X).

Lemma assum_ca_comp_out Ψ X Y :
  Ψ ∈! X ->
  Ψ ∈! X ⪡ Y.
Proof.
  elim => {X}; intros; rewrite comp_assoc.
  * apply (A_self _ _ (k + bv Y) _ _ _ _ (Z ⪡ Y)).
    inve H. rewrite -Nat.add_assoc -bv_comp. econs.
  * apply (A_wind _ _ (k + bv Y) _ (Z ⪡ Y)).
    inve H; rewrite -bv_comp; econs.
Qed.

Lemma assum_ca_comp_in Ψ X Y :
  (shift (bv X) 0 <$> Ψ) ∈! Y ->
  Ψ ∈! X ⪡ Y.
Proof.
  elim => {Y}; intros; rewrite -comp_assoc.
  * apply (A_self _ (X ⪡ X0) k).
    inve H. rewrite -bshift_add bv_comp -Nat.add_assoc Nat.add_comm. econs.
  * apply (A_wind _ (X ⪡ X0) k).
    inve H; rewrite -bshift_add bv_comp Nat.add_comm; econs.
Qed.

(** ** Local rules *)

Reserved Infix "⇀" (at level 80).

Inductive step : bouquet -> bouquet -> Prop :=

(** *** Pollination *)

| R_pol (Ψ : bouquet) n X :
  Ψ ≺ n in X ->
  X ⋖ (shift n 0 <$> Ψ) ⇀
  X ⋖ []

(** *** Empty pistil *)

| R_epis_pis m Ψ n Φ Φ' Δ :
  n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ' ⊢ Δ ⇀
  n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ') ⊢ gshift m 0 <$> Δ

| R_epis_pet m Ψ n Φ Φ' γ Δ Δ' :
  γ ⊢ Δ ++ [n ⋅ Φ ++ [⊢ [m ⋅ Ψ]] ++ Φ'] ++ Δ' ⇀
  γ ⊢ Δ ++ [n + m ⋅ (shift m 0 <$> Φ) ++ Ψ ++ (shift m 0 <$> Φ')] ++ Δ'

(** *** Co-pollination + co-empty pistil *)

| R_copolepis (Ψ Φ : bouquet) n X :
  Ψ ≺ n in X ->
  X ⋖ Φ ⇀
  X ⋖ (0 ⋅ shift n 0 <$> Ψ ⊢ [0 ⋅ Φ])

(** *** Empty petal *)

| R_pet	γ Δ Δ' :
  γ ⊢ Δ ++ [∅] ++ Δ' ⇀
  []

(** *** Reproduction *)

| R_rep Δ n Φ Φ' Δ' :
  n ⋅ Φ ++ [⊢ Δ] ++ Φ' ⊢ Δ' ⇀
  n ⋅ Φ ++ Φ' ⊢ [0 ⋅ (λ '(m ⋅ Ψ), m ⋅ Ψ ⊢ gshift m 0 <$> Δ') <$> Δ]

(** *** Instantiation *)

| R_ipis i t n Φ Δ :
  0 <= i <= n ->
  S n ⋅ Φ ⊢ Δ ⇀
  [n ⋅ unshift 1 i <$> (subst i (tshift (S n) 0 t) <$> Φ) ⊢ gunshift 1 i <$> (gsubst i (tshift (S n) 0 t) <$> Δ); S n ⋅ Φ ⊢ Δ]

| R_ipet i t n Φ γ Δ Δ' :
  0 <= i <= n ->
  γ ⊢ Δ ++ [S n ⋅ Φ] ++ Δ' ⇀
  γ ⊢ Δ ++ [n ⋅ unshift 1 i <$> (subst i (tshift (S n) 0 t) <$> Φ); S n ⋅ Φ] ++ Δ'

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

(** * Basic proof search *)

(* TODO: rewrite all tactics *)

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
  | |- [?γ ⊢ _] ~>* _ =>
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
  | |- [?γ ⊢ _] ~>* _ =>
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
  | |- [_ ⊢ ?Δ] ~>* _ =>
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
  | |- [_ ⊢ ?Δ] ~>* _ =>
      let H := fresh "H" in
      epose proof (H := R_epis_pis m _ n Φl Φr Δ);
      list_simplifier;
      repeat rewrite bshift_zero in H;
      repeat rewrite pshift_zero in H;
      etransitivity; [> eapply rtc_once; rself; eapply H |];
      clear H
  end.

Ltac rrep :=
  eapply rtc_l; [>
    rself;
    match goal with
    | |- [?n ⋅ ?Φl ++ [⊢ ?Ψs] ++ ?Φr ⊢ ?Δ] ⇀ _ =>
        let H := fresh "H" in
        pose proof (H := R_rep Ψs n Φl Φr Δ);
        list_simplifier;
        eapply H
    end
  |].

Ltac rpet Δ Δ' :=
  apply (R_pet _ Δ Δ').

Ltac rpetm p Δ Δ' :=
  rcstepm p (@nil flower); [> rpet Δ Δ' |].

Open Scope string_scope.

Example deriv_contraction :
  [Atom "a" []; Atom "b" []] ~>* [Atom "a" []; Atom "b" []; Atom "b" []].
Proof.
  apply rtc_once.
Admitted.