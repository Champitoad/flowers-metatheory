Require Import stdpp.list.
Require Import ssreflect.

Require Import Flowers.Utils.

(** ** Terms *)

Inductive term :=
| TVar (n : nat)
| TFun (f : name) (args : list term).

(* Definition sig : Type :=
  name -> option nat.

Context (Σ : sig).

Definition andb_map {A} (f : A -> bool) (l : list A) : bool :=
  foldr (λ x b, b && f x) true l.

Lemma andb_map_In {A} {f : A -> bool} {x : A} : ∀ (l : list A),
  In x l -> andb_map f l -> f x.
Proof.
  elim => [Hx H |a l IH Hx H].
  * elim Hx.
  * elim Hx => [Heq |HIn];
    rewrite /andb_map//= in H; apply andb_prop_elim in H.
    - rewrite -Heq; easy.
    - apply IH; easy.
Qed.

Fixpoint wf (t : fterm) : bool :=
  match t with
  | TVar _ => true
  | TFun f args =>
      Σ (f, length args) && andb_map wf args
  end.

Definition term :=
  { t : fterm | wf t }. *)

(* Lemma wf_fun_inv f : ∀ args,
  wf (TFun f args) -> Forall wf args.
Proof.
  move => args Hwf.
  apply In_Forall. move => t HIn.
  apply (andb_map_In args); auto.
  rewrite /wf in Hwf.
  apply andb_prop_elim in Hwf. easy.
Qed. *)

Lemma term_induction_full :
  ∀ (P : term -> Prop) (Pn : nat -> Prop)
  (IHn : ∀ n, Pn n)
  (IHvar : ∀ n, Pn n -> P (TVar n))
  (IHfun : ∀ f args, Forall P args -> P (TFun f args)),
  ∀ t, P t.
Proof.
  intros; move: t; fix IH 1; induction t.
  * apply IHvar. apply IHn.
  * apply IHfun. elim args; auto.
Qed.

Lemma term_induction :
  ∀ (P : term -> Prop)
  (IHvar : ∀ n, P (TVar n))
  (IHfun : ∀ f args, Forall P args -> P (TFun f args)),
  ∀ t, P t.
Proof.
  intros. eapply term_induction_full; eauto.
  exact (fun _ => I).
Qed.

Fixpoint tsubst (n : nat) (u : term) (t : term) : term :=
  match t with
  | TVar m => if n =? m then u else t
  | TFun f args => TFun f (tsubst n u <$> args)
  end.

Fixpoint tshift (n : nat) (c : nat) (t : term) : term :=
  match t with
  | TVar m => TVar (if m <? c then m else m + n)
  | TFun f args => TFun f (tshift n c <$> args)
  end.

Fixpoint tunshift (n : nat) (c : nat) (t : term) : term :=
  match t with
  | TVar m => TVar (if m <? c then m else m - n)
  | TFun f args => TFun f (tunshift n c <$> args)
  end.
