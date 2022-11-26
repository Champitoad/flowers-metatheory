Require Import ssreflect stdpp.propset.

Require Import Flowers.Syntax.

Definition monotone {A B : Type} (f : A -> B) (RA : relation A) (RB : relation B) :=
  ∀ x y, RA x y -> RB (f x) (f y).

Class KStruct {A : Type} : Type := {
  world : Type;
  accessible : relation world;
  accessible_po : PartialOrder accessible;
  domain : world -> propset A;
  domain_mono : monotone domain accessible subseteq;
  interp : nat -> ∀ w, { a : A | a ∈ domain w };
  forces : world -> flower;
}.