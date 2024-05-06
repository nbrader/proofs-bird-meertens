Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Open Scope R_scope.

Fixpoint tails {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | _ :: xs' => xs :: tails xs'
end.

(* Define the inits function using reverse and tails *)
Definition inits {A : Type} (xs : list A) : list (list A) :=
  map (@rev A) (tails (rev xs)).

Definition concat {A : Type} : list (list A) -> list A := @List.concat A.

Definition segs {A : Type} : list A -> list (list A) := concat ∘ map tails ∘ inits.

Definition foldl {A B : Type} (f : B -> A -> B) (i : B) (xs : list A) : B := fold_left f xs i.

Fixpoint scanl {A B : Type} (f : B -> A -> B) (i : B) (xs : list A) {struct xs} : list B :=
  i ::
    match xs with
    | nil => nil
    | x :: xs' => scanl f (f i x) xs'
    end.
