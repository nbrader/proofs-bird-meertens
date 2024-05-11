Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.

Require Import Coq.ssr.ssrfun.

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

(* I'm having to remake some lemmas for foldl so it can have the required argument order*)
Lemma foldl_left_app : forall [A B : Type] (f : A -> B -> A) (l l' : list B) (i : A),
  foldl f i (l ++ l') = foldl f (foldl f i l) l'.
Proof.
  unfold foldl.
  apply fold_left_app.
Qed.

Theorem cons_append : forall (X : Type) (x : X) (xs : list X),
  x :: xs = [x] ++ xs.
Proof.
  intros X x xs.
  reflexivity.
Qed.

Context {A : Type} (HmagmaA : Magma A) (HsemigroupA : Semigroup A) (HmonoidA : Monoid A).

Lemma monoid_concat `{Monoid A} (idH : idempotent m_op) : let f := foldl m_op mn_id in f ∘ concat = f ∘ map f.
Proof.
  intros.
  unfold f.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite foldl_left_app.
    rewrite mn_left_id.
    (* rewrite FreeMonoid.extend_monoid_homomorphism (fun x => x).
    rewrite IH.
    f_equal.
    apply idH. *)
Admitted.

Lemma foldl_nil : forall [A B : Type] (f : A -> B -> A) (i : A),
  foldl f i nil = i.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
