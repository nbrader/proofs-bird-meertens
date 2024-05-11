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
Lemma foldl_app : forall [A B : Type] (f : B -> A -> B) (l l' : list A) (i : B),
  foldl f i (l ++ l') = foldl f (foldl f i l) l'.
Proof.
  intros A B.
  revert A.
  revert B.
  unfold foldl.
  apply fold_left_app.
Qed.


(* Allows us to expand a left fold as if it were a right fold, provided the operation allows a form of commutativity. *)
Lemma fold_left_cons_comm : forall [A B : Type] (f : B -> A -> B) (x : A) (xs : list A) (i : B),
  (forall (i : B), commutative (fun x y => f (f i x) y)) -> fold_left f (x :: xs) i = f (fold_left f xs i) x.
Proof.
  intros A B f x xs i comH.
  simpl. (* This reduces `fold_left f (x :: xs) i` to `fold_left f xs (f i x)` *)
  revert i. (* We prepare to use induction on `xs` *)
  induction xs as [|x' xs' IH]; intros i.
  - simpl. (* Base case: `fold_left f [] (f i x)` simplifies to `f i x` *)
    reflexivity.
  - simpl in *. (* Inductive case: unfold the definition for one more element *)
    rewrite <- (IH (f i x')). (* Use the induction hypothesis *)
    f_equal.
    apply comH.
Qed.

Lemma foldl_cons_comm : forall [A B : Type] (f : B -> A -> B) (x : A) (xs : list A) (i : B),
  (forall i, commutative (fun x y => f (f i x) y)) -> foldl f i (x :: xs) = f (foldl f i xs) x.
Proof.
  unfold foldl.
  apply fold_left_cons_comm.
Qed.

Lemma foldl_comm_app : forall [A B : Type] (f : A -> A -> A) (xs ys : list A) (i : A),
  commutative f -> foldl f i (xs ++ ys) = foldl f i (ys ++ xs).
Proof.

Admitted.

Lemma foldl_comm_cons_app : forall [A B : Type] (f : A -> A -> A) (x : A) (xs ys : list A) (i : A),
  commutative f -> foldl f i ((x :: xs) ++ ys) = foldl f i (xs ++ (x :: ys)).
Proof.

Admitted.

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
  - rewrite foldl_app.
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
