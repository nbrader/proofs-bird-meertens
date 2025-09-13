Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List. Export Coq.Lists.List.
Import ListNotations. Export ListNotations.

Require Import Coq.ssr.ssrfun.

Definition tails {A : Type}: list A -> list (list A) := fold_right (fun x xsxss => match xsxss with
  | [] => [[]] (* This case is impossible. *)
  | xs :: xss => (x::xs) :: (xs::xss)
end) [[]].

(* Define the inits function using reverse and tails *)
Definition inits {A : Type}: list A -> list (list A) := fold_right (fun x => (cons []) ∘ map (cons x)) [[]].

Definition concat {A : Type} : list (list A) -> list A := @List.concat A.

Definition segs {A : Type} : list A -> list (list A) := concat ∘ map inits ∘ tails.

Fixpoint scan_right {A B : Type} (f : A -> B -> B) (i : B) (xs : list A) {struct xs} : list B :=
  match xs with
  | nil => [i]
  | x :: xs' => let q := fold_right f i xs' in
                f x q :: scan_right f i xs'
  end.

Fixpoint scan_left {A B : Type} (f : B -> A -> B) (xs : list A) (i : B) {struct xs} : list B :=
  i ::
    match xs with
    | nil => nil
    | x :: xs' => scan_left f xs' (f i x)
    end.

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

(* Lemma fold_left_comm_cons_app : forall [A B : Type] (f : A -> A -> A) (x : A) (xs ys : list A) (i : A),
  commutative f -> fold_left f ((x :: xs) ++ ys) i = fold_left f (xs ++ (x :: ys)) i.
Proof.
  intros. *)

(* Lemma foldl_comm_app : forall [A B : Type] (f : A -> A -> A) (xs ys : list A) (i : A),
  commutative f -> fold_left f (xs ++ ys) i = fold_left f (ys ++ xs) i.
Proof.
  intros. *)

Theorem cons_append : forall (X : Type) (x : X) (xs : list X),
  x :: xs = [x] ++ xs.
Proof.
  intros X x xs.
  reflexivity.
Qed.

Lemma fold_left_nil : forall [A B : Type] (f : A -> B -> A) (i : A),
  fold_left f nil i = i.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma fold_right_nil : forall [A B : Type] (f : B -> A -> A) (i : A),
  fold_right f i nil = i.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* Let me approach this more carefully by understanding what we need to prove *)
(* scan_right f i (x::xs') = f x (fold_right f i xs') :: scan_right f i xs' *)
(* tails (x::xs') should give us (x::xs') :: tails xs' *)
(* So map (fold_right f i) (tails (x::xs')) should give us *)
(* fold_right f i (x::xs') :: map (fold_right f i) (tails xs') *)

(* First, let me prove this step by step with admits to check the structure *)
Lemma scan_right_tails_fold : forall {A B : Type} (f : A -> B -> B) (i : B) (xs : list A),
  scan_right f i xs = map (fold_right f i) (tails xs).
Proof.
  intros A B f i xs.
  induction xs as [| x xs' IH].
  - (* Base case: xs = [] *)
    simpl.
    unfold tails. simpl.
    reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    (* scan_right f i (x :: xs') = f x (fold_right f i xs') :: scan_right f i xs' *)
    simpl scan_right.
    (* For tails (x :: xs'), let me manually work out what this should be *)
    (* Based on the tails definition: fold_right (fun x xsxss => ...) [[]] (x::xs') *)
    (* This needs careful analysis of the fold_right structure *)
    admit. (* This is getting quite complex and may need a different approach *)
Admitted.
