Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List. Export Coq.Lists.List.
Import ListNotations. Export ListNotations.

Require Import Coq.ssr.ssrfun.
Require Import Coq.micromega.Lia.

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

(* Let me try a different approach - prove by computation for small examples first *)
(* and then try to generalize the pattern *)

(* Simple computational lemma for concrete small cases *)
Example tails_one : tails [1] = [[1]; []].
Proof. 
  unfold tails. simpl. reflexivity.
Qed.

Example tails_two : tails [1; 2] = [[1; 2]; [2]; []].
Proof.
  unfold tails. simpl. reflexivity.  
Qed.

(* Now let me try the main theorem with a more direct computational approach *)
Example scan_right_tails_example : 
  scan_right Nat.add 0 [1; 2] = map (fold_right Nat.add 0) (tails [1; 2]).
Proof.
  simpl scan_right.
  rewrite tails_two.
  simpl map.
  simpl fold_right.
  reflexivity.
Qed.

(* Let me try to prove a more general version by understanding the fold_right structure *)
(* Let me try a more direct approach - prove a key lemma about fold_right behavior *)
(* Let me focus on computational examples first *)
(* Skip the problematic general lemma for now *)

(* Let me try computational examples to understand the pattern *)
Example tails_two_elements : tails [1; 2] = [[1; 2]; [2]; []].
Proof.
  unfold tails. simpl. reflexivity.
Qed.

Example tails_three_elements : tails [1; 2; 3] = [[1; 2; 3]; [2; 3]; [3]; []].
Proof.
  unfold tails. simpl. reflexivity.
Qed.

(* Now let me try to prove the first element property for specific cases *)
Lemma tails_first_elem_is_input_singleton (x : nat) :
  exists rest, tails [x] = [x] :: rest.
Proof.
  unfold tails. simpl.
  exists [[]]. reflexivity.
Qed.

Lemma tails_first_elem_is_input_pair (x y : nat) :
  exists rest, tails [x; y] = [x; y] :: rest.
Proof.
  unfold tails. simpl.
  eexists. reflexivity.
Qed.

(* New approach: try to prove the structural property directly using the fold_right definition *)
(* Let me analyze what happens with the fold_right step by step *)

(* Key insight from computational examples: I need to prove that after fold_right builds tails xs',
   the pattern match always picks the second case and first_elem = xs' *)

(* Let me try a more direct approach using the pattern I observed *)
(* The key insight: for any non-empty list xs, tails xs starts with xs itself *)

(* Based on computational examples, I know the pattern works. *)
(* Let me try to complete scan_right_tails_fold by assuming the structural property *)

(* Alternative approach: define a recursive version of tails and prove equivalence *)
Fixpoint tails_rec {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' => xs :: tails_rec xs'
  end.

(* Prove that our recursive version matches the expected behavior *)
Example tails_rec_test1 : tails_rec [1] = [[1]; []].
Proof. simpl. reflexivity. Qed.

Example tails_rec_test2 : tails_rec [1; 2] = [[1; 2]; [2]; []].
Proof. simpl. reflexivity. Qed.

Lemma fold_right_tails_never_nil : forall {A : Type} (xs : list A),
  fold_right (fun x xsxss => match xsxss with 
                             | [] => [[]] 
                             | xs :: xss => (x::xs) :: (xs::xss) 
                             end) [[]] xs <> [].
Proof.
  intros A xs.
  induction xs as [| x xs' IH].
  - simpl. discriminate.
  - simpl. 
    destruct (fold_right _ [[]] xs') eqn:E.
    + (* If fold_right produced [], that contradicts IH *)
      exfalso. apply IH. reflexivity.
    + discriminate.
Qed.

Lemma fold_right_tails_cons : forall {A : Type} (x : A) (xs : list A),
  exists t ts, fold_right (fun x xsxss => match xsxss with 
                                          | [] => [[]] 
                                          | xs :: xss => (x::xs) :: (xs::xss) 
                                          end) [[]] xs = t :: ts.
Proof.
  intros A x xs.
  induction xs as [| y ys IH].
  - simpl. exists [], []. reflexivity.
  - simpl.
    destruct (fold_right _ [[]] ys) eqn:E.
    + pose proof (fold_right_tails_never_nil ys).
      contradiction.
    + exists (y :: l), (l :: l0). reflexivity.
Qed.

Lemma tails_rec_equiv : forall {A : Type} (xs : list A), tails xs = tails_rec xs.
Proof.
  intros A xs.
  induction xs as [| x xs' IH].
  
  - (* Base case: xs = [] *)
    simpl tails_rec.
    unfold tails. simpl.
    reflexivity.
    
  - (* Inductive case: xs = x :: xs' *)
    simpl tails_rec.
    unfold tails at 1.
    simpl fold_right.
    
    (* The key insight: fold_right on xs' produces tails xs' *)
    assert (Htails: fold_right (fun x xsxss => match xsxss with 
                                               | [] => [[]] 
                                               | xs :: xss => (x::xs) :: (xs::xss) 
                                               end) [[]] xs' = tails xs').
    { unfold tails. reflexivity. }
    
    rewrite Htails.
    rewrite IH.
    
    (* Now we need to show the pattern match on tails_rec xs' *)
    destruct xs' as [| y ys].
    
    + (* xs' = [] *)
      simpl.
      reflexivity.
      
    + (* xs' = y :: ys *)
      simpl tails_rec.
      reflexivity.
Qed.

(* With tails_rec_equiv, tails_cons becomes trivial *)
Lemma tails_cons : forall {A : Type} (x : A) (xs : list A),
  tails (x :: xs) = (x :: xs) :: tails xs.
Proof.
  intros A x xs.
  rewrite (tails_rec_equiv (x :: xs)).
  rewrite (tails_rec_equiv xs).
  simpl tails_rec.
  reflexivity.
Qed.

(* Let me add some simpler, provable utility lemmas first *)
(* These can serve as building blocks for more complex proofs *)

Lemma scan_right_singleton : forall {A B : Type} (f : A -> B -> B) (i : B) (x : A),
  scan_right f i [x] = [f x i; i].
Proof.
  intros A B f i x.
  simpl. reflexivity.
Qed.

Lemma scan_right_nil : forall {A B : Type} (f : A -> B -> B) (i : B),
  scan_right f i [] = [i].
Proof.
  intros A B f i.
  simpl. reflexivity.
Qed.

Lemma tails_nil : forall {A : Type}, tails (@nil A) = [[]].
Proof.
  intro A.
  unfold tails. simpl. reflexivity.
Qed.

Lemma tails_singleton : forall {A : Type} (x : A), tails [x] = [[x]; []].
Proof.
  intro A. intro x.
  unfold tails. simpl. reflexivity.
Qed.

(* Let me try to understand this with concrete examples first *)
Example scan_right_tails_example_nil : forall (f : nat -> nat -> nat) (i : nat),
  scan_right f i [] = map (fold_right f i) (tails []).
Proof.
  intros f i.
  rewrite scan_right_nil.
  rewrite tails_nil.
  simpl map.
  simpl fold_right.
  reflexivity.
Qed.

Example scan_right_tails_example_one (x : nat) (f : nat -> nat -> nat) (i : nat) :
  scan_right f i [x] = map (fold_right f i) (tails [x]).
Proof.
  rewrite tails_singleton.
  simpl map.
  simpl scan_right.
  simpl fold_right.
  reflexivity.
Qed.

(* The pattern is clear from examples. Let me state the general property *)
Lemma tails_head_property : forall {A : Type} (xs : list A),
  xs <> [] -> exists rest, tails xs = xs :: rest.
Proof.
  intros A xs Hneq.
  (* Using the equivalence, we can reason about the simpler recursive definition. *)
  rewrite (tails_rec_equiv xs).
  (* Since xs is not empty, it must be of the form (x :: xs'). *)
  destruct xs as [|x xs'].
  - (* This case is impossible given xs <> []. *)
    contradiction.
  - (* The definition of tails_rec for a non-empty list is exactly what we need. *)
    simpl tails_rec.
    exists (tails_rec xs').
    reflexivity.
Qed.

(* Now the original theorem follows from equivalence (if we can prove it) *)
Lemma scan_right_tails_fold : forall {A B : Type} (f : A -> B -> B) (i : B) (xs : list A),
  scan_right f i xs = map (fold_right f i) (tails xs).
Proof.
  intros A B f i xs.
  induction xs as [| x xs' IH]. 

  - (* Base case: xs = [] *)
    simpl.
    reflexivity.

  - (* Inductive case: xs = x :: xs' *)
    (* Expand scan_right on the left hand side. *)
    simpl scan_right.

    (* Use tails_cons to expand tails on the right hand side. *)
    rewrite (tails_cons x xs').

    (* Expand map on the right hand side. *)
    simpl map.

    (* The tails of both sides are now equal by the induction hypothesis. *)
    rewrite IH.
    (* The heads of both sides are definitionally equal. *)
    f_equal.
Qed.

(* Now we can prove the original theorem using the equivalence *)

Lemma scan_right_tails_rec_fold : forall {A B : Type} (f : A -> B -> B) (i : B) (xs : list A),
  scan_right f i xs = map (fold_right f i) (tails_rec xs).
Proof.
  intros A B f i xs.
  induction xs as [| x xs' IH].
  
  - (* Base case: xs = [] *)
    reflexivity.
    
  - (* Inductive case: xs = x :: xs' *)
    (* Let's debug by doing step by step *)
    simpl scan_right.
    simpl tails_rec.
    simpl map.
    (* Now the goal should be: 
       f x (fold_right f i xs') :: scan_right f i xs' = 
       fold_right f i (x :: xs') :: map (fold_right f i) (tails_rec xs') *)
    (* Since fold_right f i (x :: xs') = f x (fold_right f i xs'), 
       the goal becomes:
       f x (fold_right f i xs') :: scan_right f i xs' = 
       f x (fold_right f i xs') :: map (fold_right f i) (tails_rec xs') *)
    f_equal.
    exact IH.
Qed.
