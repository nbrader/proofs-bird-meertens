Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.MonoidFree.
Require Import BirdMeertens.ListFunctions.

Open Scope Z_scope.

(* 
   This file establishes tails as a monoid homomorphism to reduce Horner's rule 
   to monoid homomorphism properties.
   
   Key insight: tails can be viewed as a homomorphism from the list monoid (under append)
   to a specialized "tails monoid" where:
   - Elements are lists that are results of tails operations  
   - Operation: take head of each input, append heads, apply tails to result
*)


Section TailsMonoid.
Variable A : Type.

(* Define the underlying set: lists that are results of tails_rec operations on some list *)
Definition is_tails_result (xss : list (list A)) : Prop :=
  exists xs : list A, tails_rec xs = xss.

(* Dependent pair type for valid tails results *)
Definition TailsResult : Type := { xss : list (list A) | is_tails_result xss }.

(* Helper function to extract the list from a TailsResult *)
Definition tails_carrier (tr : TailsResult) : list (list A) := proj1_sig tr.

(* Helper function to extract the proof from a TailsResult *)
Definition tails_proof (tr : TailsResult) : is_tails_result (tails_carrier tr) := proj2_sig tr.

(* Constructor for TailsResult from any list using tails_rec for simplicity *)
Definition mk_tails_result (xs : list A) : TailsResult :=
  exist is_tails_result (tails_rec xs) (ex_intro _ xs eq_refl).

(* Extract the head list from a TailsResult - this is always well-defined *)
Definition head_of_tails_result (tr : TailsResult) : list A :=
  match tails_carrier tr with
  | xs :: _ => xs  (* First element is the head *)
  | [] => []       (* This case should never occur for valid tails results *)
  end.

(* Key lemma: head extraction works correctly *)
Lemma head_of_tails_result_correct : forall xs : list A,
  head_of_tails_result (mk_tails_result xs) = xs.
Proof.
  intros xs.
  unfold head_of_tails_result, mk_tails_result, tails_carrier.
  simpl.
  unfold tails_rec.
  destruct xs as [|x xs'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* The monoid operation on TailsResult: head both arguments, append heads, apply tails *)
Definition tails_result_op (tr1 tr2 : TailsResult) : TailsResult :=
  let head1 := head_of_tails_result tr1 in
  let head2 := head_of_tails_result tr2 in
  mk_tails_result (head1 ++ head2).

(* The identity element for tails monoid - tails [] = [[]] *)
Definition tails_result_id : TailsResult := mk_tails_result [].

(* Prove this forms a magma on TailsResult *)
Instance TailsResultMagma : Magma TailsResult := {
  m_op := tails_result_op
}.

(* Key lemma: tails_result_op is associative *)
Lemma tails_result_op_assoc : forall x y z : TailsResult,
  m_op x (m_op y z) = m_op (m_op x y) z.
Proof.
  intros x y z.
  simpl. (* Unfold m_op to tails_result_op *)
  unfold tails_result_op.
  (* The goal is now: 
     mk_tails_result (head_of_tails_result x ++ head_of_tails_result (mk_tails_result (head_of_tails_result y ++ head_of_tails_result z))) = 
     mk_tails_result (head_of_tails_result (mk_tails_result (head_of_tails_result x ++ head_of_tails_result y)) ++ head_of_tails_result z) *)
  
  (* Use the head extraction lemma to simplify *)
  repeat rewrite head_of_tails_result_correct.
  
  (* Now the goal becomes equality of mk_tails_result applied to associated lists *)
  f_equal.
  apply app_assoc.
Qed.

Instance TailsResultSemigroup : Semigroup TailsResult := {
  sg_assoc := tails_result_op_assoc
}.

(* Prove identity laws for TailsResult *)
Lemma tails_result_left_id : forall x : TailsResult,
  m_op tails_result_id x = x.
Proof.
  intros x.
  simpl. (* Unfold m_op to tails_result_op *)
  unfold tails_result_op, tails_result_id.
  (* The goal is: mk_tails_result (head_of_tails_result (mk_tails_result []) ++ head_of_tails_result x) = x *)
  
  rewrite head_of_tails_result_correct.
  (* Now: mk_tails_result ([] ++ head_of_tails_result x) = x *)
  
  simpl. (* [] ++ y = y *)
  (* Now: mk_tails_result (head_of_tails_result x) = x *)
  
  (* Since x is a TailsResult, it has the form mk_tails_result (some list) *)
  (* The key insight: head_of_tails_result extracts the original list, so applying mk_tails_result to it should give back x *)
  destruct x as [xss Hxss].
  simpl.
  unfold head_of_tails_result, tails_carrier.
  simpl.
  
  (* Hxss tells us that xss = tails_rec (some original list) *)
  unfold is_tails_result in Hxss.
  destruct Hxss as [orig_xs Hxss_eq].
  subst xss.
  
  (* Now we need: mk_tails_result (match tails_rec orig_xs with | ys :: _ => ys | [] => [] end) = exist _ (tails_rec orig_xs) _ *)
  unfold mk_tails_result.
  
  (* For tails_rec, the first element is always the original list *)
  destruct orig_xs as [|h t].
  - (* orig_xs = [] *)
    simpl. f_equal. (* Both sides are [] *)
  - (* orig_xs = h :: t *)  
    simpl. f_equal. (* Both sides are h :: t *)
Qed.

Lemma tails_result_right_id : forall x : TailsResult,
  m_op x tails_result_id = x.
Proof.
  intros x.
  simpl. (* Unfold m_op to tails_result_op *)
  unfold tails_result_op, tails_result_id.
  (* The goal is: mk_tails_result (head_of_tails_result x ++ head_of_tails_result (mk_tails_result [])) = x *)
  
  rewrite head_of_tails_result_correct.
  (* Now: mk_tails_result (head_of_tails_result x ++ []) = x *)
  
  rewrite app_nil_r.
  (* Now: mk_tails_result (head_of_tails_result x) = x *)
  
  (* This follows the same pattern as left identity *)
  destruct x as [xss Hxss].
  simpl.
  unfold head_of_tails_result, tails_carrier.
  simpl.
  
  (* Hxss tells us that xss = tails_rec (some original list) *)
  unfold is_tails_result in Hxss.
  destruct Hxss as [orig_xs Hxss_eq].
  subst xss.
  
  (* Now we need: mk_tails_result (match tails_rec orig_xs with | ys :: _ => ys | [] => [] end) = exist _ (tails_rec orig_xs) _ *)
  unfold mk_tails_result.
  
  (* For tails_rec, the first element is always the original list *)
  destruct orig_xs as [|h t].
  - (* orig_xs = [] *)
    simpl. f_equal. (* Both sides are [] *)
  - (* orig_xs = h :: t *)  
    simpl. f_equal. (* Both sides are h :: t *)
Qed.

Instance TailsResultMonoid : Monoid TailsResult := {
  mn_id := tails_result_id;
  mn_left_id := tails_result_left_id;
  mn_right_id := tails_result_right_id
}.

(* Now prove that mk_tails_result is a monoid homomorphism *)
(* from (list A, app, []) to (TailsResult, tails_result_op, tails_result_id) *)

(* For now, use list monoid directly *)
Instance ListMagma : Magma (list A) := {
  m_op := @app A
}.

Instance ListSemigroup : Semigroup (list A) := {
  sg_assoc := @app_assoc A
}.

Instance ListMonoid : Monoid (list A) := {
  mn_id := [];
  mn_left_id := fun x => eq_refl;
  mn_right_id := @app_nil_r A
}.

Theorem mk_tails_result_is_homomorphism : 
  MonoidHomomorphism ListMonoid TailsResultMonoid mk_tails_result.
Proof.
  split.
  - (* homo_preserves_op: mk_tails_result (xs ++ ys) = m_op (mk_tails_result xs) (mk_tails_result ys) *)
    intros xs ys.
    (* The goal should be: mk_tails_result (xs ++ ys) = tails_result_op (mk_tails_result xs) (mk_tails_result ys) *)
    simpl. (* Simplify m_op to tails_result_op *)
    unfold tails_result_op.
    (* Now we need: mk_tails_result (xs ++ ys) = mk_tails_result (head_of_tails_result (mk_tails_result xs) ++ head_of_tails_result (mk_tails_result ys)) *)
    repeat rewrite head_of_tails_result_correct.
    (* This should now be: mk_tails_result (xs ++ ys) = mk_tails_result (xs ++ ys) *)
    reflexivity.
  - (* homo_preserves_id: mk_tails_result [] = mn_id *)
    simpl.
    unfold mk_tails_result, tails_result_id.
    reflexivity.
Qed.

End TailsMonoid.