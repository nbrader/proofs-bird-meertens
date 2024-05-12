Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidRLBmax.
Require Import BirdMeertens.MonoidRLBplus.
Require Import BirdMeertens.RealsWithLowerBound.
Require Import BirdMeertens.FunctionLemmas.

Require Import Psatz.

Notation "x <.> y" := (RLBmaxSoFarAndPreviousSum x y) (at level 50, left associativity).

Lemma map_distr {A B C : Type} : forall (f : B -> C) (g : A -> B),
  map f ∘ map g = map (f ∘ g).
Proof.
  intros.
  unfold compose.
  f_equal.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite IH.    (* Apply the induction hypothesis *)
    reflexivity.
Qed.

Lemma map_promotion {A : Type} : forall (f : (list A) -> A),
  map f ∘ concat = concat ∘ map (map f).
Proof.
  intros.
  unfold compose.
  f_equal.
  apply functional_extensionality.
  intros.
  apply concat_map.
Qed.

Lemma fold_promotion : RLBmaximum ∘ concat = RLBmaximum ∘ map RLBmaximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite cons_append.
    rewrite RLBmaximum_distr.
    rewrite RLBmaximum_distr.
    rewrite IH.
    f_equal.
    apply RLBmaximum_idempotent.
Qed.

Lemma horners_rule : True. (* RLBmaximum ∘ map RLBsum ∘ inits = fold_right RLBplus (Some 0). *)
Proof.
  
Admitted.

Lemma horners_rule_false : RLBmaximum ∘ map RLBsum ∘ inits <> fold_right RLBplus None.
Proof.
  intros H. (* Assume horners_rule is true and aim for a contradiction. *)
  assert (Hempty: (RLBmaximum (map RLBsum (inits nil))) = fold_right RLBplus None nil). 
  - rewrite <- H. reflexivity. (* Use the hypothesis on an empty list. *)
  - (* Evaluate the left side of Hempty. *)
    simpl in Hempty. (* Simplify the left side with empty list calculations. *)
    unfold RLBmaximum, map, RLBsum, inits in Hempty.
    simpl in Hempty.
    unfold MonoidRLBmax.identity in Hempty.

    (* At this point, we have:
      Hempty : Some 0 = None
      This is a contradiction because Some 0 cannot be equal to None. *)
    discriminate Hempty. (* `Some 0 = None` is impossible, which means our initial assumption H must be false. *)
Qed.


Lemma horners_rule_false_2 : ~(RLBmaximum ∘ map RLBsum ∘ inits = fold_right RLBplus (Some 0)).
Proof.
  apply functions_not_equal.
  (* Use a specific counterexample where the lemma fails. *)
  (* Consider the list [Some 1, Some (-1)] *)
  exists [Some 1; Some (-1)].
  simpl. 
  unfold RLBsum, RLBmaximum, map, inits.
  simpl. (* At this point you would simplify the expressions based on the actual definitions of RLBsum and RLBmaximum *)

  (* Assume specific behavior:
      - RLBsum [Some 1, Some (-1)] evaluates to Some 0
      - RLBmaximum [Some 0, Some 1] evaluates to Some 1 *)
  (* These assumptions are based on typical sum and maximum operations, assuming Some 0 is a neutral element and RLBmaximum picks the max value *)
  
  intuition.
  inversion H. (* Use inversion to exploit the injectivity of Some *)
  unfold Rmax in H1. (* Expand Rmax definition *)
  destruct (Rle_dec (1 + 0) 0) in H1. (* Apply a lemma or use built-in Real number inequalities *)
  + lra.
  + destruct (Rle_dec (1 + (-1 + 0)) (1 + 0)) in H1.
    * lra.
    * lra.
Qed.