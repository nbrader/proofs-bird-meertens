Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidRLB_max.
Require Import BirdMeertens.MonoidRLB_plus.
Require Import BirdMeertens.RealsWithLowerBound.
Require Import BirdMeertens.FunctionLemmas.

Require Import Psatz.

(* Refs:
 - form8 -> (* Refs: NONE *)
*)
Definition RLB_maxSoFarAndPreviousSum : RLB -> (RLB * RLB) -> (RLB * RLB) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.
Notation "x <.> y" := (RLB_maxSoFarAndPreviousSum x y) (at level 50, left associativity).

(* Refs:
 - form4_eq_form5 -> (* Refs: NONE *)
*)
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

(* Refs:
 - form2_eq_form3 -> (* Refs: NONE *)
*)
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

(* Refs:
 - form3_eq_form4 -> (* Refs: NONE *)
*)
Lemma fold_promotion : RLB_maximum ∘ concat = RLB_maximum ∘ map RLB_maximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite cons_append.
    rewrite RLB_maximum_distr.
    rewrite RLB_maximum_distr.
    rewrite IH.
    f_equal.
    apply RLB_maximum_idempotent.
Qed.

(* Refs: NONE *)
Lemma horners_rule_false : RLB_maximum ∘ map RLB_sum ∘ inits <> fold_right RLB_plus neg_inf.
Proof.
  intros H. (* Assume horners_rule is true and aim for a contradiction. *)
  assert (Hempty: (RLB_maximum (map RLB_sum (inits nil))) = fold_right RLB_plus neg_inf nil). 
  - rewrite <- H. reflexivity. (* Use the hypothesis on an empty list. *)
  - (* Evaluate the left side of Hempty. *)
    simpl in Hempty. (* Simplify the left side with empty list calculations. *)
    unfold RLB_maximum, map, RLB_sum, inits in Hempty.
    simpl in Hempty.
    unfold MonoidRLB_max.identity in Hempty.

    (* At this point, we have:
      Hempty : finite 0 = neg_inf
      This is a contradiction because finite 0 cannot be equal to neg_inf. *)
    discriminate Hempty. (* `finite 0 = neg_inf` is impossible, which means our initial assumption H must be false. *)
Qed.

(* Refs: NONE *)
(* Lemma horners_rule_false_2 : ~(RLB_maximum ∘ map RLB_sum ∘ inits = fold_right RLB_plus (finite 0)).
Proof.
  apply functions_not_equal.
  (* Use a specific counterexample where the lemma fails. *)
  (* Consider the list [finite 1, finite (-1)] *)
  exists [finite 1; finite (-1)].
  simpl. 
  unfold RLB_sum, RLB_maximum, map, inits.
  simpl. (* At this point you would simplify the expressions based on the actual definitions of RLB_sum and RLB_maximum *)

  (* Assume specific behavior:
      - RLB_sum [finite 1, finite (-1)] evaluates to finite 0
      - RLB_maximum [finite 0, finite 1] evaluates to finite 1 *)
  (* These assumptions are based on typical sum and maximum operations, assuming finite 0 is a neutral element and RLB_maximum picks the max value *)
  
  intuition.
  inversion H. (* Use inversion to exploit the injectivity of finite *)
  unfold Rmax in H1. (* Expand Rmax definition *)
  destruct (Rle_dec (1 + 0) 0) in H1. (* Apply a lemma or use built-in Real number inequalities *)
  + lra.
  + destruct (Rle_dec (1 + (-1 + 0)) (1 + 0)) in H1.
    * lra.
    * lra.
Qed. *)

(* Refs:
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Definition MaxNonNegSumInits : list RLB -> RLB := RLB_maximum ∘ map RLB_nonNegSum ∘ inits.
Definition MaxNonNegSumInitsInd (xs : list RLB) : RLB := fold_right RLB_nonNegPlus (finite 0) xs.

(* Refs: NONE *)
Lemma MaxNonNegSumInits_extensionally_equal : MaxNonNegSumInits = MaxNonNegSumInitsInd.
Proof.
  apply functional_extensionality.
  intros.
  unfold MaxNonNegSumInits.
  unfold compose.
  induction x.
  - simpl.
    unfold RLB_maximum.
    unfold MonoidRLB_max.RLB_FreeMonoid.extend.
    simpl.
    unfold MonoidRLB_max.identity.
    reflexivity.
  - simpl.
    rewrite <- IHx. clear IHx.
    unfold RLB_nonNegPlus.
    destruct (RLB_le_dec (finite 0) (a <+> RLB_maximum (map RLB_nonNegSum (inits x)))).
    + rewrite cons_append.
      rewrite RLB_maximum_distr.
      rewrite (RLB_maximum_singleton (finite 0)).
      (* rewrite (RLB_max_implementation (finite 0) (a <+> RLB_maximum (map RLB_nonNegSum (inits x)))) in r. *)
Admitted.

(* Refs:
 - horners_rule -> (* Refs: NONE *)
*)
Lemma MaxNonNegSumInits_mor (x : RLB) (xs : list RLB) : MaxNonNegSumInits (x :: xs) = x <#> MaxNonNegSumInits xs.
Proof.
  rewrite MaxNonNegSumInits_extensionally_equal.
  simpl.
  reflexivity.
Qed.

(* Refs: form4_eq_form6 -> (* Refs: NONE *) *)
Lemma horners_rule : (RLB_maximum ∘ map RLB_nonNegSum ∘ inits) = fold_right RLB_nonNegPlus (finite 0).
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite <- IH.
    apply (MaxNonNegSumInits_mor x xs).
Qed.

(* Refs: generalised_horners_rule -> (* Refs: NONE *) *)
Definition foldl [A B : Type] (f : A -> B -> A) (i : A) (xs : list B) := fold_left f xs i.

(* Refs: NONE *)
Lemma generalised_horners_rule (op : R -> R -> R) : foldl (fun x y => x + y) 0 ∘ map (foldl op 1) ∘ tails = foldl (fun x y => x * y + 1) 1.
Proof.

Admitted.
