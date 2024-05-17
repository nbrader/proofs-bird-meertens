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
 - RLB_nonNegPlus
 - RLB_nonNegSum
 - RLB_nonNegPlusEitherPlusOr0
 - RLB_nonNegPlusNotNegInf
 - horners_rule -> (* Refs: NONE *)
 - form6
 - form7
*)
Definition RLB_nonNegPlus (x y : RLB) : RLB :=
  if RLB_le_dec (finite 0) (RLB_plus x y) then RLB_plus x y else finite 0.
Notation "x <#> y" := (RLB_nonNegPlus x y) (at level 50, left associativity).

(* Refs:
 - horners_rule -> (* Refs: NONE *)
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Definition RLB_nonNegSum : list RLB -> RLB := fold_right RLB_nonNegPlus (finite 0).

(* Refs: NONE *)
Lemma RLB_nonNegPlusEitherPlusOr0 : forall (x y : RLB),
  x <#> y = if RLB_le_dec (finite 0) (x <+> y) then x <+> y else finite 0.
Proof.
  intros x y.
  unfold RLB_nonNegPlus.
  destruct (RLB_le_dec (finite 0) (x <+> y)); reflexivity.
Qed.

(* Refs:
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Lemma RLB_nonNegPlusNotNegInf : forall (x y : RLB), exists r, (x <#> y) = finite r.
Proof.
  intros x y.
  unfold RLB_nonNegPlus.
  destruct x, y.
  - (* Case: x = finite r, y = finite r0 *)
    destruct (RLB_le_dec (finite 0) (finite r <+> finite r0)).
    + exists (r + r0). simpl. reflexivity.
    + exists 0. reflexivity.
  - (* Case: x = finite r, y = neg_inf *)
    simpl. destruct (RLB_le_dec (finite 0) neg_inf).
    + (* This case is impossible since neg_inf is not >= finite 0 *)
      exfalso. simpl in r0. exact r0.
    + exists 0. simpl. reflexivity.
  - (* Case: x = neg_inf, y = finite r *)
    simpl. destruct (RLB_le_dec (finite 0) neg_inf).
    + (* This case is impossible since neg_inf is not >= finite 0 *)
      exfalso. simpl in r0. exact r0.
    + exists 0. simpl. reflexivity.
  - (* Case: x = neg_inf, y = neg_inf *)
    simpl. destruct (RLB_le_dec (finite 0) neg_inf).
    + (* This case is impossible since neg_inf is not >= finite 0 *)
      exfalso. simpl in r. exact r.
    + exists 0. simpl. reflexivity.
Qed.

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
Lemma horners_rule_false_2 : ~(RLB_maximum ∘ map RLB_sum ∘ inits = fold_right RLB_plus (finite 0)).
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
Qed.

(* Refs:
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Definition MaxNonNegSumInits : list RLB -> RLB := RLB_maximum ∘ map RLB_nonNegSum ∘ inits.

(* Refs:
 - horners_rule -> (* Refs: NONE *)
*)
Lemma MaxNonNegSumInits_mor (x : RLB) (xs : list RLB) : MaxNonNegSumInits (x :: xs) = x <#> MaxNonNegSumInits xs.
Proof.
  unfold MaxNonNegSumInits.
  unfold compose.
  (* Compute inits (x :: xs). *)
  (* = [[]; [x]; [x; y1]; [x; y1; y2]; ...] if xs = [y1; y2; ...] *)

  assert (H: inits (x :: xs) = [] :: map (cons x) (inits xs)).
  {
    admit.
  }
  rewrite H. clear H.
  
  (* map RLB_nonNegSum (inits (x :: xs)) = map RLB_nonNegSum ([] :: map (cons x) (inits xs)) *)
  simpl.
  (* = RLB_nonNegSum [] :: map RLB_nonNegSum (map (cons x) (inits xs)) *)
  (* = (finite 0) :: map (fun l => RLB_nonNegSum (x :: l)) (inits xs) *)
  simpl.

  assert (H1: map RLB_nonNegSum (map (cons x) (inits xs)) = map (fun l => x <#> RLB_nonNegSum l) (inits xs)).
  {
    induction xs as [| y ys IH].
    - simpl. reflexivity.
    - admit.
  }
  rewrite H1. clear H1.

  (* Now, RLB_maximum (finite 0 :: map (fun l => x <#> RLB_nonNegSum l) (inits xs)) *)
  (* = RLB_max (finite 0) (RLB_maximum (map (fun l => x <#> RLB_nonNegSum l) (inits xs))) *)
  simpl.

  (* = RLB_maximum (map (fun l => x <#> RLB_nonNegSum l) (inits xs)) *)

  (* = x <#> RLB_maximum (map RLB_nonNegSum (inits xs)) *)
  (* = x <#> MaxNonNegSumInits xs *)

  induction xs as [| y ys IH].
  - simpl.
    unfold RLB_maximum.
    simpl.
    unfold Rmax.
    pose (RLB_nonNegPlusNotNegInf x (finite 0)).
    destruct e.
    rewrite H.
    simpl.
    unfold MonoidRLB_max.identity.
    rewrite H.
    case (Rle_dec 0 x0).
      + intros.
        reflexivity.
      + intros.
        exfalso.
        admit.
  - simpl.
    unfold RLB_maximum.
    unfold MonoidRLB_max.identity.
    admit.
Admitted.

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
