Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.FunctionLemmas.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersTac.
Require Import Coq.Numbers.NatInt.NZAxioms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Open Scope Z_scope.

Require Import Coq.Structures.GenericMinMax.
Open Scope Z_scope.

(* Define nonNegPlus using Qle_bool to convert the proposition to a boolean *)
Definition nonNegPlus (x y : Z) : Z :=
  if Z.leb 0 (x + y) then x + y else 0.

Notation "x <#> y" := (nonNegPlus x y) (at level 50, left associativity).
Notation "x <|> y" := (Z.max x y) (at level 50, left associativity).

Definition nonNegSum : list Z -> Z := fold_right nonNegPlus 0.

Definition nonNegMaximum : list Z -> Z := fold_right (fun x y => x <|> y) 0.

(* Refs:
 - form8 -> (* Refs: NONE *)
*)
Definition maxSoFarAndPreviousSum : Z -> (Z * Z) -> (Z * Z) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.
Notation "x <.> y" := (maxSoFarAndPreviousSum x y) (at level 50, left associativity).

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

Lemma app_concat [A : Type] : forall (l : list (list A)),
  concat l = fold_right (@app A) [] l.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma max_idempotent : forall (x : Z), Z.max x x = x.
Proof.
  intros.
  unfold Z.max.
  destruct (x ?= x); reflexivity.
Qed.


(* Refs:
 - form3_eq_form4 -> (* Refs: NONE *)
*)
Lemma fold_max_nonneg : forall (l : list Z), 
  (0 <= fold_right Z.max 0 l)%Z.
Proof.
  induction l as [|x xs IH].
  - simpl. reflexivity.
  - simpl. 
    apply Z.le_trans with (m := fold_right Z.max 0 xs).
    + exact IH.
    + apply Z.le_max_r.
Qed.

Lemma fold_max_app : forall (l1 l2 : list Z),
  fold_right Z.max 0 (l1 ++ l2) = Z.max (fold_right Z.max 0 l1) (fold_right Z.max 0 l2).
Proof.
  intros.
  induction l1 as [|x xs IH].
  - simpl. 
    (* Need to prove: fold_right Z.max 0 l2 = Z.max 0 (fold_right Z.max 0 l2) *)
    rewrite Z.max_r.
    + reflexivity.
    + apply fold_max_nonneg.
  - simpl. rewrite IH. rewrite Z.max_assoc. reflexivity.
Qed.

Lemma fold_promotion : nonNegMaximum ∘ concat = nonNegMaximum ∘ map nonNegMaximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]. 
  - simpl. reflexivity.
  - simpl. unfold nonNegMaximum at 1.
    rewrite app_concat.
    simpl fold_right at 1.
    unfold nonNegMaximum at 2.
    simpl map at 1.
    simpl fold_right at 2.
    rewrite fold_max_app.
    f_equal.
    rewrite app_concat in IH.
    exact IH.
Qed.

(* Prove the max_app lemma *)
(* Lemma max_app : forall (l1 l2 : list Q),
  nonNegMaximum (l1 ++ l2) = Qmax (nonNegMaximum l1) (nonNegMaximum l2).
Proof.
  intros.
  induction l1, l2. simpl.
  - rewrite Qmax_idempotent.
    reflexivity.
  - simpl. unfold nonNegMaximum at 2. simpl.
    (* assert (0 <|> (q <|> fold_right (fun x y : Q => x <|> y) 0 l2) = ).
       reflexivity.
  - intros l2. rewrite IH. apply max_assoc. *)
Admitted. *)

(* Refs: NONE *)
(* Lemma horners_rule_false_2 : ~(maximum ∘ map RLB_sum ∘ inits = fold_right RLB_plus (finite 0)).
Proof.
  apply functions_not_equal.
  (* Use a specific counterexample where the lemma fails. *)
  (* Consider the list [finite 1, finite (-1)] *)
  exists [finite 1; finite (-1)].
  simpl. 
  unfold RLB_sum, maximum, map, inits.
  simpl. (* At this point you would simplify the expressions based on the actual definitions of RLB_sum and maximum *)

  (* Assume specific behavior:
      - RLB_sum [finite 1, finite (-1)] evaluates to finite 0
      - maximum [finite 0, finite 1] evaluates to finite 1 *)
  (* These assumptions are based on typical sum and maximum operations, assuming finite 0 is a neutral element and maximum picks the max value *)
  
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
Definition MaxNonNegSumInits : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ inits.
Definition MaxNonNegSumInitsInd (xs : list Z) : Z := fold_right nonNegPlus 0 xs.

Definition distributes_over_max (op : Z -> Z -> Z) := forall s t x, op (Z.max s t) x = Z.max  (op s x) (op t x).

Lemma plus_distributes_over_max : distributes_over_max (fun x y => x + y).
Proof.
  unfold distributes_over_max.
  unfold Z.max.
  intros.
  unfold gmax.
  case_eq (s + x ?= t + x).
  - case_eq (s ?= t).
    + intros.
      reflexivity.
    + intros.
      rewrite Z.compare_eq_iff in H0.
      rewrite H0.
      reflexivity.
    + intros.
      rewrite Z.compare_eq_iff in H0.
      rewrite H0.
      reflexivity.
  - case_eq (s ?= t).
    + intros.
      rewrite Z.compare_eq_iff in H.
      rewrite H.
      reflexivity.
    + intros.
      reflexivity.
    + intros.
      rewrite Z.compare_lt_iff in H0.
      rewrite Z.compare_gt_iff in H.
      rewrite <- Z.add_lt_mono_r in H0.
      apply Z.lt_asymm in H0.
      contradiction.
  - case_eq (s ?= t).
    + intros.
      rewrite Z.compare_eq_iff in H.
      rewrite H.
      reflexivity.
    + intros.
      rewrite Z.compare_lt_iff in H.
      rewrite Z.compare_gt_iff in H0.
      rewrite <- Z.add_lt_mono_r in H0.
      apply Z.lt_asymm in H0.
      contradiction.
    + intros.
      reflexivity.
Qed.

(* Simple test lemma to verify basic Coq understanding *)
Lemma test_simple : forall x : Z, x + 0 = x.
Proof.
  intro x.
  ring.
Qed.

(* Test nonNegPlus with simple cases *)
Lemma nonNegPlus_zero_right : forall x : Z, x <#> 0 = if Z.leb 0 x then x else 0.
Proof.
  intro x.
  unfold nonNegPlus.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

(* Test how nonNegPlus behaves with Z.max in simple case *)
Lemma nonNegPlus_max_simple : forall x : Z, nonNegPlus (Z.max x x) 0 = Z.max (nonNegPlus x 0) (nonNegPlus x 0).
Proof.
  intro x.
  rewrite max_idempotent.
  rewrite max_idempotent.
  reflexivity.
Qed.

(* Try distributivity in one specific case first *)
Lemma nonNegPlus_distributes_case1 : forall s t x : Z, 
  s = t -> nonNegPlus (Z.max s t) x = Z.max (nonNegPlus s x) (nonNegPlus t x).
Proof.
  intros s t x H_eq.
  rewrite H_eq.
  rewrite max_idempotent.
  rewrite max_idempotent.
  reflexivity.
Qed.

(* Let me search for useful lemmas first *)
(* Remove search commands for now since they cause output issues
Search Z.max.
Search Z.leb.
Search Z.compare.
Search (_ < _)%Z.
Check Z.max_r.
Check Z.lt_le_incl.
Check Z.leb_le.
*)

(* Simplified approach - let me admit this and focus on what I can prove *)
Lemma nonNegPlus_distributes_case2 : forall s t x : Z, 
  (s < t)%Z -> nonNegPlus (Z.max s t) x = Z.max (nonNegPlus s x) (nonNegPlus t x).
Proof.
Admitted.

Lemma nonNegPlus_distributes_over_max : distributes_over_max nonNegPlus.
Proof.
  unfold distributes_over_max.
  intros s t x.
  unfold nonNegPlus.
  destruct (Z.leb 0 (Z.max s t + x)) eqn:H_max;
  destruct (Z.leb 0 (s + x)) eqn:H_s;
  destruct (Z.leb 0 (t + x)) eqn:H_t; try (
    rewrite Z.leb_le in *; rewrite Z.leb_gt in *;
    try (rewrite Z.add_max_distr_r; reflexivity);
    try (contradiction)
  ).
  (* Handle cases systematically *)
  all: (rewrite Z.add_max_distr_r in * || idtac);
  try (rewrite Z.leb_le in *; rewrite Z.leb_gt in *);
  try (reflexivity || contradiction).
  (* If all else fails, use distributivity of addition over max *)
  all: try (rewrite Z.add_max_distr_r; reflexivity).
Admitted.

(* Refs: NONE *)
Lemma generalised_horners_rule : fold_right (fun x y => x <|> y) 0 ∘ map (fold_right (fun x y => x <#> y) 0) ∘ inits = fold_right (fun x y => (x <#> y) <|> 0) 0.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH].
  - simpl.
    rewrite Z.max_l.
    + reflexivity.
    + discriminate.
  - replace (fold_right (fun x0 y : Z => x0 <#> y <|> 0) 0 (x :: xs)) with (x <#> fold_right (fun x0 y : Z => x0 <#> y <|> 0) 0 xs <|> 0) by reflexivity.
    rewrite <- IH.
    (* Additional proof steps would be needed here to complete the theorem *)
    (* This builds on the more advanced proof approach from the remote *)
Admitted.
