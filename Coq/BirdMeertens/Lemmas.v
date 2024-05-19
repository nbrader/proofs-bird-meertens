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
Lemma fold_promotion : nonNegMaximum ∘ concat = nonNegMaximum ∘ map nonNegMaximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]. simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite (app_concat (x :: xs)).
Admitted.

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

Lemma nonNegPlus_distributes_over_max : distributes_over_max nonNegPlus.
Proof.
  unfold distributes_over_max, Z.max, nonNegPlus.
  intros s t x.
  case s, t, x; try reflexivity.
  - simpl.
    destruct ((p ?= p)%positive); reflexivity.
  - simpl.
    case_eq ((p0 ?= p + p0)%positive).
    + intros.
      case_eq ((p0 ?= p + p0)%positive).
      (* rewrite Z.compare_eq_iff in H.
  f_equal.
  apply plus_distributes_over_max. *)
Admitted.

(* Refs: NONE *)
Lemma generalised_horners_rule : fold_right (fun x y => x <|> y) 0 ∘ map (fold_right (fun x y => x <#> y) 0) ∘ inits = fold_right (fun x y => (x <#> y) <|> 0) 0.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH].
  - simpl.
    (* rewrite max_idempotent.
    reflexivity.
  - unfold inits.
    + assert (fold_right (fun x : Q => cons [] ∘ map (cons x)) [[]] (x :: xs) = (cons [] ∘ map (cons x)) (fold_right (fun x : Q => cons [] ∘ map (cons x)) [[]] xs)).
      * unfold fold_right.
        reflexivity.
      * rewrite H.
        fold (inits xs). *)
Admitted.
