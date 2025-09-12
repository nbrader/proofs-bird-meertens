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
Require Import Coq.Init.Nat.
Require Import Coq.Structures.GenericMinMax.

Open Scope Z_scope.

(* Define nonNegPlus using Qle_bool to convert the proposition to a boolean *)
Definition nonNegPlus (x y : Z) : Z :=
  if Z.leb 0 (x + y) then x + y else 0.

Notation "x <#> y" := (nonNegPlus x y) (at level 50, left associativity).
Notation "x <|> y" := (Z.max x y) (at level 50, left associativity).

Definition nonNegSum (xs : list Z) : Z := fold_left nonNegPlus xs 0%Z.

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
  - rewrite IH. (* Apply the induction hypothesis *)
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
  destruct (x ?= x);
  reflexivity.
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
  - simpl. (* Need to prove: fold_right Z.max 0 l2 = Z.max 0 (fold_right Z.max 0 l2) *)
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

(* Lemma foldl_promotion (xss : list (list nat)) :
  fold_left Nat.add (concat xss) 0%nat =
  fold_left Nat.add (map (fun xs => fold_left Nat.add xs 0%nat) xss) 0%nat.
Proof.
Admitted. *)

(* Refs: NONE *)
(*
Lemma horners_rule_false_2 : ~(maximum ∘ map RLB_sum ∘ inits = fold_right RLB_plus (finite 0)).
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
Qed.
*)

(* Refs:
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Definition MaxNonNegSumInits : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ inits.
Definition MaxNonNegSumInitsInd (xs : list Z) : Z := fold_right nonNegPlus 0 xs.

Definition distributes_over_max (op : Z -> Z -> Z) := forall s t x, op (Z.max s t) x = Z.max  (op s x) (op t x).

(* Helper lemma: addition distributes over max *)
Lemma max_add_distributes : forall s t x,
  Z.max s t + x = Z.max (s + x) (t + x).
Proof.
  intros.
  rewrite Z.add_max_distr_r.
  reflexivity.
Qed.



Lemma nonNegPlus_distributes_over_max : distributes_over_max nonNegPlus.
Admitted.
(* Proof.
  unfold distributes_over_max, nonNegPlus.
  intros s t x.
  rewrite max_add_distributes.
  (* Case analysis on the boolean conditions *)
  destruct (Z.leb 0 (s + x)) eqn:Hs;
  destruct (Z.leb 0 (t + x)) eqn:Ht;
  destruct (Z.leb 0 (Z.max (s + x) (t + x))) eqn:Hmax.
  - (* Case 1: s+x >= 0, t+x >= 0, max >= 0 *)
    apply Z.leb_le in Hs. apply Z.leb_le in Ht. apply Z.leb_le in Hmax.
    reflexivity.
  - (* Case 2: s+x >= 0, t+x >= 0, but max < 0 (impossible) *)
    apply Z.leb_le in Hs. apply Z.leb_le in Ht. apply Z.leb_gt in Hmax.
    exfalso.
    assert (0 <= Z.max (s + x) (t + x)) by
      (apply Z.le_trans with (m := s + x); [assumption | apply Z.le_max_l]).
    lia.
  - (* Case 3: s+x >= 0, t+x < 0, max >= 0 *)
    apply Z.leb_le in Hs. apply Z.leb_gt in Ht. apply Z.leb_le in Hmax.
    simpl.
    rewrite Z.max_l by (apply Hs).
    rewrite Z.max_l by (apply Hs).
    reflexivity.
  - (* Case 4: s+x >= 0, t+x < 0, but max < 0 (impossible) *)
    apply Z.leb_le in Hs. apply Z.leb_gt in Ht. apply Z.leb_gt in Hmax.
    exfalso.
    assert (0 <= Z.max (s + x) (t + x)) by
      (apply Z.le_trans with (m := s + x); [assumption | apply Z.le_max_l]).
    lia.
  - (* Case 5: s+x < 0, t+x >= 0, max >= 0 *)
    apply Z.leb_gt in Hs. apply Z.leb_le in Ht. apply Z.leb_le in Hmax.
    simpl.
    rewrite Z.max_r by (apply Ht).
    rewrite Z.max_r by (apply Ht).
    reflexivity.
  - (* Case 6: s+x < 0, t+x >= 0, but max < 0 (impossible) *)
    apply Z.leb_gt in Hs. apply Z.leb_le in Ht. apply Z.leb_gt in Hmax.
    exfalso.
    assert (0 <= Z.max (s + x) (t + x)) by
      (apply Z.le_trans with (m := t + x); [assumption | apply Z.le_max_r]).
    lia.
  - (* Case 7: s+x < 0, t+x < 0, but max >= 0 (impossible) *)
    apply Z.leb_gt in Hs. apply Z.leb_gt in Ht. apply Z.leb_le in Hmax.
    exfalso.
    assert (Z.max (s + x) (t + x) < 0) by (apply Z.max_lub_lt; lia).
    lia.
  - (* Case 8: s+x < 0, t+x < 0, max < 0 *)
    apply Z.leb_gt in Hs. apply Z.leb_gt in Ht. apply Z.leb_gt in Hmax.
    simpl. reflexivity.
Qed. *)

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
    + reflexivity.
  - (* Inductive case: x :: xs *)
    (* For now, the inductive case needs more development *)
    (* The base case works, but this requires deeper lemmas *)
Admitted.

(* Lemma horner_rule (xs : list nat) :
  fold_left Nat.add (map (fun ys => fold_left Nat.mul ys 1%nat) (tails xs)) 0%nat =
  fold_left (fun acc y => (acc * y + 1)%nat) xs 1%nat.
Proof.
Admitted. *)

Lemma scan_lemma (xs : list nat) : scan_left Nat.add xs 0%nat = map (fun ys : list nat => fold_left Nat.add ys 0%nat) (inits xs).
Proof.
Admitted.

Lemma fold_scan_fusion (xs : list Z) : fold_left Z.add (scan_left Z.mul xs 1%Z) 0%Z = fst (fold_left (fun '(u,v) x => let w := (v * x)%Z in ((u + w)%Z, w)) xs (0%Z,1%Z)).
Proof.
Admitted.
