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

Definition RLB_nonNegPlus : RLB -> RLB -> RLB := fun x y => (x <+> y) <|> finite 0.
Notation "x <#> y" := (RLB_nonNegPlus x y) (at level 50, left associativity).

Lemma RLB_nonNegPlusEitherPlusOr0 : forall (x y : RLB), (RLB_lte (finite 0) (x <+> y) -> x <#> y = x <+> y) \/ (~(RLB_lte (finite 0) (x <+> y)) -> x <#> y = finite 0).
Proof.
  intros.
  unfold RLB_nonNegPlus.
  unfold RLB_max.
  case_eq (x <+> y).
  - intros.
    left.
    intros.
    unfold RLB_lte in H0.
    unfold Rmax.
    case_eq (Rle_dec r 0).
    + intros.
      rewrite (Rle_antisym 0 r H0).
      * reflexivity.
      * apply r0.
    + intros.
      reflexivity.
  - simpl.
    intros.
    right.
    intros.
    reflexivity.
Qed.

Lemma RLB_nonNegPlusNotNegInf : forall (x y : RLB), exists r, (x <#> y) = finite r.
Proof.
  intros.
  destruct (RLB_nonNegPlusEitherPlusOr0 x y) as [Hsum | Hzero].
  case_eq (x <+> y).
  - intros.
    exists r.
    rewrite Hsum.
    + apply H.
    + case x, y in H.
      (* * 
  - intros.
    exfalso.
    unfold RLB_nonNegPlus in Hsum.
    rewrite H in Hsum.
    simpl in Hsum.
    discriminate.
  - rewrite Hzero.
    exists 0.
    reflexivity. *)
Admitted.

(* Lemma RLB_nonNegPlusNotNegInf : forall (x y : RLB), exists r, (x <#> y) = finite r.
Proof.
  intros.
  pose (H := RLB_nonNegPlusEitherPlusOr0 x y (x <#> y) eq_refl).
  case_eq (x <#> y).
  - intros.
    exists r.
    reflexivity.
  - intros.
    exfalso.
    unfold RLB_nonNegPlus in H0.
    case x, y in H0.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
Qed. *)

Definition RLB_nonNegSum : list RLB -> RLB := fold_right RLB_nonNegPlus (finite 0).

Definition RLB_maxSoFarAndPreviousSum : RLB -> (RLB * RLB) -> (RLB * RLB) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.
Notation "x <.> y" := (RLB_maxSoFarAndPreviousSum x y) (at level 50, left associativity).


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

Lemma horners_rule_attept3 : (RLB_maximum ∘ map RLB_nonNegSum ∘ inits) = fold_right RLB_nonNegPlus (finite 0).
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite <- IH.
    unfold RLB_maximum.
    unfold MonoidRLB_max.RLB_FreeMonoid.extend.
    unfold MonoidRLB_max.identity.
    simpl.
    unfold MonoidRLB_max.RLB_FreeMonoid.extend_monoid.
    simpl.
    induction (map RLB_nonNegSum (inits (x :: xs))), (map RLB_nonNegSum (inits xs)).
    + exfalso.
      unfold RLB_maximum in IH.
      simpl in IH.
      induction xs in IH.
      * simpl in IH.
        discriminate.
      * simpl in IH.
        (* assert ()
        unfold RLB_nonNegPlus in IH.
        case_eq (a <#> fold_right RLB_nonNegPlus (finite 0) xs).
        -- intros.
           rewrite H in IH.
           discriminate.
        -- intros. *)
        (* rewrite <- IHxs.
        case_eq (a <#> fold_right RLB_nonNegPlus (finite 0) xs).
        -- intros.
           rewrite H in IH.
           discriminate.
        -- intros.
        rewrite <- IHxs. *)
      
    (* assert (RLB_maximum [x] = x).
    + unfold RLB_maximum.
      unfold MonoidRLB_max.RLB_FreeMonoid.extend.
      unfold MonoidRLB_max.identity.
      apply RLB_max_right_id.
    + rewrite <- H at 2.
      rewrite <- RLB_maximum_distr.
    rewrite <- (app_nil_l x).
    RLB_maximum_distr
    rewrite (rev_cons xs x).
    rewrite RLB_maximum_distr.
    rewrite RLB_maximum_distr.
    rewrite IH.
    f_equal.
    apply RLB_maximum_idempotent. *)
Admitted.

Lemma horners_rule_attept3_false : (RLB_maximum ∘ map RLB_nonNegSum ∘ inits) <> fold_right RLB_nonNegPlus (finite 0).
Proof.
  
Admitted.
