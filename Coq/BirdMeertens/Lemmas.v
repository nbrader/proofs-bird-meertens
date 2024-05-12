Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidRLBmax.
Require Import BirdMeertens.RealsWithLowerBound.

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

Lemma horners_rule : RLBmaximum ∘ map RLBsum ∘ inits = fold_right RLBplus None.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite <- IH.
    assert (x = RLBmaximum (x :: nil)).
    + unfold RLBmaximum.
      simpl.
      rewrite RLBmax_right_id.
      reflexivity.
    + assert (RLBplus x (RLBmaximum (map RLBsum (inits xs))) = RLBmaximum (x :: map RLBsum (inits xs))).
      * unfold RLBmaximum.
        unfold RLBFreeMonoid.extend.
        simpl.
         (* extend_monoid_homomorphism
      rewrite H at 2.
      apply AFreeMonoid.extend_monoid_homomorphism.
      rewrite <- RLBmaximum_distr.
      simpl.
      rewrite RLBmax_right_id.
      reflexivity. *)
Admitted.
