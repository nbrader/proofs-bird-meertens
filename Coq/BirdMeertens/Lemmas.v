Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidRLBmax.
Require Import BirdMeertens.MonoidRLBplus.
Require Import BirdMeertens.RealsWithLowerBound.

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

Lemma horners_rule : RLBmaximum ∘ map RLBsum ∘ inits = fold_right RLBplus None.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - unfold RLBsum.
    simpl. (* Goal: RLBmaximum (Some 0 :: nil) = None     <---- This is false so, by reductio ad absurdum, horners_rule (as currently stated) is false.
                                                                It looks like I'll have to qualify it with an assumption of the result being at least 0. *)
    
Admitted.
