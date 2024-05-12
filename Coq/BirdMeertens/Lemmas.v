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

Lemma horners_rule : RLBmaximum ∘ map RLBsum ∘ inits = fold_right RLBplus (Some 0).
Proof.
  unfold compose.
  apply functional_extensionality.
  intros x.
  induction x as [|x xs IH]; simpl.
  - unfold RLBsum.
    simpl.
    reflexivity.
  - assert (x <+> fold_right RLBplus (Some 0) xs = fold_right RLBplus (Some 0) (x :: xs)) as H by reflexivity.
    rewrite H.
    assert (fold_right RLBplus (Some 0) (x :: xs) = MonoidRLBplus.RLBsumImplementation (x :: xs)) as H0 by (unfold MonoidRLBplus.RLBsumImplementation; reflexivity).
    rewrite H0.
    rewrite RLBsum_implementation_correctness.
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
