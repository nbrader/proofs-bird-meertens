Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import ListFunctions.
Require Import MonoidMax.

Definition RfoldlSum := foldl (fun x y => x + y) 0.

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

Lemma foldl_promotion : RfoldlSum ∘ concat = RfoldlSum ∘ map RfoldlSum.
Proof.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - unfold compose.
    rewrite concat_cons.
    rewrite map_cons.
    unfold RfoldlSum.
    simpl.
    rewrite Rplus_0_l.
    rewrite foldl_left_app.
    fold RfoldlSum.
    induction xs.
    + simpl.
      reflexivity.
    + simpl.
      rewrite foldl_left_app.
      admit.
Admitted.

Lemma foldl_promotion1 : RfoldlSum ∘ concat = RfoldlSum ∘ map RfoldlSum.
Proof.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - unfold compose.
    induction x, xs.
    + unfold concat, RfoldlSum.
      simpl.
      f_equal.
      ring.
    + rewrite concat_cons.
      rewrite app_nil_l.
      unfold compose in IH.
      unfold concat in IH.
      rewrite IH.
      rewrite map_cons.
      rewrite map_cons.
      rewrite map_cons.
      unfold RfoldlSum.
      simpl.
      rewrite Rplus_0_l.
      rewrite Rplus_0_l.
      rewrite Rplus_0_l.
      fold RfoldlSum.
      reflexivity.
    + rewrite map_cons.
      simpl.
      rewrite app_nil_r.
      unfold RfoldlSum.
      simpl.
      rewrite Rplus_0_l.
      rewrite Rplus_0_l.
      reflexivity.
    + admit.
Admitted.

Lemma fold_promotion : maximum ∘ concat = maximum ∘ map maximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - 
Admitted.
