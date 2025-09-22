(* Major Lemmas - Immediate Dependencies of BirdMeertens.v *)
(* This file contains the actual theorem statements that BirdMeertens.v depends on directly *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.Lemmas.
Require Import CoqUtilLib.ListFunctions.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* ===== IMMEDIATE DEPENDENCIES FROM BirdMeertens.v ===== *)
(* These are the actual theorem statements that BirdMeertens.v uses directly *)

(* 0. map_promotion - used in form4_eq_form5 *)
Lemma map_distr {A B C : Type} : forall (f : B -> C) (g : A -> B),
  map f ∘ map g = map (f ∘ g).
Proof.
  intros.
  unfold compose.
  f_equal.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* 1. map_promotion - used in form2_eq_form3 *)
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

(* 2. fold_promotion - imported from Lemmas.v *)
Lemma fold_promotion : nonNegMaximum ∘ concat = nonNegMaximum ∘ map nonNegMaximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros x.
  induction x as [|xs xss IH].
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

(* 3. nonNegPlus_comm - used in form7_eq_form8 *)
Lemma nonNegPlus_comm : forall x y : Z, nonNegPlus x y = nonNegPlus y x.
Proof.
  intros x y.
  unfold nonNegPlus.
  rewrite Z.add_comm.
  reflexivity.
Qed.

(* 4. fold_scan_fusion_pair - used in form7_eq_form8 *)
Lemma fold_scan_fusion_pair :
  forall (xs : list Z),
    fold_right
      (fun x uv => let '(u, v) := uv in (Z.max u (nonNegPlus x v), nonNegPlus x v))
      (0, 0) xs
    =
    (fold_right Z.max 0 (scan_right nonNegPlus 0 xs),
     fold_right nonNegPlus 0 xs).
Proof.
  intros xs.
  induction xs as [| x xs' IH].
  - (* Base case: xs = [] *)
    simpl.
    reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    simpl scan_right.
    simpl fold_right.
    (* Destructure the IH *)
    rewrite IH.
    (* Now we need to prove the components are equal *)
    f_equal.
    (* For the first component, we need Z.max commutativity *)
    apply Z.max_comm.
Qed.

(* 5. generalised_horners_rule - used in form5_eq_form6 *)
Lemma generalised_horners_rule : fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits.
Proof.
  apply functional_extensionality.
  intros xs.
  (* First, simplify using the fact that (x <#> y <|> 0) = (x <#> y) *)
  assert (H: fold_right (fun x y : Z => x <#> y <|> 0) 0 xs = fold_right nonNegPlus 0 xs).
  {
    apply fold_right_ext.
    intros a b.
    apply tropical_horner_eq_nonNegPlus.
  }
  rewrite H.
  clear H.
  (* Now we need to prove: fold_right nonNegPlus 0 xs = (nonNegMaximum ∘ map nonNegSum ∘ inits) xs *)
  unfold compose.
  unfold nonNegSum.
  (* Apply the key lemma *)
  apply fold_right_nonNegPlus_eq_max_prefixes.
Qed.

(* 6. generalised_horners_rule' - used in form5_eq_form6 *)
Lemma generalised_horners_rule' : nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec = nonNegMaximum ∘ map nonNegSum ∘ tails_rec.
Proof.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  f_equal.
  apply map_ext.
  intros tail.
  (* For each tail, we need: (nonNegMaximum ∘ map nonNegSum ∘ inits) tail = nonNegSum tail *)
  unfold compose.
  unfold nonNegSum.
  (* This follows from our first lemma:
     nonNegMaximum (map (fold_right nonNegPlus 0) (inits tail)) = fold_right nonNegPlus 0 tail *)
  symmetry.
  apply fold_right_nonNegPlus_eq_max_prefixes.
Qed.

(* 7. fold_right_ext - imported from Lemmas.v *)

(* ===== DUAL FORM DEPENDENCIES ===== *)

(* 8. fold_promotion_dual - used in form3_dual_eq_form4_dual *)
Lemma fold_promotion_dual : nonNegMaximum_dual ∘ (concat (A:=Z)) = nonNegMaximum_dual ∘ map nonNegMaximum_dual.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros x.
  unfold nonNegMaximum_dual.
  (* Convert both sides using duality *)
  rewrite max_fold_duality_zero.
  rewrite max_fold_duality_zero.
  (* Now both sides use fold_right, so we can apply the original fold_promotion *)
  unfold nonNegMaximum.
  (* We need to show that the mapped functions are equivalent under duality *)
  assert (H_map_eq: map (fun xs => fold_left (fun x0 y : Z => x0 <|> y) xs 0) x =
                    map (fun xs => fold_right (fun x0 y : Z => x0 <|> y) 0 xs) x).
  {
    apply map_ext.
    intro xs.
    apply max_fold_duality_zero.
  }
  rewrite H_map_eq.
  (* Now apply the original fold_promotion with the right-fold version *)
  assert (H_fold_prom := fold_promotion).
  unfold compose in H_fold_prom.
  unfold nonNegMaximum in H_fold_prom.
  apply (equal_f H_fold_prom x).
Qed.

(* 9. fold_scan_fusion_pair_dual - used in form7_dual_eq_form8_dual *)
Lemma fold_scan_fusion_pair_dual :
  forall (xs : list Z),
    fold_left
      (fun uv x => let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x))
      xs (0, 0)
    =
    (fold_left Z.max (scan_left (fun acc x => nonNegPlus acc x) xs 0) 0,
     fold_left (fun acc x => nonNegPlus acc x) xs 0).
Proof.
  intro xs.
  (* This is a special case of fold_scan_fusion_pair_general with u0 = 0, v0 = 0 *)
  apply fold_scan_fusion_pair_general.
  - (* 0 >= 0 *) apply Z.ge_le_iff. apply Z.le_refl.
  - (* 0 >= 0 *) apply Z.ge_le_iff. apply Z.le_refl.
Qed.

(* 10. fold_left_ext - used in form7_dual_eq_form8_dual *)
Lemma fold_left_ext {A B : Type} : forall (f g : B -> A -> B) (xs : list A) (init : B),
  (forall acc x, f acc x = g acc x) ->
  fold_left f xs init = fold_left g xs init.
Proof.
  intros f g xs init H.
  generalize dependent init.
  induction xs as [|x xs' IH]; simpl; intro init.
  - reflexivity.
  - rewrite H. apply IH.
Qed.

(* 11. fold_left_nonNegPlus_eq_max_suffixes - used in form5_dual_eq_form6_dual *)
Lemma fold_left_nonNegPlus_eq_max_suffixes : forall xs : list Z,
  fold_left (fun acc x => nonNegPlus acc x) xs 0 =
  nonNegMaximum_dual (map nonNegSum_dual (tails xs)).
Proof.
  intros xs.

  (* xs is one of its tails *)
  assert (H_in: In xs (tails xs)).
  {
    rewrite tails_rec_equiv.
    induction xs as [|x xs' IH].
    - simpl. left. reflexivity.
    - simpl. left. reflexivity.
  }

  (* Every element of tails xs is a suffix of xs, and xs gives the maximum sum *)
  (* We'll use fold_left_max_returns_max to establish this *)

  (* First, show nonNegSum_dual xs >= 0 *)
  assert (Hm_nonneg: nonNegSum_dual xs >= 0).
  { apply nonNegSum_dual_nonneg. }

  (* Show that xs is in the mapped list *)
  assert (H_xs_mapped: In (nonNegSum_dual xs) (map nonNegSum_dual (tails xs))).
  {
    rewrite in_map_iff.
    exists xs.
    split.
    - reflexivity.
    - exact H_in.
  }

  (* Show that nonNegSum_dual xs is >= all other elements in the mapped list *)
  assert (H_is_max: forall y, In y (map nonNegSum_dual (tails xs)) -> y <= nonNegSum_dual xs).
  {
    intros y H_y_in.
    rewrite in_map_iff in H_y_in.
    destruct H_y_in as [ys [H_eq H_ys_in]].
    rewrite <- H_eq.
    (* ys is a suffix of xs, so nonNegSum_dual ys <= nonNegSum_dual xs *)
    (* This follows from tails_are_suffixes and nonNegSum_dual_suffix_le *)
    destruct (tails_are_suffixes Z xs ys H_ys_in) as [zs H_app].
    apply nonNegSum_dual_suffix_le.
    exists zs; exact H_app.
  }

  (* Now apply fold_left_max_returns_max *)
  unfold nonNegMaximum_dual.
  symmetry.
  apply fold_left_max_returns_max with (m := nonNegSum_dual xs).
  - exact Hm_nonneg.
  - exact H_is_max.
  - exact H_xs_mapped.
Qed.

(* 12. fold_left_right_rev - used in Original_Dual_Equivalence *)
Theorem fold_left_right_rev {A B : Type} :
  forall (f : A -> B -> B) (xs : list A) (init : B),
    fold_left (fun acc x => f x acc) xs init = fold_right f init (rev xs).
Proof.
  intros f xs init.
  revert init.
  induction xs as [|x xs' IH]; intros init.
  - simpl. reflexivity.
  - simpl rev. rewrite fold_right_app. simpl.
    simpl fold_left. rewrite IH. reflexivity.
Qed.

(* 13. generalised_horners_rule_dual - SHOULD BE used in form5_dual_eq_form6_dual BUT ISN'T *)
Lemma generalised_horners_rule_dual :
  (fun xs => fold_left (fun acc x => nonNegPlus acc x) xs 0) = nonNegMaximum_dual ∘ map nonNegSum_dual ∘ tails.
Proof.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  (* This follows directly from fold_left_nonNegPlus_eq_max_suffixes *)
  apply fold_left_nonNegPlus_eq_max_suffixes.
Qed.

(* 14. generalised_horners_rule_dual' - SHOULD BE used in form5_dual_eq_form6_dual BUT ISN'T *)
Lemma generalised_horners_rule_dual' :
  nonNegMaximum_dual ∘ map (nonNegMaximum_dual ∘ map nonNegSum_dual ∘ tails) ∘ inits_rec =
  nonNegMaximum_dual ∘ map nonNegSum_dual ∘ inits_rec.
Proof.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  f_equal.
  apply map_ext.
  intros prefix.
  (* For each prefix, we need: (nonNegMaximum ∘ map nonNegSum_dual ∘ tails) prefix = nonNegSum_dual prefix *)
  unfold compose.
  (* This follows from our first dual lemma:
     nonNegMaximum (map nonNegSum_dual (tails prefix)) = nonNegSum_dual prefix *)
  symmetry.
  apply fold_left_nonNegPlus_eq_max_suffixes.
Qed.

(* ===== HELPER DEFINITIONS ===== *)
(* Note: maxSoFarAndPreviousSum and maxSoFarAndPreviousSum_dual definitions *)
(* are imported from Lemmas.v and available for BirdMeertens.v *)

(* ===== UTILITY LIBRARY FUNCTIONS ===== *)
(* Note: tails_rec_equiv_ext, scan_right_tails_rec_fold, scan_left_inits_rec_fold *)
(* are imported from CoqUtilLib.ListFunctions and available for BirdMeertens.v *)