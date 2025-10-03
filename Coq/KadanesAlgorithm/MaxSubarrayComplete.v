Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.

(* Import the generalized framework and tropical instance *)
Require Import KadanesAlgorithm.KadanesAlgorithm.
Require Import KadanesAlgorithm.TropicalKadane.
Require Import FreeMonoid.StructSemiring.
Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.FunctionLemmas.

(*
=================================================================================
COMPLETE KADANE'S ALGORITHM WITH CORRECTNESS PROOF
=================================================================================

This file defines a complete, practical version of Kadane's algorithm that:
1. Handles all-nonpositive inputs by returning the maximum single element
2. Handles inputs with positive elements using the semiring-based algorithm
3. Is proven correct by connecting form8 (efficient) to form1 (specification)

STRATEGY:
- Prove that gform1 (from tropical semiring) matches the plain-English spec
- Use the proven equivalence gform1 = gform8 from TropicalKadane.v
- Handle the all-nonpositive case separately (max single element)
- Combine both cases into a complete algorithm

GOAL:
Show that the efficient algorithm correctly computes:
  "the maximum sum among all contiguous subarrays"
*)

(*
=================================================================================
SPECIFICATION
=================================================================================
*)

(* A segment (contiguous subarray) is a portion of the list between indices i and j *)
(* We use the existing segs function which generates all contiguous subarrays *)

(* Helper: standard list sum *)
Fixpoint list_sum (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: xs' => x + list_sum xs'
  end.

(* Non-empty segments only - filter out empty list *)
Definition nonempty_segs (xs : list Z) : list (list Z) :=
  filter (fun seg => match seg with [] => false | _ => true end) (segs xs).

(* The maximum subarray sum is the maximum sum among all NON-EMPTY segments *)
(* This matches the standard definition which requires at least one element *)
Definition max_subarray_sum_spec (xs : list Z) : Z :=
  (* Specification: maximum sum over all non-empty contiguous subarrays *)
  match nonempty_segs xs with
  | [] => 0  (* only happens when xs = [] *)
  | seg :: rest => fold_right Z.max (list_sum seg) (map list_sum rest)
  end.

(*
=================================================================================
CONVERSION BETWEEN ExtZ AND Z
=================================================================================
*)

(* Convert ExtZ to Z - NegInf maps to a very negative value or 0 for practical purposes *)
Definition extZ_to_Z (x : ExtZ) : Z :=
  match x with
  | NegInf => 0  (* For max subarray, empty subarray has sum 0 *)
  | Finite z => z
  end.

(* Convert Z to ExtZ *)
Definition Z_to_extZ (z : Z) : ExtZ := Finite z.

(*
=================================================================================
CONNECTING TO TROPICAL SEMIRING GFORM8
=================================================================================
*)

(* Use the kadane_algorithm from TropicalKadane.v which is proven correct *)
(* It returns option Z, so we need to handle the None case *)
Definition tropical_kadanes (xs : list Z) : Z :=
  match KadanesAlgorithm.TropicalKadane.kadane_algorithm xs with
  | Some z => z
  | None => 0  (* Empty list case *)
  end.

(*
=================================================================================
PROVING GFORM1 MATCHES THE SPECIFICATION
=================================================================================
*)

(* First, we need to show that gform1 from the tropical semiring formulation
   actually computes what we want: the maximum subarray sum *)

(* TODO: This requires showing that:
   1. semiring_sum with ExtZ max operation gives us the maximum
   2. semiring_product with ExtZ addition gives us the sum
   3. The composition computes max sum over all segments
*)

(*
=================================================================================
COMPLETE ALGORITHM WITH CASE HANDLING
=================================================================================
*)

(* Check if all elements are nonpositive *)
Fixpoint all_nonpositive (xs : list Z) : bool :=
  match xs with
  | [] => true
  | x :: xs' => (x <=? 0) && all_nonpositive xs'
  end.

(* For all-nonpositive case: return maximum single element *)
Fixpoint max_element (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | [x] => x
  | x :: xs' => Z.max x (max_element xs')
  end.

(* The complete algorithm *)
Definition kadanes_algorithm (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | _ =>
      if all_nonpositive xs
      then max_element xs
      else tropical_kadanes xs  (* Use the tropical semiring algorithm *)
  end.

(*
=================================================================================
CORRECTNESS THEOREM
=================================================================================

Theorem kadanes_algorithm_correct : forall xs : list Z,
  kadanes_algorithm xs = max_subarray_sum_spec xs.

PROOF STRATEGY:
1. Case: xs = []
   - Trivial: both return 0

2. Case: all_nonpositive xs = true
   - Show max_element xs = maximum single element
   - Show maximum subarray in all-nonpositive case is a single element
   - Therefore max_element xs = max_subarray_sum_spec xs

3. Case: all_nonpositive xs = false (has positive elements)
   - Use form8 from TropicalKadane.v (the efficient algorithm)
   - Use proven equivalence: gform1 = gform8 from Generalized_Kadane_Correctness
   - Prove gform1 xs = max_subarray_sum_spec xs (form1 is the spec!)
   - Conclude: form8 xs = max_subarray_sum_spec xs

The key insight: gform1 (specification form) IS almost the same as our plain-English
spec - it's literally "sum of products over all segments" which for tropical semiring
means "max of sums over all segments" = maximum subarray sum!
*)

(*
=================================================================================
LEMMAS FOR ALL-NONPOSITIVE CASE
=================================================================================
*)

(* Helper: When all elements are nonpositive, extending a segment decreases or maintains the sum *)
Lemma list_sum_nonpositive_decreases : forall xs x,
  all_nonpositive xs = true ->
  x <= 0 ->
  list_sum (xs ++ [x]) <= list_sum xs.
Proof.
  intros xs x Hall Hx.
  induction xs as [|y ys IH].
  - simpl. lia.
  - simpl in *.
    apply andb_true_iff in Hall. destruct Hall as [Hy Hall'].
    apply Z.leb_le in Hy.
    assert (IH' := IH Hall').
    lia.
Qed.

(* Helper: Adding a nonpositive element to the front decreases sum *)
Lemma list_sum_cons_nonpositive : forall x xs,
  x <= 0 ->
  all_nonpositive xs = true ->
  list_sum (x :: xs) <= list_sum xs.
Proof.
  intros x xs Hx Hxs.
  simpl.
  induction xs as [|y ys IH].
  - simpl. lia.
  - simpl in *.
    apply andb_true_iff in Hxs. destruct Hxs as [Hy Hys].
    apply Z.leb_le in Hy.
    lia.
Qed.

(* Lemma: max_element returns the maximum element in the list *)
Lemma max_element_is_max : forall xs x,
  In x xs ->
  xs <> [] ->
  x <= max_element xs.
Proof.
  intros xs x Hin Hne.
  induction xs as [|y ys IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. destruct ys.
      * simpl. lia.
      * simpl. apply Z.le_max_l.
    + destruct ys as [|z zs].
      * contradiction.
      * simpl. apply Z.max_le_iff. right.
        apply IH; auto. discriminate.
Qed.


(* Helper: In a nonpositive list, the sum is at most any single element *)
Lemma sum_le_max_in_nonpositive : forall seg x,
  all_nonpositive seg = true ->
  In x seg ->
  list_sum seg <= x.
Proof.
  intros seg x Hall Hin.
  induction seg as [|y ys IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* x = y, the head element *)
      subst. simpl.
      simpl in Hall. apply andb_true_iff in Hall. destruct Hall as [Hy Hys].
      apply Z.leb_le in Hy.
      (* list_sum ys <= 0 since all elements are nonpositive *)
      assert (Hsum: list_sum ys <= 0).
      { clear IH. induction ys as [|z zs IHys].
        - simpl. lia.
        - simpl. simpl in Hys. apply andb_true_iff in Hys.
          destruct Hys as [Hz Hzs]. apply Z.leb_le in Hz.
          assert (IHys' := IHys Hzs). lia.
      }
      lia.
    + (* x is in the tail *)
      simpl in Hall. apply andb_true_iff in Hall. destruct Hall as [Hy Hys].
      apply Z.leb_le in Hy.
      simpl.
      assert (IH' := IH Hys Hin').
      lia.
Qed.

(* Lemma: max_element xs is actually an element of xs *)
Lemma max_element_in_list : forall xs,
  all_nonpositive xs = true ->
  xs <> [] ->
  exists x, In x xs /\ max_element xs = x.
Proof.
  intros xs Hall Hne.
  induction xs as [|y ys IH].
  - contradiction.
  - destruct ys as [|z zs].
    + (* Singleton case *)
      exists y. split.
      * left. reflexivity.
      * simpl. reflexivity.
    + (* Multiple elements: y :: z :: zs *)
      simpl in Hall. apply andb_true_iff in Hall.
      destruct Hall as [Hy Hys].
      assert (Hne': (z :: zs) <> []) by discriminate.
      assert (IH' := IH Hys Hne').
      destruct IH' as [w [Hin_w Heq_w]].
      (* Case analysis on zs to expose the structure of max_element *)
      destruct zs as [|z' zs'].
      * (* zs = [], so z :: zs = [z] and max_element [z] = z *)
        simpl in Heq_w. subst w.
        simpl max_element.
        destruct (Z_le_gt_dec y z) as [Hle | Hgt].
        -- (* y <= z, so max is z *)
           exists z. split.
           ++ right. left. reflexivity.
           ++ apply Z.max_r. exact Hle.
        -- (* y > z, so max is y *)
           exists y. split.
           ++ left. reflexivity.
           ++ apply Z.max_l. lia.
      * (* zs = z' :: zs', so we have y :: z :: z' :: zs' *)
        (* max_element (y :: z :: z' :: zs') = Z.max y (Z.max z (max_element (z' :: zs'))) *)
        (* and max_element (z :: z' :: zs') = Z.max z (max_element (z' :: zs')) = w *)
        assert (Heq_expanded: max_element (y :: z :: z' :: zs') = Z.max y (max_element (z :: z' :: zs'))).
        { simpl. reflexivity. }
        rewrite Heq_expanded.
        destruct (Z_le_gt_dec y (max_element (z :: z' :: zs'))) as [Hle | Hgt].
        -- (* y <= max_element (z :: z' :: zs'), so max is w *)
           exists w. split.
           ++ right. exact Hin_w.
           ++ rewrite <- Heq_w. apply Z.max_r. exact Hle.
        -- (* y > max_element (z :: z' :: zs'), so max is y *)
           exists y. split.
           ++ left. reflexivity.
           ++ apply Z.max_l. lia.
Qed.

(* Helper: Elements in inits are elements of the original list *)
Lemma elem_in_init_in_list : forall (xs init : list Z) (y : Z),
  In init (inits xs) ->
  In y init ->
  In y xs.
Proof.
  intros xs init y Hin_init Hin_y.
  generalize dependent init.
  generalize dependent y.
  induction xs as [|x xs' IH].
  - intros y init Hin_init Hin_y.
    unfold inits in Hin_init. simpl in Hin_init.
    destruct Hin_init as [Heq | []].
    subst init. contradiction.
  - intros y init Hin_init Hin_y.
    rewrite inits_cons in Hin_init.
    simpl in Hin_init. destruct Hin_init as [Heq | Hin'].
    + subst init. contradiction.
    + apply in_map_iff in Hin'.
      destruct Hin' as [init' [Heq Hin'']].
      subst init. simpl in Hin_y. destruct Hin_y as [Heq | Hin_y'].
      * left. exact Heq.
      * right. apply (IH y init' Hin'' Hin_y').
Qed.

(* Helper: Elements in tails are elements of the original list *)
Lemma elem_in_tail_in_list : forall (xs tail : list Z) (y : Z),
  In tail (tails xs) ->
  In y tail ->
  In y xs.
Proof.
  intros xs tail y Hin_tail Hin_y.
  generalize dependent tail.
  generalize dependent y.
  induction xs as [|x xs' IH].
  - intros y tail Hin_tail Hin_y.
    unfold tails, compose in Hin_tail. simpl in Hin_tail.
    destruct Hin_tail as [Heq | []].
    subst tail. contradiction.
  - intros y tail Hin_tail Hin_y.
    rewrite tails_cons in Hin_tail.
    simpl in Hin_tail. destruct Hin_tail as [Heq | Hin'].
    + subst tail. exact Hin_y.
    + simpl. right. apply (IH y tail Hin' Hin_y).
Qed.

(* Helper: Elements in segments are elements of the original list *)
Lemma elem_in_seg_in_list : forall (xs seg : list Z) (y : Z),
  In seg (segs xs) ->
  In y seg ->
  In y xs.
Proof.
  intros xs seg y Hin_seg Hin_y.
  unfold segs, compose in Hin_seg.
  apply in_concat in Hin_seg.
  destruct Hin_seg as [inits_tail [Hin_map Hin_inits]].
  apply in_map_iff in Hin_map.
  destruct Hin_map as [tail [Heq Hin_tail]].
  subst inits_tail.
  (* y is in an init of tail, so y is in tail *)
  assert (Hin_y_tail: In y tail).
  { apply (elem_in_init_in_list tail seg y Hin_inits Hin_y). }
  (* tail is in tails xs, so y is in xs *)
  apply (elem_in_tail_in_list xs tail y Hin_tail Hin_y_tail).
Qed.

(* Helper: All elements of xs are <= 0 *)
Lemma all_elem_nonpositive : forall xs y,
  all_nonpositive xs = true ->
  In y xs ->
  y <= 0.
Proof.
  intros xs y Hall Hin.
  induction xs as [|x xs' IH].
  - contradiction.
  - unfold all_nonpositive in Hall. simpl in Hall.
    apply andb_true_iff in Hall. destruct Hall as [Hx Hall'].
    apply Z.leb_le in Hx.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. exact Hx.
    + apply (IH Hall' Hin').
Qed.

(* Helper lemma: If all elements of a list are in xs and xs is all_nonpositive, then the list is all_nonpositive *)
Lemma all_elem_in_implies_nonpositive : forall xs seg,
  all_nonpositive xs = true ->
  (forall y, In y seg -> In y xs) ->
  all_nonpositive seg = true.
Proof.
  intros xs seg Hall Hsub.
  induction seg as [|z zs IH].
  - reflexivity.
  - unfold all_nonpositive. simpl. apply andb_true_iff. split.
    + apply Z.leb_le.
      assert (Hin_z: In z xs).
      { apply Hsub. left. reflexivity. }
      apply (all_elem_nonpositive xs z Hall Hin_z).
    + apply IH.
      intros y Hin_y.
      apply Hsub. right. exact Hin_y.
Qed.

(* Helper: Sublists of all_nonpositive lists are all_nonpositive *)
Lemma all_nonpositive_sublist : forall xs seg,
  all_nonpositive xs = true ->
  In seg (segs xs) ->
  all_nonpositive seg = true.
Proof.
  intros xs seg Hall Hin.
  apply (all_elem_in_implies_nonpositive xs seg Hall).
  intros y Hin_y.
  apply (elem_in_seg_in_list xs seg y Hin Hin_y).
Qed.

(* Lemma: In all-nonpositive lists, any non-empty segment sum is at most the maximum single element *)
Lemma segment_sum_at_most_max_element : forall xs seg,
  all_nonpositive xs = true ->
  In seg (nonempty_segs xs) ->
  xs <> [] ->
  list_sum seg <= max_element xs.
Proof.
  intros xs seg Hall Hin Hne.
  (* Since seg is in nonempty_segs, it's not empty *)
  unfold nonempty_segs in Hin.
  apply filter_In in Hin. destruct Hin as [Hin_segs Hnonemp].
  destruct seg as [|x xs'].
  - (* seg = [] contradicts Hnonemp *)
    simpl in Hnonemp. discriminate.
  - (* seg = x :: xs', a nonempty segment *)
    (* seg inherits all_nonpositive from xs *)
    assert (Hseg_np: all_nonpositive (x :: xs') = true).
    { apply (all_nonpositive_sublist xs (x :: xs') Hall Hin_segs). }
    (* x is in xs *)
    assert (Hx_in: In x xs).
    { apply (elem_in_seg_in_list xs (x :: xs') x Hin_segs). left. reflexivity. }
    (* Sum of seg <= x (by sum_le_max_in_nonpositive) *)
    assert (Hsum_x: list_sum (x :: xs') <= x).
    { apply (sum_le_max_in_nonpositive (x :: xs') x Hseg_np). left. reflexivity. }
    (* x <= max_element xs (by max_element_is_max) *)
    assert (Hx_max: x <= max_element xs).
    { apply (max_element_is_max xs x Hx_in Hne). }
    (* Combine the two inequalities *)
    lia.
Qed.

(* Helper: [] is always in inits *)
Lemma nil_in_inits : forall (A : Type) (xs : list A),
  In [] (inits xs).
Proof.
  intros A xs.
  induction xs as [|x xs' IH].
  - unfold inits. simpl. left. reflexivity.
  - rewrite inits_cons. left. reflexivity.
Qed.

(* Helper: [x] is in inits of any list starting with x *)
Lemma singleton_in_inits : forall (x : Z) xs,
  In [x] (inits (x :: xs)).
Proof.
  intros x xs.
  rewrite inits_cons.
  simpl. right.
  apply in_map_iff.
  exists []. split.
  - reflexivity.
  - apply nil_in_inits.
Qed.

(* Helper: If y::ys is in tails xs, then [y] is in segs xs *)
Lemma singleton_from_tail : forall (y : Z) ys xs,
  In (y :: ys) (tails xs) ->
  In [y] (segs xs).
Proof.
  intros y ys xs Hin.
  unfold segs, compose.
  apply in_concat.
  exists (inits (y :: ys)).
  split.
  - apply in_map. exact Hin.
  - apply singleton_in_inits.
Qed.

(* Helper: If x is in xs, then there exists a tail in tails xs starting with x *)
Lemma elem_in_some_tail : forall (x : Z) xs,
  In x xs ->
  exists ys, In (x :: ys) (tails xs).
Proof.
  intros x xs Hin.
  induction xs as [|y ys IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* x = y *)
      subst. exists ys.
      rewrite tails_cons.
      left. reflexivity.
    + (* x is in ys *)
      destruct (IH Hin') as [zs Hin_tail].
      exists zs.
      rewrite tails_cons.
      right.
      exact Hin_tail.
Qed.

(* Lemma: The maximum element appears as a singleton segment *)
Lemma max_element_in_segs : forall xs (x : Z),
  In x xs ->
  xs <> [] ->
  In [x] (nonempty_segs xs).
Proof.
  intros xs x Hin Hne.
  unfold nonempty_segs.
  apply filter_In. split.
  - (* [x] is in segs xs *)
    destruct (elem_in_some_tail x xs Hin) as [ys Hin_tail].
    apply (singleton_from_tail x ys xs Hin_tail).
  - (* [x] is nonempty *)
    simpl. reflexivity.
Qed.

(* Helper: fold_right Z.max when maximum element is in the list *)
Lemma fold_max_achieves_bound : forall (xs : list Z) (m init : Z),
  In m xs ->
  (forall x, In x xs -> x <= m) ->
  init <= m ->
  fold_right Z.max init xs = m.
Proof.
  intros xs m init Hin_m Hall_le Hinit_le.
  induction xs as [|x xs' IH].
  - contradiction.
  - simpl in Hin_m. destruct Hin_m as [Heq | Hin'].
    + (* m = x, so x is the max *)
      subst x. simpl.
      assert (Hfold_le: fold_right Z.max init xs' <= m).
      { assert (Hall_xs': forall z, In z xs' -> z <= m).
        { intros z Hin_z. apply Hall_le. simpl. right. exact Hin_z. }
        clear IH Hall_le. induction xs' as [|y ys IH'].
        - simpl. exact Hinit_le.
        - simpl. apply Z.max_lub.
          + apply Hall_xs'. left. reflexivity.
          + apply IH'.
            intros z Hin_z. apply Hall_xs'. right. exact Hin_z. }
      lia.
    + (* m is in xs' *)
      simpl.
      assert (Hfold_xs': fold_right Z.max init xs' = m).
      { apply IH.
        - exact Hin'.
        - intros y Hin_y. apply Hall_le. right. exact Hin_y. }
      rewrite Hfold_xs'.
      assert (Hx_le: x <= m).
      { apply Hall_le. left. reflexivity. }
      lia.
Qed.

(* Lemma: In all-nonpositive lists, the maximum subarray is a single element *)
Lemma all_nonpositive_max_is_singleton : forall xs : list Z,
  all_nonpositive xs = true ->
  xs <> [] ->
  max_subarray_sum_spec xs = max_element xs.
Proof.
  intros xs Hall Hne.
  unfold max_subarray_sum_spec.
  destruct (nonempty_segs xs) as [|seg segs'] eqn:Hsegs.
  - (* nonempty_segs xs = [] - contradicts xs <> [] *)
    (* If xs <> [], then at least singleton segments exist *)
    exfalso.
    assert (Hmax_elem: exists x, In x xs).
    { destruct xs as [|x xs']; [contradiction | exists x; left; reflexivity]. }
    destruct Hmax_elem as [x Hx_in].
    assert (Hsing: In [x] (nonempty_segs xs)).
    { apply (max_element_in_segs xs x Hx_in Hne). }
    rewrite Hsegs in Hsing. contradiction.
  - (* nonempty_segs xs = seg :: segs' *)
    (* Show that max_element is the maximum over all segment sums *)
    (* First, get max_element in the segments *)
    assert (Hmax_in: exists x, In x xs /\ max_element xs = x).
    { apply (max_element_in_list xs Hall Hne). }
    destruct Hmax_in as [x_max [Hx_max_in Hx_max_eq]].
    assert (Hsing_in: In [x_max] (nonempty_segs xs)).
    { apply (max_element_in_segs xs x_max Hx_max_in Hne). }
    (* list_sum [x_max] = x_max *)
    assert (Hsum_sing: list_sum [x_max] = x_max).
    { simpl. lia. }
    (* Every segment sum <= max_element *)
    assert (Hall_le: forall s, In s (nonempty_segs xs) -> list_sum s <= max_element xs).
    { intros s Hs_in.
      apply (segment_sum_at_most_max_element xs s Hall Hs_in Hne). }
    (* Therefore fold_right Z.max over segment sums = max_element *)
    rewrite Hx_max_eq.
    (* Need to show that x_max is the maximum in the list of sums *)
    (* Since [x_max] is in nonempty_segs and its sum is x_max *)
    (* and all other sums are <= x_max, the fold_right Z.max gives x_max *)
    (* Establish bounds before rewriting *)
    assert (Hx_max_in_sums: In x_max (map list_sum (nonempty_segs xs))).
    { apply in_map_iff.
      exists [x_max]. split.
      - exact Hsum_sing.
      - exact Hsing_in. }
    assert (Hall_sums_le: forall s, In s (map list_sum (nonempty_segs xs)) -> s <= x_max).
    { intros s Hin_s.
      apply in_map_iff in Hin_s.
      destruct Hin_s as [seg' [Heq_s Hin_seg']].
      subst s.
      assert (Hle_max: list_sum seg' <= max_element xs).
      { apply Hall_le. exact Hin_seg'. }
      rewrite Hx_max_eq in Hle_max.
      exact Hle_max. }
    (* Now apply the helper lemma *)
    (* Goal is already about seg :: segs' from the destruct at line 587 *)
    (* But hypotheses still refer to nonempty_segs xs - need to rewrite *)
    rewrite Hsegs in Hx_max_in_sums, Hall_sums_le.
    (* After simpl: Z.max (list_sum seg) (fold_right Z.max (list_sum seg) (map list_sum segs')) = x_max *)
    simpl.
    simpl in Hx_max_in_sums, Hall_sums_le.
    (* Now we have: In x_max (list_sum seg :: map list_sum segs') *)
    (* and: forall s, In s (list_sum seg :: map list_sum segs') -> s <= x_max *)
    (* Need to show: Z.max (list_sum seg) (fold_right Z.max (list_sum seg) (map list_sum segs')) = x_max *)

    (* Need to show: fold_right Z.max (list_sum seg) (map list_sum segs') = x_max *)
    (* We know x_max is in the list of sums and is an upper bound *)
    (* Case analysis: is x_max = list_sum seg, or is x_max in the tail? *)
    destruct Hx_max_in_sums as [Heq_seg | Hin_tail].
    + (* x_max = list_sum seg *)
      rewrite <- Heq_seg.
      (* Need to show: fold_right Z.max (list_sum seg) (map list_sum segs') = list_sum seg *)
      (* Since all elements in map list_sum segs' are <= list_sum seg *)
      assert (Hall_tail_le: forall y, In y (map list_sum segs') -> y <= list_sum seg).
      { intros y Hy.
        assert (Hy_le_xmax: y <= x_max).
        { apply Hall_sums_le. right. exact Hy. }
        lia. }
      clear - Hall_tail_le.
      induction (map list_sum segs') as [|z zs IH].
      * simpl. reflexivity.
      * simpl.
        rewrite IH.
        -- apply Z.max_r. apply Hall_tail_le. left. reflexivity.
        -- intros y Hy. apply Hall_tail_le. right. exact Hy.
    + (* x_max is in map list_sum segs' *)
      apply fold_max_achieves_bound.
      * exact Hin_tail.
      * intros y Hy. apply Hall_sums_le. right. exact Hy.
      * apply Hall_sums_le. left. reflexivity.
Qed.

(*
=================================================================================
LEMMAS FOR CONNECTING GFORM1 TO SPECIFICATION
=================================================================================
*)

(* Helper lemma: Finite distributes over Z.max *)
Lemma finite_max_dist : forall x y : Z,
  Finite (Z.max x y) = TropicalKadane.tropical_add (Finite x) (Finite y).
Proof.
  intros x y.
  unfold TropicalKadane.tropical_add.
  reflexivity.
Qed.

(* Helper lemma: Finite distributes over addition *)
Lemma finite_plus_dist : forall x y : Z,
  Finite (x + y) = TropicalKadane.tropical_mul (Finite x) (Finite y).
Proof.
  intros x y.
  unfold TropicalKadane.tropical_mul.
  reflexivity.
Qed.

(* Helper: xs is in inits xs *)
Lemma full_list_in_inits : forall {A : Type} (xs : list A),
  In xs (inits xs).
Proof.
  intros A xs.
  induction xs as [|x xs' IH].
  - simpl. left. reflexivity.
  - rewrite inits_cons. right. apply in_map_iff.
    exists xs'. split; [reflexivity | exact IH].
Qed.

(* Helper: xs is the first element of tails xs (when non-empty) *)
Lemma full_list_first_in_tails : forall {A : Type} (xs : list A),
  xs <> [] -> exists rest, tails xs = xs :: rest.
Proof.
  intros A xs Hne.
  destruct xs as [|x xs'].
  - contradiction.
  - rewrite tails_cons. eexists. reflexivity.
Qed.

(* Helper: full list is in segs *)
Lemma full_list_in_segs : forall {A : Type} (xs : list A),
  xs <> [] -> In xs (segs xs).
Proof.
  intros A xs Hne.
  unfold segs, compose.
  (* segs xs = concat (map inits (tails xs))
     We know xs is first in tails xs, and xs is in inits xs *)
  destruct (full_list_first_in_tails xs Hne) as [rest Htails].
  rewrite Htails.
  simpl map. simpl concat.
  (* Now goal is: In xs (inits xs ++ concat (map inits rest)) *)
  apply in_or_app. left.
  apply full_list_in_inits.
Qed.

(* Helper: full list is in nonempty_segs *)
Lemma full_list_in_nonempty_segs : forall (xs : list Z),
  xs <> [] -> In xs (nonempty_segs xs).
Proof.
  intros xs Hne.
  unfold nonempty_segs.
  apply filter_In.
  split.
  - apply full_list_in_segs. exact Hne.
  - destruct xs; [contradiction | reflexivity].
Qed.

(* Helper: fold tropical_mul on Finite = Finite of fold Z.add *)
Lemma fold_tropical_mul_finite : forall (xs : list Z),
  fold_right TropicalKadane.tropical_mul (Finite 0) (map Finite xs) = Finite (list_sum xs).
Proof.
  intros xs.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - simpl map. simpl fold_right.
    rewrite IH.
    unfold TropicalKadane.tropical_mul.
    simpl list_sum.
    reflexivity.
Qed.

(* Helper: fold tropical_add on Finite list starting with init = Finite of fold Z.max *)
Lemma fold_tropical_add_finite_general : forall (xs : list Z) (init : Z),
  fold_right TropicalKadane.tropical_add (Finite init) (map Finite xs) =
  Finite (fold_right Z.max init xs).
Proof.
  intros xs init.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - simpl map. simpl fold_right.
    rewrite IH.
    unfold TropicalKadane.tropical_add.
    reflexivity.
Qed.

(* Specialized version for non-empty lists *)
Lemma fold_tropical_add_finite : forall (x : Z) (xs : list Z) (init : Z),
  fold_right TropicalKadane.tropical_add (Finite init) (map Finite (x :: xs)) =
  Finite (fold_right Z.max init (x :: xs)).
Proof.
  intros. apply fold_tropical_add_finite_general.
Qed.

(* Helper: map distributes over concat *)
Lemma map_concat : forall {A B : Type} (f : A -> B) (xss : list (list A)),
  map f (concat xss) = concat (map (map f) xss).
Proof.
  intros A B f xss.
  induction xss as [|xs xss' IH].
  - simpl. reflexivity.
  - simpl concat. rewrite map_app. rewrite IH.
    reflexivity.
Qed.

(* Helper: map Finite distributes over inits *)
Lemma map_finite_inits : forall (xs : list Z),
  map (map Finite) (inits xs) = inits (map Finite xs).
Proof.
  intros xs.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - rewrite inits_cons.
    simpl.
    unfold compose.
    simpl.
    f_equal.
    rewrite map_map.
    rewrite <- IH.
    rewrite map_map.
    reflexivity.
Qed.

(* Helper: map Finite distributes over tails *)
Lemma map_finite_tails : forall (xs : list Z),
  map (map Finite) (tails xs) = tails (map Finite xs).
Proof.
  intros xs.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - rewrite tails_cons. simpl map.
    rewrite tails_cons.
    f_equal; exact IH.
Qed.

(* Helper: map Finite commutes with segs *)
Lemma map_finite_segs_commute : forall (xs : list Z),
  map (map Finite) (segs xs) = segs (map Finite xs).
Proof.
  intros xs.
  unfold segs, compose.
  rewrite map_concat.
  rewrite map_map.
  f_equal.
  rewrite <- map_finite_tails.
  rewrite map_map.
  apply map_ext.
  intros a.
  apply map_finite_inits.
Qed.

(* Helper: Relationship between gform1 on ExtZ and the spec *)
Lemma gform1_tropical_on_finite_list : forall xs : list Z,
  xs <> [] ->
  gform1 (A := ExtZ) (map Finite xs) =
  fold_right TropicalKadane.tropical_add NegInf (map Finite (map list_sum (segs xs))).
Proof.
  intros xs Hne.
  unfold gform1, compose.
  unfold semiring_sum, semiring_product.
  simpl.
  rewrite <- map_finite_segs_commute.
  rewrite map_map.
  f_equal.
  rewrite map_map.
  apply map_ext.
  intros seg.
  apply fold_tropical_mul_finite.
Qed.

(* Lemma: gform1 from tropical semiring computes the maximum subarray sum *)
Lemma tropical_gform1_is_max_subarray : forall xs : list Z,
  xs <> [] ->
  extZ_to_Z (gform1 (A := ExtZ) (map Finite xs)) = max_subarray_sum_spec xs.
Proof.
  intros xs Hne.
  (* Strategy: Show that gform1 on lifted list computes max over all segment sums
     Key insight:
     - gform1 = semiring_sum ∘ map semiring_product ∘ segs
     - For tropical: semiring_product = sum, semiring_sum = max
     - So gform1 computes max of sums of segments
     - This is exactly max_subarray_sum_spec (modulo empty segments)
  *)
  rewrite gform1_tropical_on_finite_list by assumption.
  (* Now need to connect fold_right tropical_add on Finites to Z.max *)
  unfold max_subarray_sum_spec.
  (* This requires handling nonempty_segs vs segs, and showing the fold
     operations are equivalent *)
Admitted.

(*
=================================================================================
MAIN CORRECTNESS THEOREM (ADMITTED - FRAMEWORK ESTABLISHED)
=================================================================================
*)

Theorem kadanes_algorithm_correct : forall xs : list Z,
  kadanes_algorithm xs = max_subarray_sum_spec xs.
Proof.
  intro xs.
  unfold kadanes_algorithm.
  destruct xs as [|x xs'].
  - (* Empty list case *)
    reflexivity.
  - (* Non-empty list *)
    destruct (all_nonpositive (x :: xs')) eqn:Hnonpos.
    + (* All nonpositive case *)
      symmetry.
      apply all_nonpositive_max_is_singleton.
      * exact Hnonpos.
      * discriminate.
    + (* Has positive elements - use semiring result *)
      (* Strategy:
         1. tropical_kadanes calls TropicalKadane.kadane_algorithm
         2. That equals extract_finite (gform8 (lift_Z xs))
         3. By max_subarray_correct: gform8 = gform1
         4. Need to show this equals max_subarray_sum_spec

         The key challenge: connecting ExtZ operations on lifted lists
         to Z operations on the original list.
      *)
      (* The core challenge: we need to prove that
         tropical_kadanes (x :: xs') = max_subarray_sum_spec (x :: xs')

         Key facts available:
         1. TropicalKadane.max_subarray_correct proves gform8 = gform1 on ExtZ lists
         2. tropical_gform1_is_max_subarray (when completed) will connect
            gform1 on lifted Z lists to max_subarray_sum_spec on Z lists
         3. all_nonpositive (x :: xs') = false means there's a positive element

         The proof requires:
         - tropical_gform1_is_max_subarray to be completed
         - A lemma showing extract_finite succeeds when there are positive elements
         - Careful handling of the lift_Z conversion

         This is a substantial remaining task that requires the infrastructure
         to be fully developed.
      *)
Admitted.

(*
=================================================================================
NOTES FOR COMPLETION
=================================================================================

To complete this file, we need to:

1. Define proper conversion between ExtZ (from TropicalKadane.v) and Z
   - extZ_to_Z : ExtZ -> Z
   - Handle NegInf appropriately (probably map to most negative value or 0)

2. Extract the actual form8 implementation from TropicalKadane.v
   - tropical_gform8 : list Z -> ExtZ
   - Wrap it: kadanes_form8 : list Z -> Z := extZ_to_Z ∘ tropical_gform8

3. Prove tropical_gform1_is_max_subarray
   - Show semiring_sum with max ≡ maximum
   - Show semiring_product with + ≡ sum
   - Show composition ≡ max sum over segments

4. Complete all_nonpositive_max_is_singleton proof
   - Show adding negative numbers decreases sum
   - Therefore optimal subarray in all-nonpositive case is singleton
   - That singleton is the maximum element

5. Complete the main theorem using the above lemmas and the proven equivalences

The beauty of this approach: We leverage the fully general semiring proof
and only need to prove the "interpretation" - that the tropical semiring
operations actually compute what we want (max of sums).
*)
