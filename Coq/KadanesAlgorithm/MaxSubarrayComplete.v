Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

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
KADANE'S ALGORITHM: CORRECTNESS PROOF VIA TROPICAL SEMIRING
=================================================================================

This file proves that Kadane's algorithm correctly computes the maximum subarray sum.

ALGORITHM:
  kadanes_algorithm : list Z → Z
  Computes the maximum sum among all non-empty contiguous subarrays.

SPECIFICATION:
  max_subarray_sum_spec : list Z → Z
  The maximum value of list_sum over all non-empty segments.

MAIN THEOREM:
  kadanes_algorithm = max_subarray_sum_spec

PROOF STRUCTURE:
  The algorithm handles two cases:
  1. All-nonpositive inputs: Returns the maximum single element
  2. Otherwise: Uses the tropical semiring formulation (gform8)

  The proof connects the efficient algorithm (gform8) to the specification
  via the generalized semiring framework from KadanesAlgorithm.v.
*)

(*
=================================================================================
SPECIFICATION
=================================================================================
*)

(* Sum of a list of integers *)
Fixpoint list_sum (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: xs' => x + list_sum xs'
  end.

(* Non-empty segments (contiguous subarrays) of a list *)
Definition nonempty_segs (xs : list Z) : list (list Z) :=
  filter (fun seg => match seg with [] => false | _ => true end) (segs xs).

(* Maximum subarray sum: max { sum(seg) | seg ∈ nonempty_segs(xs) } *)
Definition max_subarray_sum_spec (xs : list Z) : Z :=
  match nonempty_segs xs with
  | [] => 0
  | seg :: rest => fold_right Z.max (list_sum seg) (map list_sum rest)
  end.

(*
=================================================================================
TROPICAL SEMIRING CONVERSION
=================================================================================
*)

(* Extract integer from ExtZ (extended integers with -∞) *)
Definition extZ_to_Z (x : ExtZ) : Z :=
  match x with
  | NegInf => 0
  | Finite z => z
  end.

Definition Z_to_extZ (z : Z) : ExtZ := Finite z.

(* Extract result from TropicalKadane's option type *)
Definition tropical_kadanes (xs : list Z) : Z :=
  match KadanesAlgorithm.TropicalKadane.kadane_algorithm xs with
  | Some z => z
  | None => 0
  end.

(*
=================================================================================
KADANE'S ALGORITHM
=================================================================================
*)

(* Test if all elements are ≤ 0 *)
Fixpoint all_nonpositive (xs : list Z) : bool :=
  match xs with
  | [] => true
  | x :: xs' => (x <=? 0) && all_nonpositive xs'
  end.

(* Maximum element in a list *)
Fixpoint max_element (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | [x] => x
  | x :: xs' => Z.max x (max_element xs')
  end.

(* Kadane's algorithm: maximum subarray sum *)
Definition kadanes_algorithm (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | _ =>
      if all_nonpositive xs
      then max_element xs
      else tropical_kadanes xs
  end.

(*
=================================================================================
CORRECTNESS PROOF
=================================================================================

Main theorem:
  kadanes_algorithm = max_subarray_sum_spec

Proof by cases on the input list:

1. Empty list: Both sides return 0

2. All elements ≤ 0: The maximum subarray is a singleton containing the
   maximum element (adding more elements decreases the sum)

3. Has positive elements: The tropical semiring formulation (gform8) computes
   the correct result. This follows from:
   - gform8 = gform1 (proven in KadanesAlgorithm.v)
   - gform1 computes max_subarray_sum_spec (proven below)

The key: In the tropical semiring, "sum of products" becomes "max of sums",
so gform1 directly expresses the maximum subarray specification.
*)

(*
=================================================================================
LEMMAS FOR ALL-NONPOSITIVE CASE
=================================================================================
*)

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

(* Helper: when not all nonpositive, there exists a positive segment sum *)
Lemma exists_positive_segment_sum : forall xs : list Z,
  xs <> [] ->
  all_nonpositive xs = false ->
  exists seg, In seg (segs xs) /\ list_sum seg > 0.
Proof.
  intros xs Hne Hnotall.
  (* all_nonpositive xs = false means there exists a positive element *)
  (* Find the positive element - it forms a positive singleton segment *)
  induction xs as [|x xs' IH].
  - contradiction.
  - simpl in Hnotall.
    apply Bool.andb_false_iff in Hnotall.
    destruct Hnotall as [Hxpos | Hxs'pos].
    + (* x > 0 *)
      apply Z.leb_gt in Hxpos.
      exists [x].
      split.
      * (* [x] is in segs (x :: xs') *)
        unfold segs, compose.
        apply in_concat.
        exists (inits (x :: xs')).
        split.
        -- apply in_map.
           rewrite tails_cons.
           simpl. left. reflexivity.
        -- (* [x] is in inits (x :: xs') *)
           rewrite inits_cons.
           (* inits (x :: xs') = [] :: map (cons x) (inits xs') *)
           (* [x] is in this list, specifically [x] = cons x [] and [] is in inits xs' *)
           simpl. right.
           apply in_map_iff.
           exists [].
           split.
           ++ reflexivity.
           ++ (* [] is in inits xs' - inits always contains [] *)
              destruct xs' as [|y ys].
              ** (* inits [] = [[]] *)
                 unfold inits. simpl. left. reflexivity.
              ** (* inits (y :: ys) = [] :: ... *)
                 rewrite inits_cons. simpl. left. reflexivity.
      * simpl. lia.
    + (* all_nonpositive xs' = false *)
      destruct xs' as [|y ys].
      * (* xs' = [], so Hxs'pos is all_nonpositive [] = false, but all_nonpositive [] = true *)
        simpl in Hxs'pos. discriminate.
      * (* xs' = y :: ys, IH applies *)
        assert (Hne': y :: ys <> []) by discriminate.
        specialize (IH Hne' Hxs'pos).
        destruct IH as [seg [Hin Hpos]].
        exists seg.
        split.
        -- (* seg is in segs (x :: y :: ys) *)
           unfold segs, compose in *.
           apply in_concat in Hin.
           destruct Hin as [lst [Hin_tails Hin_inits]].
           apply in_concat.
           exists lst.
           split.
           ++ (* lst is in map inits (tails (y :: ys)),
                 need to show it's in map inits (tails (x :: y :: ys)) *)
              (* tails (x :: y :: ys) = (x :: y :: ys) :: tails (y :: ys) *)
              rewrite tails_cons.
              simpl. right.
              exact Hin_tails.
           ++ exact Hin_inits.
        -- exact Hpos.
Qed.

(* Helper: segs includes the empty list *)
Lemma nil_in_segs : forall {A : Type} (xs : list A),
  In [] (segs xs).
Proof.
  intros A xs.
  unfold segs, compose.
  apply in_concat.
  exists (inits []).
  split.
  - apply in_map.
    destruct xs as [|x xs'].
    + unfold tails, compose. simpl. left. reflexivity.
    + rewrite tails_cons. simpl. right.
      clear x. induction xs' as [|y ys IH].
      * unfold tails, compose. simpl. left. reflexivity.
      * rewrite tails_cons. simpl. right. exact IH.
  - unfold inits. simpl. left. reflexivity.
Qed.

(* Note: The empty list [] appears MULTIPLE times in segs xs (once per tail),
   so we cannot split segs into before ++ [[]] ++ after with only one [].
   This lemma is unused and has an incorrect statement. We remove it. *)
(* Lemma segs_split_empty : forall (xs : list Z),
  exists before after,
    segs xs = before ++ [[]] ++ after /\
    (forall seg, In seg before -> seg <> []) /\
    (forall seg, In seg after -> seg <> []).
Proof.
  (* This statement is incorrect - [] appears multiple times in segs *)
Admitted. *)
Lemma nonempty_segs_removes_empty : forall (xs : list Z),
  forall seg, In seg (nonempty_segs xs) <-> (In seg (segs xs) /\ seg <> []).
Proof.
  intros xs seg.
  unfold nonempty_segs.
  rewrite filter_In.
  split.
  - intros [Hin Hpred].
    split; [exact Hin |].
    destruct seg; [discriminate | discriminate].
  - intros [Hin Hne].
    split; [exact Hin |].
    destruct seg; [contradiction | reflexivity].
Qed.

(* Helper: fold_right Z.max is associative/commutative in a specific sense *)
Lemma fold_max_cons_swap : forall (x y : Z) (ys : list Z),
  Z.max x (fold_right Z.max y ys) = Z.max y (fold_right Z.max x ys).
Proof.
  intros x y ys.
  revert x y.
  induction ys as [|z zs IH].
  - intros x y. simpl. apply Z.max_comm.
  - intros x y.
    simpl.
    (* Goal: Z.max x (Z.max z (fold_right Z.max y zs)) = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    (* Use associativity to rearrange *)
    rewrite Z.max_assoc.
    (* Now: Z.max (Z.max x z) (fold_right Z.max y zs) = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    rewrite (Z.max_comm x z).
    (* Now: Z.max (Z.max z x) (fold_right Z.max y zs) = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    rewrite <- Z.max_assoc.
    (* Now: Z.max z (Z.max x (fold_right Z.max y zs)) = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    rewrite (IH x y).
    (* Now: Z.max z (Z.max y (fold_right Z.max x zs)) = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    (* Swap z and (Z.max y ...) using commutativity *)
    rewrite (Z.max_comm z (Z.max y (fold_right Z.max x zs))).
    (* Now: Z.max (Z.max y (fold_right Z.max x zs)) z = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    (* Apply backward associativity: Z.max (Z.max a b) c = Z.max a (Z.max b c) *)
    rewrite <- (Z.max_assoc y (fold_right Z.max x zs) z).
    (* Now: Z.max y (Z.max (fold_right Z.max x zs) z) = Z.max y (Z.max z (fold_right Z.max x zs)) *)
    f_equal.
    apply Z.max_comm.
Qed.

(* Helper: fold_right tropical_add on non-empty list of Finites *)
Lemma fold_tropical_add_finite_nonempty : forall (x : Z) (xs : list Z),
  fold_right TropicalKadane.tropical_add NegInf (map Finite (x :: xs)) =
  Finite (fold_right Z.max x xs).
Proof.
  intros x xs.
  induction xs as [|y ys IH] in x |- *.
  - simpl. unfold TropicalKadane.tropical_add. reflexivity.
  - change (fold_right TropicalKadane.tropical_add NegInf (map Finite (x :: y :: ys)))
      with (TropicalKadane.tropical_add (Finite x)
             (fold_right TropicalKadane.tropical_add NegInf (map Finite (y :: ys)))).
    rewrite IH.
    unfold TropicalKadane.tropical_add.
    f_equal.
    (* Goal: Z.max x (fold_right Z.max y ys) = fold_right Z.max x (y :: ys) *)
    simpl.
    (* Goal: Z.max x (fold_right Z.max y ys) = Z.max y (fold_right Z.max x ys) *)
    (* This is exactly fold_max_cons_swap! *)
    apply fold_max_cons_swap.
Qed.

(* Helper: segs of non-empty list is non-empty *)
Lemma segs_nonempty : forall {A : Type} (xs : list A),
  xs <> [] -> segs xs <> [].
Proof.
  intros A xs Hne.
  unfold segs, compose.
  destruct xs as [|x xs'].
  - contradiction.
  - rewrite tails_cons.
    simpl concat.
    discriminate.
Qed.

(* Helper: map list_sum (segs xs) is non-empty when xs is *)
Lemma map_list_sum_segs_nonempty : forall (xs : list Z),
  xs <> [] -> map list_sum (segs xs) <> [].
Proof.
  intros xs Hne.
  assert (H: segs xs <> []) by (apply segs_nonempty; assumption).
  destruct (segs xs); [contradiction | discriminate].
Qed.

(* Helper: fold_right Z.max is bounded by maximum element *)
Lemma fold_max_le_maximum : forall (xs : list Z) (m init : Z),
  (forall x, In x xs -> x <= m) ->
  init <= m ->
  fold_right Z.max init xs <= m.
Proof.
  intros xs m init Hall init_le.
  induction xs as [|a xs' IH].
  - simpl. exact init_le.
  - simpl.
    assert (Ha_le: a <= m) by (apply Hall; left; reflexivity).
    assert (IH': fold_right Z.max init xs' <= m).
    { apply IH. intros y Hy. apply Hall. right. exact Hy. }
    apply Z.max_lub; assumption.
Qed.

(* Helper: fold_right Z.max over list containing x gives >= x *)
Lemma fold_max_ge_element : forall (xs : list Z) (x init : Z),
  In x xs ->
  fold_right Z.max init xs >= x.
Proof.
  intros xs x init Hin.
  induction xs as [|a xs' IH].
  - contradiction.
  - simpl in Hin. simpl. destruct Hin as [Heq | Hin'].
    + subst. lia.
    + assert (IH': fold_right Z.max init xs' >= x) by (apply IH; exact Hin').
      lia.
Qed.

(* Helper: when max element m is in list and is maximum, fold gives m *)
Lemma fold_max_is_maximum : forall (xs : list Z) (m init : Z),
  In m xs ->
  (forall x, In x xs -> x <= m) ->
  init <= m ->
  fold_right Z.max init xs = m.
Proof.
  intros xs m init Hin Hall init_le.
  induction xs as [|a xs' IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* m = a *)
      subst a. simpl.
      assert (Hfold_le: fold_right Z.max init xs' <= m).
      { apply fold_max_le_maximum; [|exact init_le].
        intros y Hy. apply Hall. right. exact Hy. }
      lia.
    + (* m in xs' *)
      simpl.
      assert (Ha_le: a <= m) by (apply Hall; left; reflexivity).
      assert (IH': fold_right Z.max init xs' = m).
      { apply IH.
        * exact Hin'.
        * intros y Hy. apply Hall. right. exact Hy. }
      lia.
Qed.

(* Helper: Every nonempty segment sum appears in all segment sums *)
Lemma nonempty_sums_subset_all_sums : forall (xs : list Z) (n : Z),
  In n (map list_sum (nonempty_segs xs)) ->
  In n (map list_sum (segs xs)).
Proof.
  intros xs n Hin.
  apply in_map_iff in Hin.
  destruct Hin as [seg [Hsum Hin_seg]].
  apply in_map_iff.
  exists seg.
  split; [exact Hsum |].
  apply nonempty_segs_removes_empty in Hin_seg.
  destruct Hin_seg as [Hin_segs _].
  exact Hin_segs.
Qed.

(* Helper: fold_right Z.max always returns an element from the nonempty list *)
Lemma fold_max_in_list : forall (init : Z) (xs : list Z),
  In (fold_right Z.max init xs) (init :: xs).
Proof.
  intros init xs.
  induction xs as [|x xs' IH].
  - simpl. left. reflexivity.
  - simpl.
    destruct (Z.max_spec x (fold_right Z.max init xs')) as [[Hle Hmax]|[Hle Hmax]];
      rewrite Hmax.
    + (* max = fold_right Z.max init xs', which is in init :: xs' by IH *)
      simpl in IH. destruct IH as [Heq|Hin].
      * left. exact Heq.
      * right. right. exact Hin.
    + (* max = x *)
      right. left. reflexivity.
Qed.

(* Lemma: gform1 from tropical semiring computes the maximum subarray sum *)
Lemma tropical_gform1_is_max_subarray : forall xs : list Z,
  xs <> [] ->
  all_nonpositive xs = false ->
  extZ_to_Z (gform1 (A := ExtZ) (map Finite xs)) = max_subarray_sum_spec xs.
Proof.
  intros xs Hne Hnotallnonpos.
  rewrite gform1_tropical_on_finite_list by assumption.
  (* Now: extZ_to_Z (fold_right tropical_add NegInf (map Finite (map list_sum (segs xs))))
          = max_subarray_sum_spec xs *)

  (* map list_sum (segs xs) is non-empty *)
  assert (Hne_sums: map list_sum (segs xs) <> []) by (apply map_list_sum_segs_nonempty; assumption).

  (* So we can destructure it *)
  destruct (map list_sum (segs xs)) as [|s ss] eqn:Hsums.
  - contradiction.
  - (* Now use fold_tropical_add_finite_nonempty *)
    rewrite fold_tropical_add_finite_nonempty.
    unfold extZ_to_Z.

    (* Now: fold_right Z.max s ss = max_subarray_sum_spec xs *)
    (* where s :: ss = map list_sum (segs xs) *)

    unfold max_subarray_sum_spec.

    (* Key insight: segs xs = nonempty_segs xs ++ [[]]
       Actually, that's not quite right - [] could be anywhere in segs.

       Better approach: show that fold_right Z.max over (map list_sum (segs xs))
       equals fold_right Z.max over (map list_sum (nonempty_segs xs)) when the
       max is >= 0 (because [] contributes 0).

       Since we don't know if max >= 0, we need a more general result.
       Actually, let's use that [] is in segs xs, so 0 is in the list of sums.
    *)

    (* Key insight: Since all_nonpositive xs = false, there exists a positive segment sum.
       map list_sum (segs xs) includes 0 (from []) and all nonempty segment sums.
       map list_sum (nonempty_segs xs) has just the nonempty segment sums.

       The max over the first list equals the max over the second when there's a positive value,
       because max(0, ..., positive, ...) = max(..., positive, ...).
    *)

    (* Get the positive segment *)
    assert (Hpos_seg: exists seg, In seg (segs xs) /\ list_sum seg > 0).
    { apply exists_positive_segment_sum; assumption. }
    destruct Hpos_seg as [pos_seg [Hin_pos Hsum_pos]].

    (* 0 is in map list_sum (segs xs) because [] is in segs xs and list_sum [] = 0 *)
    assert (H0_in: In 0 (map list_sum (segs xs))).
    { apply in_map_iff.
      exists [].
      split.
      - reflexivity.  (* list_sum [] = 0 *)
      - apply nil_in_segs. }

    (* list_sum pos_seg is in map list_sum (segs xs) *)
    assert (Hpos_sum_in: In (list_sum pos_seg) (map list_sum (segs xs))).
    { apply in_map. exact Hin_pos. }

    (* The max of map list_sum (segs xs) is >= list_sum pos_seg > 0 *)
    (* Therefore max >= 0, so including 0 doesn't change the max *)

    (* Actually, let me use a more computational approach.
       We know:
       1. s :: ss = map list_sum (segs xs)
       2. fold_right Z.max s ss computes the max of this list
       3. nonempty_segs xs contains all segments except []
       4. So map list_sum (nonempty_segs xs) has all the same values except 0
       5. If the max is > 0, then removing 0 doesn't change it
       6. If the max is 0, then... but we know there's a positive value, so max > 0
    *)

    (* Strategy: Find the maximum segment sum m, show it's > 0, and use fold_max_is_maximum *)

    (* The maximum of map list_sum (segs xs) is some value m *)
    (* We know list_sum pos_seg > 0 is in the list, so m >= list_sum pos_seg > 0 *)

    (* First, show that fold_right Z.max s ss >= list_sum pos_seg *)
    (* Since list_sum pos_seg is in s :: ss, the fold >= it *)
    assert (Hfold_ge: fold_right Z.max s ss >= list_sum pos_seg).
    { assert (Hin': In (list_sum pos_seg) (s :: ss)) by (rewrite <- Hsums; exact Hpos_sum_in).
      simpl in Hin'. destruct Hin' as [Heq | Hin_ss].
      * subst.
        (* After subst, s = list_sum pos_seg, so we need:
           fold_right Z.max (list_sum pos_seg) ss >= list_sum pos_seg *)
        clear Hpos_sum_in. clear H0_in. clear Hsum_pos. clear Hin_pos. clear Hsums. clear Hne_sums.
        clear Hnotallnonpos. clear Hne. clear xs.
        (* Now prove the general fact *)
        induction ss as [|s' ss' IH].
        -- (* ss = [] *)
           simpl. lia.
        -- (* ss = s' :: ss' *)
           (* Goal: Z.max s' (fold_right Z.max (list_sum pos_seg) ss') >= list_sum pos_seg *)
           simpl.
           (* By IH, fold_right Z.max (list_sum pos_seg) ss' >= list_sum pos_seg *)
           (* So Z.max s' (fold ...) >= fold ... >= list_sum pos_seg *)
           assert (Hfold: fold_right Z.max (list_sum pos_seg) ss' >= list_sum pos_seg) by exact IH.
           lia.
      * apply fold_max_ge_element. exact Hin_ss. }

    (* So fold_right Z.max s ss > 0 *)
    assert (Hfold_pos: fold_right Z.max s ss > 0) by lia.

    (* Now we need to show this equals max_subarray_sum_spec xs *)
    (* For nonempty_segs, we have a similar structure *)
    destruct (nonempty_segs xs) as [|seg rest] eqn:Hnonempty.
    + (* nonempty_segs xs = [] - impossible since xs <> [] *)
      exfalso.
      assert (Hfull: In xs (nonempty_segs xs)).
      { apply full_list_in_nonempty_segs. exact Hne. }
      rewrite Hnonempty in Hfull. contradiction.
    + (* nonempty_segs xs = seg :: rest *)
      simpl.

      (* Both folds compute the maximum. Since they're over related lists
         (one has 0 added, one doesn't), and the max is > 0, they should be equal.

         The key: the maximum segment sum appears in both lists (since it's non-empty,
         it's in nonempty_segs, and all nonempty_segs are in segs).

         By fold_max_is_maximum, if the same maximum m appears in both lists,
         both folds equal m.
      *)

      (* Key insight: We need to prove that
           fold_right Z.max s ss = fold_right Z.max (list_sum seg) (map list_sum rest)
         where s :: ss = map list_sum (segs xs)
         and   seg :: rest = nonempty_segs xs *)

      (* Rewrite to use the equation *)
      assert (Heq_sums: s :: ss = map list_sum (segs xs)) by (symmetry; exact Hsums).
      assert (Heq_nonempty: seg :: rest = nonempty_segs xs) by (symmetry; exact Hnonempty).

      (* The key observation: Every element in map list_sum (nonempty_segs xs) is in
         map list_sum (segs xs), and the only additional element in the latter is 0.
         Since fold_right Z.max s ss > 0, adding 0 to the list doesn't change the max. *)

      (* Actually, let me prove this more carefully using a permutation-like argument.
         The issue is that segs xs and nonempty_segs xs differ by exactly [] *)

      (* Cleaner approach: Show that the maximum element is the same in both lists,
         and apply fold_max_is_maximum to both. *)

      (* Strategy: The maximum value in both lists is the same, call it m.
         We'll show both folds equal m by proving:
         1. m is in both lists
         2. m is >= all elements in both lists
         Then apply fold_max_is_maximum to each *)

      (* First, establish what we're comparing *)
      set (all_sums := s :: ss).
      set (nonempty_sums := list_sum seg :: map list_sum rest).

      (* We have all_sums = map list_sum (segs xs) by Hsums *)
      assert (Hall_sums_eq: all_sums = map list_sum (segs xs)) by (unfold all_sums; symmetry; exact Hsums).

      (* And nonempty_sums = map list_sum (nonempty_segs xs) *)
      assert (Hnonempty_sums_eq: nonempty_sums = map list_sum (nonempty_segs xs)).
      { unfold nonempty_sums.
        rewrite Hnonempty.
        reflexivity. }

      (* Let m = fold_right Z.max s ss (the max over all_sums) *)
      set (m := fold_right Z.max s ss).

      (* We have m > 0 *)
      assert (Hm_pos: m > 0) by (unfold m; exact Hfold_pos).

      (* Since list_sum pos_seg is in all_sums and m >= it, and m is the fold value *)
      (* Also, list_sum pos_seg is a nonempty segment sum *)
      assert (Hpos_ne: pos_seg <> []).
      { intro Hcontra. subst. simpl in Hsum_pos. lia. }

      assert (Hpos_in_nonempty: In (list_sum pos_seg) nonempty_sums).
      { rewrite Hnonempty_sums_eq.
        apply in_map_iff.
        exists pos_seg.
        split; [reflexivity |].
        apply nonempty_segs_removes_empty.
        split; [exact Hin_pos | exact Hpos_ne]. }

      (* Now I'll show that m is also the maximum of nonempty_sums *)
      (* Claim: fold_right Z.max (list_sum seg) (map list_sum rest) = m *)

      (* Key insight: m is the max of all_sums. All elements of nonempty_sums are in all_sums.
         So m >= all elements of nonempty_sums. Also, since m > 0 and 0 is in all_sums,
         m must come from some nonempty segment (since only [] gives 0).
         Therefore m is in nonempty_sums. *)

      (* The maximum value must come from a nonempty segment since m > 0 and only [] sums to 0 *)
      assert (Hm_from_nonempty: exists seg_m, In seg_m (nonempty_segs xs) /\ list_sum seg_m = m).
      { (* Since m is the max of all_sums and m > 0, it can't be the sum of [] *)
        (* We know m is the fold of all_sums. We need to find which segment gives this maximum. *)
        (* Key: m must be in all_sums (it's the max of a nonempty list) *)
        (* Since m > 0 and list_sum [] = 0, the segment with sum m must be nonempty *)

        (* First, show that m is actually in all_sums *)
        (* Actually, this is tricky - fold_right Z.max doesn't guarantee m is IN the list,
           only that it's >= all elements. But we know list_sum pos_seg is in the list
           and m >= list_sum pos_seg. *)

        (* Different approach: We know m = fold_right Z.max s ss where s :: ss = map list_sum (segs xs).
           This means m is either s or the max of ss. Either way, m is in s :: ss. *)

        (* Let me use a helper: the fold equals one of the elements when the list is nonempty *)
        assert (Hm_in_all: In m all_sums).
        { unfold m, all_sums.
          apply fold_max_in_list. }

        (* Now m is in all_sums = map list_sum (segs xs) *)
        rewrite Hall_sums_eq in Hm_in_all.
        apply in_map_iff in Hm_in_all.
        destruct Hm_in_all as [seg_m [Hsum_m Hin_m]].

        (* seg_m is a segment with sum m. Since m > 0, seg_m <> [] *)
        assert (Hseg_ne: seg_m <> []).
        { intro Hcontra. subst. simpl in Hsum_m. lia. }

        (* Therefore seg_m is in nonempty_segs xs *)
        exists seg_m.
        split.
        - apply nonempty_segs_removes_empty. split; assumption.
        - exact Hsum_m. }

      (* Now use this to complete the proof *)
      destruct Hm_from_nonempty as [seg_m [Hin_seg_m Hsum_m]].

      (* m is in nonempty_sums *)
      assert (Hm_in_nonempty: In m nonempty_sums).
      { rewrite Hnonempty_sums_eq.
        apply in_map_iff.
        exists seg_m.
        split.
        - rewrite <- Hsum_m. reflexivity.
        - exact Hin_seg_m. }

      (* Now both folds equal m by showing:
         1. m is in both lists
         2. m >= all elements in both lists *)

      (* m >= all elements in all_sums (by definition of fold_right Z.max) *)
      assert (Hm_max_all: forall y, In y all_sums -> y <= m).
      { intros y Hy.
        unfold m, all_sums in *.
        (* fold_right Z.max s ss >= all elements of s :: ss *)
        simpl in Hy. destruct Hy as [Heq | Hin].
        - (* y = s *)
          subst.
          destruct ss as [|s' ss'].
          + simpl. unfold m. simpl. lia.
          + unfold m. simpl.
            (* y <= Z.max s' (fold_right Z.max y ss') *)
            (* Since fold_right Z.max y ss' >= y, and Z.max takes the larger of s' and fold....,
               the result is >= y *)
            transitivity (fold_right Z.max y ss').
            * clear. induction ss' as [|s'' ss'' IH].
              -- simpl. lia.
              -- simpl. transitivity (fold_right Z.max y ss'').
                 ++ exact IH.
                 ++ apply Z.le_max_r.
            * apply Z.le_max_r.
        - (* y is in ss *)
          assert (Hge: fold_right Z.max s ss >= y).
          { apply fold_max_ge_element with (init := s).
            exact Hin. }
          lia. }

      (* m >= all elements in nonempty_sums (since nonempty_sums ⊆ all_sums) *)
      assert (Hm_max_nonempty: forall z, In z nonempty_sums -> z <= m).
      { intros z Hz.
        apply Hm_max_all.
        rewrite Hnonempty_sums_eq in Hz.
        rewrite Hall_sums_eq.
        apply nonempty_sums_subset_all_sums.
        exact Hz. }

      (* Therefore fold_right Z.max (list_sum seg) (map list_sum rest) = m *)

      (* First, show that fold_right Z.max (list_sum seg) (map list_sum rest) = m *)
      assert (Hfold_nonempty_eq_m: fold_right Z.max (list_sum seg) (map list_sum rest) = m).
      { (* We know In m nonempty_sums *)
        unfold nonempty_sums in Hm_in_nonempty.
        simpl in Hm_in_nonempty.
        destruct Hm_in_nonempty as [Heq_m | Hin_m].
        - (* Case 1: m = list_sum seg *)
          (* Then fold_right Z.max (list_sum seg) (map list_sum rest) = list_sum seg = m *)
          (* Since m >= all elements in nonempty_sums and m = list_sum seg, we have
             fold_right Z.max (list_sum seg) (map list_sum rest) = list_sum seg *)
          symmetry in Heq_m.
          rewrite <- Heq_m.
          (* Goal: fold_right Z.max (list_sum seg) (map list_sum rest) = list_sum seg *)
          assert (Hfold_le: fold_right Z.max (list_sum seg) (map list_sum rest) <= list_sum seg).
          { apply fold_max_le_maximum.
            - intros z Hz.
              assert (Hz_le_m: z <= m).
              { apply Hm_max_nonempty.
                unfold nonempty_sums. simpl. right. exact Hz. }
              (* Heq_m : m = list_sum seg, so z <= m = list_sum seg *)
              lia.
            - lia. }
          (* Since fold_right ... <= list_sum seg, and it's also >= list_sum seg (by fold property), they're equal *)
          (* fold_right Z.max init xs always returns a value >= init *)
          (* This follows because fold_right Z.max init (x::xs) = Z.max x (fold_right Z.max init xs) >= init *)
          destruct (map list_sum rest) as [|r rs] eqn:Hrest_eq.
          + (* rest is empty, so fold_right Z.max (list_sum seg) [] = list_sum seg *)
            simpl. reflexivity.
          + (* rest is nonempty, so fold_right Z.max (list_sum seg) (r::rs) = Z.max r (fold...) >= list_sum seg *)
            (* We have Hfold_le, and also the fold >= list_sum seg by Z.max properties *)
            simpl.
            assert (Hfold_ge_seg: Z.max r (fold_right Z.max (list_sum seg) rs) >= list_sum seg).
            { (* Z.max r x >= x for any r and x, and fold_right Z.max (list_sum seg) rs >= list_sum seg *)
              (* By fold property: fold_right Z.max init xs >= init *)
              assert (Hfold_init: forall init xs, fold_right Z.max init xs >= init).
              { clear. intros init xs. induction xs as [|x xs' IH].
                - simpl. lia.
                - simpl. assert (H := Z.le_max_r x (fold_right Z.max init xs')). lia. }
              assert (H1: fold_right Z.max (list_sum seg) rs >= list_sum seg).
              { apply Hfold_init. }
              assert (H2 := Z.le_max_r r (fold_right Z.max (list_sum seg) rs)). lia. }
            simpl in Hfold_le.
            apply Z.le_antisymm.
            * rewrite Heq_m.
              exact Hfold_le.
            * apply Z.ge_le_iff.
              rewrite Heq_m.
              exact Hfold_ge_seg.
        - (* Case 2: m is in map list_sum rest *)
          apply fold_max_is_maximum.
          + exact Hin_m.
          + intros z Hz. apply Hm_max_nonempty.
            unfold nonempty_sums. simpl. right. exact Hz.
          + apply Hm_max_nonempty.
            unfold nonempty_sums. simpl. left. reflexivity. }

      (* Now we have both folds equal m *)
      unfold m in Hfold_nonempty_eq_m.
      symmetry.
      exact Hfold_nonempty_eq_m.
Qed.

(*
=================================================================================
MAIN CORRECTNESS THEOREM
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
      unfold tropical_kadanes.
      unfold KadanesAlgorithm.TropicalKadane.kadane_algorithm.
      unfold KadanesAlgorithm.TropicalKadane.extract_finite.
      unfold KadanesAlgorithm.TropicalKadane.max_subarray_sum.
      unfold KadanesAlgorithm.TropicalKadane.lift_Z.

      (* Use gform8 = gform1 *)
      rewrite <- Generalized_Kadane_Correctness.

      (* Apply tropical_gform1_is_max_subarray *)
      assert (H := tropical_gform1_is_max_subarray (x :: xs')).
      assert (Hne: x :: xs' <> []) by discriminate.
      specialize (H Hne Hnonpos).

      (* Match on gform1 to extract the result *)
      unfold extZ_to_Z in H.
      destruct (gform1 (map Finite (x :: xs'))) eqn:Hgform.
      * simpl. simpl in H. symmetry. symmetry in H. exact H.
      * simpl. simpl in H. symmetry. symmetry in H. exact H.
Qed.

(*
=================================================================================
SUMMARY
=================================================================================

This file proves Kadane's algorithm correct via the tropical semiring framework.

The proof leverages the generalized semiring-based derivation from
KadanesAlgorithm.v, requiring only an "interpretation" proof that tropical
semiring operations (max as ⊕, addition as ⊗) correctly compute maximum
subarray sums.

Key theorems:
  - tropical_gform1_is_max_subarray: gform1 computes max subarray sum
  - all_nonpositive_max_is_singleton: all-nonpositive optimal subarray is a singleton
  - kadanes_algorithm_correct: kadanes_algorithm = max_subarray_sum_spec
*)

(*
=================================================================================
EXAMPLE USAGE
=================================================================================
*)

(* Example 1: Array with positive sum *)
Example kadane_example1 : kadanes_algorithm [(-2) ; 1 ; (-3) ; 4 ; (-1) ; 2 ; 1 ; (-5) ; 4] = 6.
Proof. reflexivity. Qed.

(* Example 2: All negative array *)
Example kadane_example2 : kadanes_algorithm [(-2) ; (-3) ; (-1) ; (-5)] = (-1).
Proof. reflexivity. Qed.

(* Example 3: Mixed with zero *)
Example kadane_example3 : kadanes_algorithm [(-1) ; 0 ; (-2) ; 3 ; 1 ; (-1)] = 4.
Proof. reflexivity. Qed.

(* Example 4: All positive *)
Example kadane_example4 : kadanes_algorithm [1 ; 2 ; 3 ; 4] = 10.
Proof. reflexivity. Qed.

(* Example 5: Single element *)
Example kadane_example5 : kadanes_algorithm [5] = 5.
Proof. reflexivity. Qed.

(* Example 6: Empty array *)
Example kadane_example6 : kadanes_algorithm [] = 0.
Proof. reflexivity. Qed.
