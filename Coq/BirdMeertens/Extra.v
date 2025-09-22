Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.FunctionLemmas.
Require Import BirdMeertens.TailsMonoid.
Require Import BirdMeertens.MajorLemmas.
Require Import BirdMeertens.Lemmas.
Require Import CoqUtilLib.ListFunctions.

Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zmax.

Open Scope Z_scope.

(* Extended integers with negative infinity for proper max monoid *)
(*
   The Z_plus_neg_inf type addresses the fundamental issue with your original
   fold_right_max_returns_max lemma. The problem was that fold_right Z.max 0
   doesn't form a proper monoid because:

   1. With identity 0, the result might not be in the original list
      (e.g., [-5; -3; -1] gives max = 0, but 0 ∉ [-5; -3; -1])

   2. The lemma required both non-negativity constraints AND membership,
      making it impossible to prove in the general case.

   With Z_plus_neg_inf and NegInf as the proper identity:
   - fold_right_max_inf ALWAYS returns an element from the list (when non-empty)
   - No non-negativity constraints needed
   - Works for any list of integers including all-negative lists

   Key lemmas:
   - fold_right_max_inf_in: Result is always in the original list
   - fold_right_max_inf_returns_max: General version without non-negativity
*)
Inductive Z_plus_neg_inf : Type :=
  | Z_val : Z -> Z_plus_neg_inf
  | NegInf : Z_plus_neg_inf.

(* Comparison for Z_plus_neg_inf *)
Definition Z_plus_neg_inf_le (x y : Z_plus_neg_inf) : Prop :=
  match x, y with
  | NegInf, _ => True
  | Z_val _, NegInf => False
  | Z_val a, Z_val b => a <= b
  end.

(* Max operation for Z_plus_neg_inf *)
Definition Z_plus_neg_inf_max (x y : Z_plus_neg_inf) : Z_plus_neg_inf :=
  match x, y with
  | NegInf, y => y
  | x, NegInf => x
  | Z_val a, Z_val b => Z_val (Z.max a b)
  end.

Notation "x <=_inf y" := (Z_plus_neg_inf_le x y) (at level 70).
Notation "x ∨_inf y" := (Z_plus_neg_inf_max x y) (at level 50, left associativity).

(* Membership for Z_plus_neg_inf in list of regular integers *)
Definition Z_plus_neg_inf_In (x : Z_plus_neg_inf) (xs : list Z) : Prop :=
  match x with
  | NegInf => False
  | Z_val z => In z xs
  end.

(* Fold right max operation for Z_plus_neg_inf *)
Definition fold_right_max_inf (xs : list Z) : Z_plus_neg_inf :=
  fold_right Z_plus_neg_inf_max NegInf (map Z_val xs).

(* Basic properties of Z_plus_neg_inf operations *)

Lemma Z_plus_neg_inf_max_comm : forall x y : Z_plus_neg_inf, x ∨_inf y = y ∨_inf x.
Proof.
  intros [a|] [b|]; simpl; try reflexivity.
  f_equal. apply Z.max_comm.
Qed.

Lemma Z_plus_neg_inf_max_assoc : forall x y z : Z_plus_neg_inf,
  (x ∨_inf y) ∨_inf z = x ∨_inf (y ∨_inf z).
Proof.
  intros [a|] [b|] [c|]; simpl; try reflexivity.
  f_equal.
  (* Use Z.max associativity *)
  rewrite Z.max_assoc.
  reflexivity.
Qed.

Lemma Z_plus_neg_inf_max_id_l : forall x : Z_plus_neg_inf, NegInf ∨_inf x = x.
Proof.
  intros [a|]; reflexivity.
Qed.

Lemma Z_plus_neg_inf_max_id_r : forall x : Z_plus_neg_inf, x ∨_inf NegInf = x.
Proof.
  intros [a|]; reflexivity.
Qed.

(* Helper lemma: fold_right on non-empty list never gives NegInf *)
Lemma fold_right_max_inf_never_neginf : forall (xs : list Z),
  xs <> [] -> exists w : Z, fold_right_max_inf xs = Z_val w.
Proof.
  intros xs H_nonempty.
  induction xs as [|x xs' IH].
  - contradiction H_nonempty; reflexivity.
  - unfold fold_right_max_inf. simpl.
    destruct xs' as [|y xs''].
    + (* xs = [x] *)
      simpl. exists x. reflexivity.
    + (* xs = x :: y :: xs'' *)
      simpl.
      assert (H_tail_nonempty: y :: xs'' <> []) by discriminate.
      specialize (IH H_tail_nonempty) as [w Hw].
      unfold fold_right_max_inf in Hw. simpl in Hw.
      exists (Z.max x w).
      unfold fold_right_max_inf. simpl.
      rewrite Hw. simpl. reflexivity.
Qed.

(* Helper lemma: Z_plus_neg_inf_max of two Z_vals gives Z_val of max *)
Lemma z_plus_neg_inf_max_z_vals : forall (a b : Z),
  Z_plus_neg_inf_max (Z_val a) (Z_val b) = Z_val (Z.max a b).
Proof.
  intros a b. simpl. reflexivity.
Qed.

(* Let me prove this directly using the definition *)
Lemma max_in_list : forall (xs : list Z) (m : Z),
  xs <> [] -> fold_right_max_inf xs = Z_val m -> In m xs.
Proof.
  intros xs.
  induction xs as [|x xs' IH].
  - intros m H_contra. contradiction H_contra; reflexivity.
  - intros m H_nonempty H_fold.
    unfold fold_right_max_inf in H_fold. simpl in H_fold.
    destruct xs' as [|y xs''].
    + (* xs = [x] *)
      simpl in H_fold.
      inversion H_fold. subst.
      left. reflexivity.
    + (* xs = x :: y :: xs'' *)
      simpl in H_fold.
      (* The fold gives us Z_plus_neg_inf_max (Z_val x) (result of tail) *)
      (* We know the tail is non-empty, so it gives Z_val w for some w *)
      assert (H_tail_nonempty: y :: xs'' <> []) by discriminate.
      assert (H_tail_exists: exists w, fold_right_max_inf (y :: xs'') = Z_val w).
      { apply fold_right_max_inf_never_neginf. exact H_tail_nonempty. }
      destruct H_tail_exists as [w Hw].

      (* Rewrite the fold equation *)
      unfold fold_right_max_inf in Hw. simpl in Hw.
      rewrite Hw in H_fold.
      simpl in H_fold.
      inversion H_fold. subst.

      (* Now m = Z.max x w, and we need to prove In (Z.max x w) (x :: y :: xs'') *)
      (* Key insight: apply IH to the tail, but carefully *)
      assert (H_w_in_tail: In w (y :: xs'')).
      {
        (* Apply IH to xs' = y :: xs'' *)
        apply (IH w).
        - exact H_tail_nonempty.
        - exact Hw.
      }

      (* Case analysis on max *)
      destruct (Z_ge_lt_dec x w) as [H_x_ge_w | H_w_gt_x].
      * (* x >= w, so Z.max x w = x *)
        replace (Z.max x w) with x.
        -- left. reflexivity.
        -- symmetry. apply Z.max_l. apply Z.ge_le. exact H_x_ge_w.
      * (* w > x, so Z.max x w = w *)
        replace (Z.max x w) with w.
        -- right. exact H_w_in_tail.
        -- symmetry. apply Z.max_r. apply Z.lt_le_incl. exact H_w_gt_x.
Qed.

(* Main lemma *)
Lemma fold_right_max_inf_in : forall (xs : list Z),
  xs <> [] -> Z_plus_neg_inf_In (fold_right_max_inf xs) xs.
Proof.
  intros xs H_nonempty.

  (* By the helper lemma, fold_right_max_inf xs = Z_val m for some m *)
  assert (H_exists: exists m, fold_right_max_inf xs = Z_val m).
  { apply fold_right_max_inf_never_neginf. exact H_nonempty. }

  destruct H_exists as [m Hm].

  (* Unfold the goal *)
  unfold Z_plus_neg_inf_In.
  rewrite Hm.

  (* Now goal is: In m xs *)
  (* By the max_in_list helper lemma *)
  apply max_in_list.
  - exact H_nonempty.
  - exact Hm.
Qed.

(* Define nonNegPlus using Qle_bool to convert the proposition to a boolean *)
(* Refs:
 - form8 -> (* Refs: NONE *)
*)
(* Dual helper functions (swap fold_right↔fold_left) *)
(* Refs:
 - form4_eq_form5 -> (* Refs: NONE *)
*)
(* Refs:
 - form2_eq_form3 -> (* Refs: NONE *)
*)

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
Lemma fold_left_max_nonneg_gen :
  forall l acc, (0 <= acc)%Z ->
    (0 <= fold_left Z.max l acc)%Z.
Proof.
  induction l as [|x xs IH]; intros acc Hacc.
  - simpl. exact Hacc.
  - simpl. apply IH.
    (* show the new accumulator is ≥ 0 *)
    apply Z.le_trans with (m := acc); [exact Hacc | apply Z.le_max_l].
Qed.

(* Import Lia locally for this proof *)
Require Import Lia.

(* fold_left Z.max l 0 is always non-negative *)
Lemma fold_max_nonneg_dual : forall l : list Z,
  0 <= fold_left Z.max l 0.
Proof.
  intro l.
  (* Key insight: fold_left Z.max always starts with 0, and max(0, x) >= 0 *)
  assert (H: forall acc, 0 <= acc -> forall l', 0 <= fold_left Z.max l' acc).
  {
    intros acc H_acc l'.
    generalize dependent acc.
    induction l' as [|x xs IH]; simpl; intros acc H_acc.
    - exact H_acc.
    - apply IH. apply Z.le_trans with (m := acc); [exact H_acc | apply Z.le_max_l].
  }
  apply H. apply Z.le_refl.
Qed.

(* Main lemma: fold_left distributes over concatenation *)
Lemma fold_max_app_dual : forall l1 l2,
  fold_left Z.max (l1 ++ l2) 0 =
  Z.max (fold_left Z.max l1 0) (fold_left Z.max l2 0).
Proof.
  (* Prove using direct duality with fold_left_right_equiv *)
  intros l1 l2.
  change Z.max with (fun x y => x <|> y).
  (* Use fold_left_right_equiv to convert to fold_right *)
  rewrite fold_left_right_equiv.
  + repeat (rewrite fold_left_right_equiv).
    * apply fold_max_app.
    * intros x y z. apply Z.max_assoc.
    * intros x y. apply Z.max_comm.
    * intros x y z. apply Z.max_assoc.
    * intros x y. apply Z.max_comm.
  + intros x y z. apply Z.max_assoc.
  + intros x y. apply Z.max_comm.
Qed.

(* Instead, let's add a simple provable lemma about nonNegPlus *)
Definition distributes_over_max (op : Z -> Z -> Z) := forall s t x, op (Z.max s t) x = Z.max  (op s x) (op t x).

Lemma max_add_distributes : forall s t x,
  Z.max s t + x = Z.max (s + x) (t + x).
Proof.
  intros.
  rewrite Z.add_max_distr_r.
  reflexivity.
Qed.

(* Helper lemma: addition distributes over max *)
Lemma nonNegPlus_distributes_over_max : distributes_over_max nonNegPlus.
Proof.
  unfold distributes_over_max.
  intros s t x.
  unfold nonNegPlus.
  rewrite max_add_distributes.
  (* Case analysis on whether each sum is non-negative *)
  destruct (Z.leb 0 (s + x)) eqn:Hs, (Z.leb 0 (t + x)) eqn:Ht.
  
  (* Case 1: both s+x >= 0 and t+x >= 0 *)
  - (* Then max(s+x, t+x) >= 0, so nonNegPlus of max is the max itself *)
    (* And max(s+x, 0) = s+x and max(t+x, 0) = t+x *)
    simpl.
    assert (H_max_nonneg: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Hs. apply Z.le_trans with (m := s + x).
      exact Hs. apply Z.le_max_l. }
    rewrite H_max_nonneg.
    reflexivity.
  
  (* Case 2: s+x >= 0 but t+x < 0 *)  
  - simpl.
    (* max(s+x, t+x) = s+x since s+x >= 0 > t+x *)
    assert (H_max_pos: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Hs. rewrite Z.leb_gt in Ht.
      apply Z.le_trans with (m := s + x). exact Hs.
      apply Z.le_max_l. }
    rewrite H_max_pos.
    (* Now goal is: Z.max (s + x) (t + x) = (s + x) <|> 0 *)
    (* Since s+x >= 0 and t+x < 0, we have Z.max (s+x) (t+x) = s+x *)
    (* And s+x <|> 0 = Z.max (s+x) 0 = s+x since s+x >= 0 *)
    rewrite Z.leb_le in Hs. rewrite Z.leb_gt in Ht.
    assert (H_sx_ge_tx: s + x >= t + x). {
      apply Z.ge_le_iff.
      apply Z.le_trans with (m := 0).
      - apply Z.lt_le_incl. exact Ht.
      - exact Hs.
    }
    rewrite Z.max_l.
    + rewrite Z.max_l; [reflexivity | exact Hs].
    + apply Z.ge_le. exact H_sx_ge_tx.
  
  (* Case 3: s+x < 0 but t+x >= 0 *)
  - simpl.
    assert (H_max_pos: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_gt in Hs. rewrite Z.leb_le in Ht.
      apply Z.le_trans with (m := t + x). exact Ht.
      apply Z.le_max_r. }
    rewrite H_max_pos.
    (* Now goal is: Z.max (s + x) (t + x) = 0 <|> (t + x) *)
    (* Since s+x < 0 and t+x >= 0, we have Z.max (s+x) (t+x) = t+x *)
    (* And 0 <|> t+x = Z.max 0 (t+x) = t+x since t+x >= 0 *)
    rewrite Z.leb_gt in Hs. rewrite Z.leb_le in Ht.
    assert (H_tx_ge_sx: t + x >= s + x). {
      apply Z.ge_le_iff.
      apply Z.le_trans with (m := 0).
      - apply Z.lt_le_incl. exact Hs.
      - exact Ht.
    }
    rewrite Z.max_r.
    + rewrite Z.max_r; [reflexivity | exact Ht].
    + apply Z.ge_le. exact H_tx_ge_sx.
  
  (* Case 4: both s+x < 0 and t+x < 0 *)
  - (* Then max(s+x, t+x) < 0, so result is 0 *)
    (* And max(0, 0) = 0 *)
    simpl.
    assert (H_max_neg: Z.leb 0 (Z.max (s + x) (t + x)) = false).
    { apply Z.leb_gt. rewrite Z.leb_gt in Hs. rewrite Z.leb_gt in Ht.
      apply Z.max_lub_lt; assumption. }
    rewrite H_max_neg.
    reflexivity.
Qed.

(* First, let me establish what inits actually does step by step *)
(* 1) helper: fold_right nonNegPlus for cons *)
Lemma fold_right_nonNegPlus_cons :
  forall a l,
    fold_right nonNegPlus 0 (a :: l) = nonNegPlus a (fold_right nonNegPlus 0 l).
Proof. intros; simpl; reflexivity. Qed.

(* 2) helper: map over inits after inits_cons *)
Lemma map_fold_right_nonNegPlus_inits_cons :
  forall (a : Z) (xs : list (list Z)),
    map (fun l => fold_right nonNegPlus 0 (a :: l)) xs =
    map (fun l => nonNegPlus a (fold_right nonNegPlus 0 l)) xs.
Proof.
  intros a xs.
  apply map_ext; intros l.
  apply fold_right_nonNegPlus_cons.
Qed.

Lemma fold_right_map_nonNegPlus_commute_counterexample :
  exists a l, fold_right Z.max 0 (map (fun v => nonNegPlus a v) l) <> nonNegPlus a (fold_right Z.max 0 l).
Proof.
  exists 1%Z, [-2%Z].
  simpl. unfold nonNegPlus. compute. congruence.
Qed.

(* 3) helper: push map (cons a) inside fold_right Z.max via map_map
   (this is just a composition-of-maps step) *)
Lemma map_map_inits_cons_step :
  forall a xs,
    map (fun l => fold_right nonNegPlus 0 (a :: l)) (inits xs) =
    map (fun l => nonNegPlus a (fold_right nonNegPlus 0 l)) (inits xs).
Proof.
  intros; apply map_fold_right_nonNegPlus_inits_cons.
Qed.

Lemma fold_left_cons_Z :
  forall (xs : list Z) (x acc : Z),
    fold_left Z.add (x :: xs) acc =
    fold_left Z.add xs (acc + x).
Proof. intros; simpl; reflexivity. Qed.

Lemma scan_left_inits_general_Z :
  forall (xs : list Z) (acc : Z),
    scan_left Z.add xs acc =
    map (fun ys : list Z => fold_left Z.add ys acc) (inits xs).
Proof.
  induction xs as [| x xs' IH]; intros acc.
  - simpl. reflexivity.
  - simpl scan_left.
    rewrite inits_cons. simpl.
    f_equal.  (* strip acc :: … *)
    rewrite (IH (acc + x)).
    rewrite map_map.
    apply map_ext; intros ys. simpl.
    reflexivity.
Qed.

Lemma scan_lemma_Z (xs : list Z) :
  scan_left Z.add xs 0 =
  map (fun ys : list Z => fold_left Z.add ys 0) (inits xs).
Proof.
  apply (scan_left_inits_general_Z xs 0).
Qed.

(* Key lemma: fold_left distributes over cons *)
Lemma fold_left_cons : forall (xs : list nat) (x acc : nat),
  fold_left Nat.add (x :: xs) acc = fold_left Nat.add xs (acc + x)%nat.
Proof.
  intros xs x acc.
  simpl.
  reflexivity.
Qed.

(* Generalized version: scan_left with arbitrary accumulator equals mapped fold_left *)
Lemma scan_left_inits_general :
  forall (xs : list nat) (acc : nat),
    scan_left Nat.add xs acc =
    map (fun ys : list nat => fold_left Nat.add ys acc) (inits xs).
Proof.
  induction xs as [| x xs' IH]; intros acc.
  - simpl; reflexivity.
  - simpl scan_left.
    rewrite inits_cons. simpl.
    f_equal.  (* strip acc :: … *)
    (* instantiate IH with (acc + x) and rewrite the recursive call first *)
    rewrite (IH (acc + x)%nat).
    (* now both sides are maps over (inits xs'), push the cons inside the map *)
    rewrite map_map.
    apply map_ext; intros ys. simpl.
    reflexivity.
Qed.

(* Simple wrapper lemma: special case accumulator = 0 *)
Lemma scan_lemma (xs : list nat) :
  scan_left Nat.add xs 0%nat = map (fun ys : list nat => fold_left Nat.add ys 0%nat) (inits xs).
Proof.
  apply (scan_left_inits_general xs 0%nat).
Qed.

(* Simple helper lemmas for nonNegPlus that are useful and provable *)

Lemma nonNegPlus_zero_right : forall x : Z, nonNegPlus x 0 = Z.max x 0.
Proof.
  intros x.
  unfold nonNegPlus.
  rewrite Z.add_0_r.
  destruct (Z.leb 0 x) eqn:H.
  - apply Z.leb_le in H.
    rewrite Z.max_l; [reflexivity | exact H].
  - apply Z.leb_gt in H.
    rewrite Z.max_r; [reflexivity | apply Z.lt_le_incl; exact H].
Qed.

Lemma nonNegPlus_zero_left : forall x : Z, nonNegPlus 0 x = Z.max x 0.
Proof.
  intros x.
  unfold nonNegPlus.
  rewrite Z.add_0_l.
  destruct (Z.leb 0 x) eqn:H.
  - apply Z.leb_le in H.
    rewrite Z.max_l; [reflexivity | exact H].
  - apply Z.leb_gt in H.
    rewrite Z.max_r; [reflexivity | apply Z.lt_le_incl; exact H].
Qed.

(* Simple test lemma to demonstrate proper workflow *)
Lemma nonNegPlus_idempotent_zero : nonNegPlus 0 0 = 0.
Proof.
  unfold nonNegPlus.
  simpl.
  reflexivity.
Qed.

(* Theorem: nonNegPlus is not associative *)
Theorem nonNegPlus_not_associative : ~ (forall x y z : Z, nonNegPlus (nonNegPlus x y) z = nonNegPlus x (nonNegPlus y z)).
Proof.
  intro H.
  (* Use counterexample: x = -10, y = -10, z = 1 *)
  specialize (H (-10) (-10) 1).
  unfold nonNegPlus in H.
  simpl in H.
  (* Left side: nonNegPlus (nonNegPlus (-10) (-10)) 1 *)
  (* = nonNegPlus (max(0, -10 + -10)) 1 *)
  (* = nonNegPlus (max(0, -20)) 1 *)
  (* = nonNegPlus 0 1 *)
  (* = max(0, 0 + 1) = 1 *)

  (* Right side: nonNegPlus (-10) (nonNegPlus (-10) 1) *)
  (* = nonNegPlus (-10) (max(0, -10 + 1)) *)
  (* = nonNegPlus (-10) (max(0, -9)) *)
  (* = nonNegPlus (-10) 0 *)
  (* = max(0, -10 + 0) = 0 *)

  (* So we have 1 = 0, which is a contradiction *)
  discriminate H.
Qed.

(* Helper lemma: nonNegPlus is always non-negative *)
(* Helper theorem: scan_left corresponds to mapping fold_left over inits *)
Theorem scan_left_fold_correspondence : forall (xs : list Z),
  scan_left (fun acc x => nonNegPlus acc x) xs 0 =
  map (fun prefix => fold_left (fun acc x => nonNegPlus acc x) prefix 0) (inits_rec xs).
Proof.
  intro xs.
  exact (@scan_left_inits_rec_fold Z Z (fun acc x => nonNegPlus acc x) xs 0).
Qed.

Lemma Z_max_l' : forall a b, a >= b -> a <|> b = a.
Proof. intros; unfold Z.max; apply Z.max_l; apply Z.ge_le; assumption. Qed.


(* Helper lemma: tails_rec on concatenation with singleton *)
Lemma tails_rec_app_singleton : forall {A : Type} (xs : list A) (x : A),
  tails_rec (xs ++ [x]) = map (fun ys => ys ++ [x]) (tails_rec xs) ++ [[]].
Proof.
  intros A xs x.
  induction xs as [| y xs' IH].

  - (* Base case: xs = [] *)
    simpl app.
    simpl tails_rec.
    reflexivity.

  - (* Inductive case: xs = y :: xs' *)
    simpl app.
    simpl tails_rec.
    rewrite IH.
    simpl map.
    (* Goal: (y :: xs') ++ [x] :: map (fun ys => ys ++ [x]) (tails_rec xs') ++ [[]] =
              ((y :: xs') ++ [x]) :: map (fun ys => ys ++ [x]) (tails_rec xs') ++ [[]] *)
    reflexivity.

Qed.

(* More general lemma: fold_left with cons and arbitrary initial accumulator *)
Lemma fold_left_cons_general : forall (A : Type) (l : list A) (acc : list A),
  fold_left (fun acc x => x :: acc) l acc =
  rev l ++ acc.
Proof.
  intros A l acc.
  revert acc.
  induction l as [|x xs IH]; intros acc.
  - (* Base case: l = [] *)
    simpl fold_left.
    simpl rev.
    simpl app.
    reflexivity.
  - (* Inductive case: l = x :: xs *)
    simpl fold_left.
    simpl rev.
    rewrite IH.
    (* Goal: (rev xs ++ [x]) ++ acc = rev xs ++ (x :: acc) *)
    (* Convert x :: acc to [x] ++ acc *)
    change (x :: acc) with ([x] ++ acc).
    (* Goal: (rev xs ++ [x]) ++ acc = rev xs ++ [x] ++ acc *)
    (* This is exactly app_assoc *)
    apply app_assoc.
Qed.

Theorem rev_fold_right_left :
  forall (A : Type) (l : list A),
    fold_left (fun acc x => x :: acc) l [] =
    rev (fold_right cons [] l).
Proof.
  intros A l.
  (* Use the general lemma with acc = [] *)
  rewrite fold_left_cons_general.
  (* Goal: rev l ++ [] = rev (fold_right cons [] l) *)
  rewrite app_nil_r.
  (* Goal: rev l = rev (fold_right cons [] l) *)
  (* Now I need to show that fold_right cons [] l = l *)
  assert (H: fold_right cons [] l = l).
  { induction l as [|x xs IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem rev_fold_left_right :
  forall (A : Type) (l : list A),
    fold_right cons [] l =
    rev (fold_left (fun acc x => x :: acc) l []).
Proof.
  intros A l.
  (* Use the general lemma with acc = [] *)
  rewrite fold_left_cons_general.
  (* Goal: rev l ++ [] = rev (fold_right cons [] l) *)
  rewrite app_nil_r.
  (* Goal: rev l = rev (fold_right cons [] l) *)
  (* Now I need to show that fold_right cons [] l = l *)
  assert (H: fold_right cons [] l = l).
  { induction l as [|x xs IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite H.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma tails_app_singleton : forall {A} (l : list A) (x : A),
  tails (l ++ [x]) = map (fun t => t ++ [x]) (tails l) ++ [[]].
Proof.
  intros A l x.
  rewrite tails_rec_equiv.
  rewrite (tails_rec_equiv l).
  apply tails_rec_app_singleton.
Qed.

Lemma map_rev_commute : forall {A B} (f : A -> B) (l : list A),
  map f (rev l) = rev (map f l).
Proof.
  intros A B f l.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite <- IH. rewrite map_app. simpl. reflexivity.
Qed.

Lemma map_rev_cons : forall {A} (x : A) (L : list (list A)),
  map (@rev A) (map (cons x) L) = map (fun l => rev l ++ [x]) L.
Proof.
  intros A x L. rewrite map_map.
  apply map_ext. intros l. simpl. reflexivity.
Qed.

Lemma inits_tails_duality : forall {A : Type} (xs : list A),
  map (@rev A) (inits xs) = rev (tails (rev xs)).
Proof.
  intros A xs.
  (* Use the recursive equivalences to simplify the proof *)
  rewrite inits_rec_equiv.
  rewrite tails_rec_equiv.
  (* Now prove: map (@rev A) (inits_rec xs) = rev (tails_rec (rev xs)) *)
  induction xs as [| x xs IH].
  - simpl. reflexivity.
  - simpl inits_rec.
    simpl map.
    simpl rev.
    rewrite tails_rec_app_singleton.
    rewrite rev_app_distr.
    simpl rev at 1.
    (* Goal: [] :: map (@rev A) (map (cons x) (inits_rec xs)) = rev [[]] ++ rev (map (fun ys => ys ++ [x]) (tails_rec (rev xs))) *)
    rewrite map_map.
    simpl rev at 1.
    (* Goal: [] :: map (fun l => rev (cons x l)) (inits_rec xs) = [[]] ++ rev (map (fun ys => ys ++ [x]) (tails_rec (rev xs))) *)
    simpl rev.
    (* Goal: [] :: map (fun x0 => rev x0 ++ [x]) (inits_rec xs) = [[]] ++ rev (map (fun ys => ys ++ [x]) (tails_rec (rev xs))) *)
    simpl app.
    f_equal.
    (* Need to show: map (fun x0 => rev x0 ++ [x]) (inits_rec xs) = rev (map (fun ys => ys ++ [x]) (tails_rec (rev xs))) *)
    (* Use IH: map (@rev A) (inits_rec xs) = rev (tails_rec (rev xs)) *)
    (* We want to show that applying the same transformation to both sides preserves equality *)
    rewrite <- (map_rev_commute (fun ys => ys ++ [x])).
    rewrite <- IH.
    rewrite map_map.
    apply map_ext.
    intro l.
    reflexivity.
Qed.

(* Key lemma: fold_left Z.max distributes over initial Z.max *)
(* Helper lemma: rev distributes over map in the right way *)
Lemma rev_map_rev : forall {A B : Type} (f : A -> B) (xs : list A),
  map f (rev xs) = rev (map f xs).
Proof.
  intros A B f xs.
  induction xs as [| x xs' IH].
  - simpl. reflexivity.
  - simpl rev at 1.
    simpl map at 2.
    simpl rev at 2.
    rewrite map_app.
    simpl map.
    rewrite IH.
    reflexivity.
Qed.

(* Dual conversion theorem: scan_left relates to scan_right via reversal *)
Lemma scan_left_right_rev : forall (A B : Type) (f : A -> B -> A) (xs : list B) (init : A),
  scan_left f xs init = rev (scan_right (fun x acc => f acc x) init (rev xs)).
Proof.
  intros A B f xs init.
  (* Use the scan-fold correspondence lemmas to establish the duality *)

  (* Express scan_left using scan_left_inits_rec_fold *)
  rewrite scan_left_inits_rec_fold.

  (* Express scan_right using scan_right_tails_rec_fold on the RHS *)
  rewrite scan_right_tails_rec_fold.

  (* Now we need to show:
     map (fun prefix => fold_left f prefix init) (inits_rec xs) =
     rev (map (fold_right (fun x acc => f acc x) init) (tails_rec (rev xs)))
  *)

  (* The key insight: use map_ext to convert fold_left to fold_right using fold_left_right_rev *)
  assert (H_fold_equiv: forall prefix,
    fold_left f prefix init = fold_right (fun x acc => f acc x) init (rev prefix)).
  {
    intro prefix.
    apply fold_left_right_rev.
  }

  rewrite (map_ext _ _ H_fold_equiv).

  (* Now we need to show:
     map (fun prefix => fold_right (fun x acc => f acc x) init (rev prefix)) (inits_rec xs) =
     rev (map (fold_right (fun x acc => f acc x) init) (tails_rec (rev xs)))
  *)

  rewrite <- map_map.

  (* Now the goal is:
     map (fold_right (fun x acc => f acc x) init) (map rev (inits_rec xs)) =
     rev (map (fold_right (fun x acc => f acc x) init) (tails_rec (rev xs)))
  *)

  (* Convert inits_rec to inits first *)
  rewrite <- inits_rec_equiv.

  (* Apply the inits-tails duality lemma *)
  rewrite inits_tails_duality.

  (* Convert tails_rec to tails in the goal *)
  rewrite <- tails_rec_equiv.

  (* Now the goal is:
     map (fold_right (fun x acc => f acc x) init) (rev (tails (rev xs))) =
     rev (map (fold_right (fun x acc => f acc x) init) (tails (rev xs)))
  *)

  (* This follows from rev_map_rev *)
  rewrite rev_map_rev.
  reflexivity.

Qed.



(* Specialized version for nonNegPlus *)
Lemma scan_left_nonNegPlus_right_rev : forall xs init,
  scan_left (fun acc x => nonNegPlus acc x) xs init =
  rev (scan_right (fun x acc => nonNegPlus acc x) init (rev xs)).
Proof.
  intros xs init.
  apply scan_left_right_rev.
Qed.

(* Theorem relating fold_left on pairs to fold_right on pairs *)
Lemma fold_pair_left_right_rev : forall (A B : Type) (f : A * B -> A -> A * B) (xs : list A) (init : A * B),
  fold_left f xs init =
  fold_right (fun x g => fun p => g (f p x)) (fun p => p) xs init.
Proof.
  intros A B f xs init.
  (* This follows directly from fold_left_as_fold_right *)
  apply fold_left_as_fold_right.
Qed.

(* Specialized version for our pair function *)
Lemma fold_pair_max_nonNegPlus_left_right_rev : forall xs,
  fold_left (fun uv x => let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x)) xs (0, 0) =
  fold_right (fun x g => fun uv => g (let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x)))
             (fun uv => uv) xs (0, 0).
Proof.
  intro xs.
  apply fold_pair_left_right_rev.
Qed.

(* Helper lemma: fold_left Z.max distributes over cons when initial value is large enough *)
Lemma fold_left_max_cons_large : forall (l : list Z) (u v : Z),
  u >= v ->
  fold_left Z.max (v :: l) u = fold_left Z.max l u.
Proof.
  intros l u v H_u_ge_v.
  simpl fold_left.
  f_equal.
  apply Z.max_l.
  apply Z.ge_le; assumption.
Qed.

(* Monotonicity lemma for fold_left Z.max *)
(* General helper lemma for fold_scan_fusion_pair_dual *)
(* Dual conversion theorems for fold operations *)

(* Helper lemma: fold_right Z.max distributes over max in initial value *)
Lemma fold_right_max_init_distrib : forall (xs : list Z) (a b : Z),
  fold_right Z.max (Z.max a b) xs = Z.max a (fold_right Z.max b xs).
Proof.
  intros xs a b.
  induction xs as [| x xs' IH].
  - (* Base case: xs = [] *)
    simpl. reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    simpl fold_right.
    rewrite IH.
    (* Goal: Z.max x (Z.max a (fold_right Z.max b xs')) = Z.max a (Z.max x (fold_right Z.max b xs')) *)
    (* This follows from associativity and commutativity of Z.max *)
    rewrite Z.max_assoc.
    rewrite (Z.max_comm x a).
    rewrite <- Z.max_assoc.
    reflexivity.
Qed.

(* For associative and commutative operations like Z.max, fold_left and fold_right are equivalent *)
Lemma fold_left_max_eq_fold_right_max : forall (xs : list Z) (init : Z),
  fold_left Z.max xs init = fold_right Z.max init xs.
Proof.
  intros xs.
  induction xs as [| x xs' IH]; intro init.
  - (* Base case: xs = [] *)
    simpl. reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    simpl fold_left. simpl fold_right.
    (* Goal: fold_left Z.max xs' (init <|> x) = x <|> fold_right Z.max init xs' *)

    (* Apply IH with the new initial value (init <|> x) *)
    rewrite (IH (init <|> x)).

    (* Now we have: fold_right Z.max (init <|> x) xs' = x <|> fold_right Z.max init xs' *)
    (* Apply the helper lemma: fold_right Z.max (Z.max init x) xs' = Z.max init (fold_right Z.max x xs') *)
    (* But we need it with x and init swapped, so first use commutativity *)
    assert (H_comm: init <|> x = x <|> init). { apply Z.max_comm. }
    rewrite H_comm.
    (* Now apply the helper lemma with a = x, b = init *)
    rewrite <- (fold_right_max_init_distrib xs' x init).
    (* Now we have the goal: Z.max x (fold_right Z.max init xs') = x <|> fold_right Z.max init xs' *)
    reflexivity.
Qed.

(* For nonNegPlus (which is not associative), we need reversal *)
Lemma fold_left_nonNegPlus_eq_fold_right_nonNegPlus_rev : forall (xs : list Z) (init : Z),
  fold_left (fun acc x => nonNegPlus acc x) xs init =
  fold_right (fun x acc => nonNegPlus acc x) init (rev xs).
Proof.
  intros xs init.
  (* Apply the general fold_left/fold_right reversal property *)
  apply fold_left_right_rev.
Qed.

(* Key lemma: nonNegPlus is commutative for our use case *)
Lemma nonNegPlus_comm_special : forall v x,
  v >= 0 -> nonNegPlus v x = nonNegPlus x v.
Proof.
  intros v x Hv.
  unfold nonNegPlus.
  destruct (Z.leb 0 (v + x)) eqn:H1; destruct (Z.leb 0 (x + v)) eqn:H2.
  - apply Z.add_comm.
  - apply Z.leb_le in H1. apply Z.leb_gt in H2. exfalso. apply (Z.lt_irrefl (v + x)). apply Z.lt_le_trans with (m := 0). rewrite Z.add_comm. exact H2. exact H1.
  - apply Z.leb_gt in H1. apply Z.leb_le in H2. exfalso. apply (Z.lt_irrefl (x + v)). apply Z.lt_le_trans with (m := 0). rewrite <- Z.add_comm. exact H1. exact H2.
  - reflexivity.
Qed.

(* Conversion theorem: scan_left nonNegPlus to scan_right nonNegPlus with reversal *)
Lemma scan_left_nonNegPlus_to_scan_right : forall xs init,
  init >= 0 ->
  scan_left (fun acc x => nonNegPlus acc x) xs init =
  rev (scan_right (fun x acc => nonNegPlus acc x) init (rev xs)).
Proof.
  intros xs init H_init_nonneg.
  (* This follows from scan_left_right_rev with the specific function *)
  apply scan_left_right_rev.
Qed.

(* Conversion theorem: fold_left nonNegPlus to fold_right nonNegPlus with reversal *)
Lemma fold_left_nonNegPlus_to_fold_right : forall xs init,
  init >= 0 ->
  fold_left (fun acc x => nonNegPlus acc x) xs init =
  fold_right (fun x acc => nonNegPlus acc x) init (rev xs).
Proof.
  intros xs init H_init_nonneg.
  (* Apply the general fold_left/fold_right reversal property *)
  apply fold_left_right_rev.
Qed.

(* Dual version of fold_scan_fusion_pair - works with fold_left and scan_left *)

(* fold_right extensionality lemma - needed for BirdMeertens.v *)
(* fold_left extensionality lemma - needed for BirdMeertens.v *)
(* Dual version of fold_scan_fusion_pair - works with fold_left and scan_left *)
(* Monoid framework for Horner's rule using TailsMonoid *)
Section HornerViaMonoids.

(*
To Do:
 - Make a max monoid with negative infinity element
 - Test the max monoid with negative infinity element in variation of Bird Meertens proof
*)

End HornerViaMonoids.

(* Key insight: the tropical Horner operation is equivalent to nonNegPlus *)
(* This approach was incorrect - the distributivity property doesn't hold in general *)
(* Let me try a different approach for the main proof *)

(* Helper lemma: inits xs contains xs as its last element *)
(* Helper lemma: removing elements from a list can only decrease nonNegSum *)
(* Helper lemma: nonNegSum_dual is always non-negative *)
(* Helper lemma: fold_left is monotonic in initial value for nonNegPlus *)
(* Helper lemma: removing elements from a list can only decrease nonNegSum *)
(* Helper lemma: fold_right Z.max 0 gives a value that's <= any upper bound *)
(* Helper lemma: fold_right Z.max 0 returns the maximum element when it's in the list *)
(* ========== DUALITY THEOREMS FOR REUSING PROOFS ========== *)

(* Import the fold_left_right_equiv theorem from CoqUtilLib *)
From Coq Require Import Arith.

(* Key duality theorem: for max operations, fold_left and fold_right are equivalent *)
(* Specialized version for our common pattern with init = 0 *)
(* For fold_left_max_le, we need a more general version since fold_right_max_le assumes init=0 *)
Lemma fold_right_max_le_general : forall (xs : list Z) (init ub : Z),
  init <= ub ->
  (forall y, In y xs -> y <= ub) ->
  fold_right (fun x y : Z => x <|> y) init xs <= ub.
Proof.
  intros xs init ub Hinit H_ub.
  induction xs as [| x xs' IH].
  - simpl. exact Hinit.
  - simpl.
    apply Z.max_lub.
    + apply H_ub. left. reflexivity.
    + apply IH. intros y Hy. apply H_ub. right. assumption.
Qed.

(* Now fold_left_max_le follows directly from the general version *)
Corollary fold_left_max_le_direct : forall (xs : list Z) (acc ub : Z),
  acc <= ub ->
  (forall y, In y xs -> y <= ub) ->
  fold_left (fun x y => x <|> y) xs acc <= ub.
Proof.
  intros xs acc ub Hacc H_ub.
  rewrite max_fold_duality.
  apply fold_right_max_le_general; assumption.
Qed.

(* Corollary: fold_left_max_returns_max can be proven directly from fold_right_max_returns_max *)
Corollary fold_left_max_returns_max_direct :
  forall (xs : list Z) (m : Z),
    m >= 0 ->
    (forall y, In y xs -> y <= m) ->
    In m xs ->
    fold_left (fun x y => x <|> y) xs 0 = m.
Proof.
  intros xs m Hm_nonneg H_ub H_in.
  rewrite max_fold_duality_zero.
  apply fold_right_max_returns_max; assumption.
Qed.

(* General theorem: any property proven for fold_right max also holds for fold_left max *)
Theorem fold_max_property_transfer : forall (P : list Z -> Z -> Prop) (xs : list Z) (init : Z),
  P xs (fold_right (fun x y => x <|> y) init xs) ->
  P xs (fold_left (fun x y => x <|> y) xs init).
Proof.
  intros P xs init H.
  rewrite max_fold_duality.
  exact H.
Qed.

(* General duality transfer theorem for max operations with membership *)
Theorem max_membership_duality : forall (xs : list Z) (m : Z),
  In m xs ->
  (forall y, In y xs -> y <= m) ->
  m >= 0 ->
  fold_right (fun x y => x <|> y) 0 xs = fold_left (fun x y => x <|> y) xs 0.
Proof.
  intros xs m H_in H_ub Hm_nonneg.
  symmetry.
  apply max_fold_duality_zero.
Qed.

(* Specialized version: fold_max_app_dual for init=0 follows from fold_max_app and duality *)
Corollary fold_left_max_app_zero : forall (l1 l2 : list Z),
  fold_left (fun x y => x <|> y) (l1 ++ l2) 0 =
  (fold_left (fun x y => x <|> y) l1 0) <|> (fold_left (fun x y => x <|> y) l2 0).
Proof.
  intros l1 l2.
  repeat rewrite max_fold_duality_zero.
  apply fold_max_app.
Qed.

(* Additional duality theorems for complex operations *)

(* Duality theorem for scan operations with nonNegPlus *)
Theorem scan_nonNegPlus_duality : forall (xs : list Z),
  scan_left (fun acc x => nonNegPlus acc x) xs 0 =
  map (fun y => fold_left (fun acc x => nonNegPlus acc x) y 0) (inits_rec xs).
Proof.
  intro xs.
  exact (@scan_left_inits_rec_fold Z Z (fun acc x => nonNegPlus acc x) xs 0).
Qed.

(* Duality for fold operations on pairs - this is needed for fold_scan_fusion_pair_dual *)
Theorem fold_pair_duality : forall (xs : list Z) (f : Z * Z -> Z -> Z * Z),
  (* If f respects the proper structure, fold_left and fold_right can be related *)
  (* For the specific case of max operations, we can establish duality *)
  forall (init : Z * Z),
  (* This is a placeholder for the full pair duality theorem *)
  True. (* We'll need to develop this further *)
Proof.
  intros. exact I.
Qed.

(* ========== END DUALITY THEOREMS ========== *)

(* Now we can prove fold_promotion_dual using the duality theorems *)
(* Helper lemma: fold_left gives a value that's <= any upper bound *)
(* NOTE: This proof is now trivial using our duality theorem! *)
Lemma fold_left_max_le : forall (xs : list Z) (acc ub : Z),
  acc <= ub ->
  (forall y, In y xs -> y <= ub) -> fold_left (fun x y => x <|> y) xs acc <= ub.
Proof.
  (* This follows directly from the duality theorem and fold_right_max_le_general *)
  apply fold_left_max_le_direct.
Qed.

(* Helper lemma for fold_left that maintains maximum when all elements are <= max *)
Lemma fold_left_max_preserves : forall (xs : list Z) (m : Z),
  m >= 0 ->
  (forall y, In y xs -> y <= m) ->
  fold_left (fun x y => x <|> y) xs m = m.
Proof.
  intros xs m Hm_nonneg H_ub.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - simpl.
    assert (H_eq: m <|> x = m).
    { apply Z.max_l. apply H_ub. left. reflexivity. }
    rewrite H_eq.
    apply IH.
    + intros y Hy. apply H_ub. right. assumption.
Qed.


(* Monotonicity lemma for fold_left max *)
Lemma fold_left_max_monotonic : forall (xs : list Z) (acc1 acc2 : Z),
  acc1 <= acc2 -> fold_left (fun x y => x <|> y) xs acc1 <= fold_left (fun x y => x <|> y) xs acc2.
Proof.
  intros xs acc1 acc2 H_le.
  revert acc1 acc2 H_le.
  induction xs as [|x xs' IH].
  - intros acc1 acc2 H_le. simpl. exact H_le.
  - intros acc1 acc2 H_le. simpl.
    apply IH.
    apply Z.max_le_compat_r. exact H_le.
Qed.

(* Helper lemma: fold_left Z.max 0 returns the maximum element when it's in the list *)
(* NOTE: This proof is now trivial using our duality theorem! *)
(* Helper lemma: fold_right_max_inf returns the maximum element *)
Lemma fold_right_max_inf_is_maximal :
  forall (xs : list Z) (w y : Z),
    xs <> [] ->
    fold_right_max_inf xs = Z_val w ->
    In y xs ->
    y <= w.
Proof.
  intro xs.
  induction xs as [|x xs' IH].
  - intros w y H_contra. contradiction H_contra; reflexivity.

  - intros w y H_nonempty H_fold H_in.
    destruct xs' as [|z xs''].

    + (* xs = [x] *)
      simpl in H_in. destruct H_in as [H_eq | H_contra].
      * subst. unfold fold_right_max_inf in H_fold. simpl in H_fold.
        inversion H_fold. apply Z.le_refl.
      * contradiction.

    + (* xs = x :: z :: xs'' *)
      unfold fold_right_max_inf in H_fold. simpl in H_fold.

      (* The fold gives Z_val x ∨_inf fold_right_max_inf (z :: xs'') *)
      (* Let's call fold_right_max_inf (z :: xs'') = Z_val w' for some w' *)
      assert (H_tail_nonempty: z :: xs'' <> []) by discriminate.
      assert (H_tail_exists: exists w', fold_right_max_inf (z :: xs'') = Z_val w').
      { apply fold_right_max_inf_never_neginf. exact H_tail_nonempty. }

      destruct H_tail_exists as [w' Hw'].
      unfold fold_right_max_inf in Hw'. simpl in Hw'.
      rewrite Hw' in H_fold.
      simpl in H_fold.
      inversion H_fold. subst.

      (* So w = Z.max x w' *)
      (* Case analysis on where y is *)
      destruct H_in as [H_y_eq_x | H_y_in_tail].

      * (* y = x *)
        subst. apply Z.le_max_l.

      * (* y in tail z :: xs'' *)
        assert (H_y_le_w': y <= w').
        { apply IH.
          - exact H_tail_nonempty.
          - exact Hw'.
          - exact H_y_in_tail. }
        apply Z.le_trans with w'. exact H_y_le_w'. apply Z.le_max_r.
Qed.

(* Direct proof using the key insight that the maximum is unique *)
Lemma fold_right_max_inf_gives_max :
  forall (xs : list Z) (m : Z),
    xs <> [] ->
    In m xs ->
    (forall y, In y xs -> y <= m) ->
    fold_right_max_inf xs = Z_val m.
Proof.
  intro xs.
  induction xs as [|x xs' IH].
  - intros m H_contra. contradiction H_contra; reflexivity.

  - intros m H_nonempty H_in H_max.
    destruct xs' as [|y xs''].

    + (* Base case: xs = [x] *)
      simpl in H_in. destruct H_in as [H_eq | H_contra].
      * subst. unfold fold_right_max_inf. simpl. reflexivity.
      * contradiction.

    + (* Inductive case: xs = x :: y :: xs'' *)
      (* Key insight: fold_right_max_inf (x :: y :: xs'') computes the max of all elements *)
      (* Since m is the unique maximum (by conditions), the fold must return Z_val m *)

      (* We know fold_right_max_inf returns some element from the list *)
      assert (H_result_in: Z_plus_neg_inf_In (fold_right_max_inf (x :: y :: xs'')) (x :: y :: xs'')).
      { apply fold_right_max_inf_in. discriminate. }

      assert (H_result_exists: exists w, fold_right_max_inf (x :: y :: xs'') = Z_val w).
      { apply fold_right_max_inf_never_neginf. discriminate. }

      destruct H_result_exists as [w Hw].

      (* From H_result_in and Hw, we get In w (x :: y :: xs'') *)
      assert (H_w_in: In w (x :: y :: xs'')).
      { unfold Z_plus_neg_inf_In in H_result_in. rewrite Hw in H_result_in. exact H_result_in. }

      (* Since m is the maximum and w is in the list, w <= m *)
      assert (H_w_le_m: w <= m).
      { apply H_max. exact H_w_in. }

      (* Since the fold computes the maximum and m is in the list, we must have w >= m *)
      (* This follows from the fact that fold_right_max_inf computes the actual maximum *)
      assert (H_m_le_w: m <= w).
      {
        (* fold_right_max_inf returns the maximum element *)
        (* So w must be >= all elements including m *)
        apply (fold_right_max_inf_is_maximal (x :: y :: xs'') w).
        - discriminate.
        - exact Hw.
        - exact H_in.
      }

      (* From w <= m and m <= w, we get w = m *)
      assert (H_w_eq_m: w = m).
      { apply Z.le_antisymm. exact H_w_le_m. exact H_m_le_w. }

      rewrite Hw. rewrite H_w_eq_m. reflexivity.
Qed.

(* Helper lemma: if m is maximum element, then fold_right_max_inf returns m *)
Lemma fold_right_max_inf_with_max :
  forall (xs : list Z) (m : Z),
    xs <> [] ->
    In m xs ->
    (forall y, In y xs -> y <= m) ->
    fold_right_max_inf xs = Z_val m.
Proof.
  (* This is now just a direct application of our helper lemma *)
  exact fold_right_max_inf_gives_max.
Qed.

(* General version: fold_right max with proper negative infinity identity *)
Lemma fold_right_max_inf_returns_max :
  forall (xs : list Z) (m : Z),
    (forall y, In y xs -> Z_val y <=_inf Z_val m) ->
    In m xs ->
    fold_right_max_inf xs = Z_val m.
Proof.
  intros xs m H_upper_bound H_in.

  (* Key insight: if m is an upper bound and in the list, then m = max(xs) *)
  assert (H_is_max: forall x, In x xs -> x <= m).
  {
    intros x H_x_in.
    specialize (H_upper_bound x H_x_in).
    unfold Z_plus_neg_inf_le in H_upper_bound.
    simpl in H_upper_bound.
    exact H_upper_bound.
  }

  (* xs cannot be empty since m ∈ xs *)
  assert (H_nonempty: xs <> []).
  {
    intro H_empty.
    rewrite H_empty in H_in.
    simpl in H_in.
    exact H_in.
  }

  (* Apply our helper lemma *)
  apply fold_right_max_inf_with_max.
  - exact H_nonempty.
  - exact H_in.
  - exact H_is_max.
Qed.

(* Helper lemma: nonNegSum is always non-negative *)
Lemma nonNegSum_nonneg : forall xs : list Z, nonNegSum xs >= 0.
Proof.
  intros xs.
  unfold nonNegSum.
  induction xs as [|x xs' IH].
  - simpl. apply Z.ge_le_iff. apply Z.le_refl.
  - simpl. apply nonNegPlus_nonneg'.
Qed.
Print Assumptions nonNegSum_nonneg.

(* Helper lemma: elements of inits are prefixes *)
(* Helper lemma: elements of tails are suffixes *)
(* Key lemma: the sum equals the maximum of prefix sums with nonNegPlus *)
(* Key lemma: the sum equals the maximum of prefix sums with nonNegPlus *)
(* Dual versions of the generalised Horner's rule lemmas *)
(* These work with fold_left instead of fold_right and tails instead of inits *)

(* For the dual approach, we need to work with the complex tails structure *)
(* Since the tails structure is complex, we'll focus on proving the scan-fold fusion first *)

(* The key insight is that we need proper dual versions of the existing lemmas *)
(* Let's create a basic framework that builds up the needed proofs step by step *)


(* Boolean consistency lemma - simpler version *)
Lemma leb_max_simple : forall s t x,
  Z.leb 0 (Z.max (s + x) (t + x)) = true -> 
  Z.leb 0 (s + x) = true \/ Z.leb 0 (t + x) = true.
Proof.
  intros s t x H.
  (* Convert boolean to proposition *)
  rewrite Z.leb_le in H.
  (* Case analysis on whether s + x >= 0 *)
  destruct (Z_le_dec 0 (s + x)) as [Hs | Hs].
  - (* Case: s + x >= 0 *)
    left. 
    rewrite Z.leb_le.
    exact Hs.
  - (* Case: s + x < 0 *)
    right.
    rewrite Z.leb_le.
    (* Since max >= 0 and s+x < 0, we must have t+x >= 0 *)
    apply Z.nle_gt in Hs.
    destruct (Z_le_dec 0 (t + x)) as [Ht | Ht].
    + exact Ht.
    + apply Z.nle_gt in Ht.
      (* Both s+x < 0 and t+x < 0, but max >= 0 - contradiction *)
      exfalso.
      assert (Z.max (s + x) (t + x) < 0).
      { apply Z.max_lub_lt; assumption. }
      apply (Z.lt_irrefl 0).
      apply Z.le_lt_trans with (m := Z.max (s + x) (t + x)).
      * exact H.
      * exact H0.
Qed.

(* Key lemma for the distributivity proof *)
Lemma nonNegPlus_cases : forall s t x,
  nonNegPlus (Z.max s t) x = 
  if Z.leb 0 (s + x) then
    if Z.leb 0 (t + x) then Z.max (s + x) (t + x)
    else if Z.leb (s + x) (t + x) then t + x else s + x
  else if Z.leb 0 (t + x) then t + x else 0.
Proof.
  intros s t x.
  unfold nonNegPlus.
  rewrite max_add_distributes.
  
  (* Case analysis on the boolean conditions *)
  destruct (Z.leb 0 (s + x)) eqn:Hs, (Z.leb 0 (t + x)) eqn:Ht.
  
  (* Case 1: s+x >= 0 and t+x >= 0 *)
  - simpl.
    (* Since both are non-negative, max is also non-negative *)
    assert (H_max_nonneg: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Hs. 
      apply Z.le_trans with (m := s + x). exact Hs. apply Z.le_max_l. }
    rewrite H_max_nonneg.
    reflexivity.
  
  (* Case 2: s+x >= 0 but t+x < 0 *)
  - simpl.
    (* Since s+x >= 0 > t+x, max(s+x, t+x) = s+x >= 0 *)
    assert (H_max_pos: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Hs.
      apply Z.le_trans with (m := s + x). exact Hs. apply Z.le_max_l. }
    rewrite H_max_pos.
    (* The RHS becomes: if (Z.leb 0 (t + x)) then ... else if (Z.leb (s+x) (t+x)) then t+x else s+x *)
    (* Since t+x < 0, the first condition is false, so we get: if (Z.leb (s+x) (t+x)) then t+x else s+x *)
    (* Since s+x >= 0 > t+x, Z.leb (s+x) (t+x) = false, so we get s+x *)
    simpl.
    rewrite Z.leb_le in Hs. rewrite Z.leb_gt in Ht.
    assert (H_ge: s + x >= t + x). {
      apply Z.ge_le_iff.
      apply Z.le_trans with (m := 0).
      - apply Z.lt_le_incl. exact Ht.
      - exact Hs.
    }
    assert (H_leb_false: Z.leb (s + x) (t + x) = false).
    { apply Z.leb_gt. apply Z.lt_le_trans with (m := 0). exact Ht. exact Hs. }
    rewrite H_leb_false.
    rewrite Z.max_l; [reflexivity | apply Z.ge_le; exact H_ge].
  
  (* Case 3: s+x < 0 but t+x >= 0 *)
  - simpl.
    (* Since t+x >= 0 > s+x, max(s+x, t+x) = t+x >= 0 *)
    assert (H_max_pos: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Ht.
      apply Z.le_trans with (m := t + x). exact Ht. apply Z.le_max_r. }
    rewrite H_max_pos.
    (* The RHS becomes: if (Z.leb 0 (t + x)) then t+x else 0 *)
    (* Since t+x >= 0, this gives t+x *)
    simpl. 
    rewrite Z.leb_gt in Hs. rewrite Z.leb_le in Ht.
    assert (H_ge: t + x >= s + x). {
      apply Z.ge_le_iff.
      apply Z.le_trans with (m := 0).
      - apply Z.lt_le_incl. exact Hs.
      - exact Ht.
    }
    rewrite Z.max_r; [reflexivity | apply Z.ge_le; exact H_ge].
  
  (* Case 4: both s+x < 0 and t+x < 0 *)
  - simpl.
    (* Both negative, so max is also negative *)
    assert (H_max_neg: Z.leb 0 (Z.max (s + x) (t + x)) = false).
    { apply Z.leb_gt. rewrite Z.leb_gt in Hs, Ht.
      apply Z.max_lub_lt; assumption. }
    rewrite H_max_neg.
    reflexivity.
Qed.

(* Helper lemma: nonNegPlus with 0 gives max-like behavior *)
Lemma nonNegPlus_max_zero : forall x y,
  nonNegPlus x y <|> 0 = Z.max (if Z.leb 0 (x + y) then x + y else 0) 0.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - simpl. rewrite Z.max_l; [reflexivity | rewrite Z.leb_le in H; assumption].
  - simpl. rewrite Z.max_r; [reflexivity | reflexivity].
Qed.
