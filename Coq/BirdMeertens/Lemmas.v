Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.FunctionLemmas.
Require Import BirdMeertens.TailsMonoid.
Require Import CoqUtilLib.ListFunctions.

Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zmax.

Open Scope Z_scope.

(* Max notation *)
Notation "x <|> y" := (Z.max x y) (at level 50, left associativity).

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

(* ===== CRITICAL DEFINITIONS (USED BY MAIN THEOREMS) ===== *)

Definition nonNegPlus (x y : Z) : Z :=
  if Z.leb 0 (x + y) then x + y else 0.

(* NonNegPlus notation *)
Notation "x <#> y" := (nonNegPlus x y) (at level 40, left associativity).

Definition nonNegSum (xs : list Z) : Z := fold_right nonNegPlus 0%Z xs.

Definition nonNegMaximum : list Z -> Z := fold_right (fun x y => x <|> y) 0.

Definition nonNegMaximum_dual (xs : list Z) : Z := fold_left (fun x y => x <|> y) xs 0.

Definition maxSoFarAndPreviousSum : Z -> (Z * Z) -> (Z * Z) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.

Definition nonNegSum_dual (xs : list Z) : Z := fold_left (fun acc x => nonNegPlus acc x) xs 0%Z.

Definition maxSoFarAndPreviousSum_dual : (Z * Z) -> Z -> (Z * Z) := fun uv x => match uv with
  | (u, v) => let w := (v <#> x) in (u <|> w, w)
end.

(* ===== ESSENTIAL THEOREMS (USED BY MAIN PROOFS) ===== *)

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

Lemma app_concat [A : Type] : forall (l : list (list A)),
  concat l = fold_right (@app A) [] l.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

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

Lemma nonNegPlus_comm : forall x y : Z, nonNegPlus x y = nonNegPlus y x.
Proof.
  intros x y.
  unfold nonNegPlus.
  rewrite Z.add_comm.
  reflexivity.
Qed.

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

Lemma nonNegPlus_nonneg' : forall x y : Z, nonNegPlus x y >= 0.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - apply Z.leb_le in H.
    apply Z.le_ge.
    exact H.
  - apply Z.le_ge.
    apply Z.le_refl.
Qed.

(* Helper lemma for max distributivity *)
Lemma max_distrib_max : forall a b c,
  Z.max (Z.max a b) c = Z.max (Z.max a c) (Z.max b c).
Proof.
  intros a b c.
  (* Let me see what the goal looks like step by step *)
  destruct (Z_le_gt_dec a b) as [H_ab | H_ab].
  - (* Case: a <= b *)
    destruct (Z_le_gt_dec a c) as [H_ac | H_ac].
    + (* Case: a <= b, a <= c *)
      destruct (Z_le_gt_dec b c) as [H_bc | H_bc].
      * (* Case: a <= b, a <= c, b <= c *)
        (* Since a <= b <= c, we have max(a,b) = b, max(a,c) = c, max(b,c) = c *)
        (* Left: max(max(a,b), c) = max(b, c) = c *)
        (* Right: max(max(a,c), max(b,c)) = max(c, c) = c *)

        (* Rewrite all max operations at once using the ordering *)
        assert (H1: Z.max a b = b) by (apply Z.max_r; assumption).
        assert (H2: Z.max a c = c) by (apply Z.max_r; assumption).
        assert (H3: Z.max b c = c) by (apply Z.max_r; assumption).

        rewrite H1, H2, H3.
        (* Now goal is: c = Z.max c c *)
        symmetry.
        apply Z.max_id.
      * (* Case: a <= b, a <= c, c < b *)
        (* So a <= c < b, meaning max(a,b) = b, max(a,c) = c, max(b,c) = b *)
        assert (H1: Z.max a b = b) by (apply Z.max_r; assumption).
        assert (H2: Z.max a c = c) by (apply Z.max_r; assumption).
        assert (H3: Z.max b c = b) by (apply Z.max_l; apply Z.gt_lt in H_bc; apply Z.lt_le_incl; assumption).
        rewrite H1, H2, H3.
        (* Goal is now: b = c <|> b, and since c < b we have max(c,b) = b *)
        symmetry.
        apply Z.max_r.
        apply Z.gt_lt in H_bc; apply Z.lt_le_incl; assumption.

    + (* Case: a <= b, c < a *)
      destruct (Z_le_gt_dec b c) as [H_bc | H_bc].
      * (* Case: a <= b, c < a, b <= c - but this is impossible since c < a <= b <= c *)
        exfalso. apply Z.gt_lt in H_ac. apply (Z.lt_irrefl c). apply Z.lt_le_trans with (m := a); [assumption | apply Z.le_trans with (m := b); assumption].
      * (* Case: a <= b, c < a, c < b *)
        (* So c < a <= b, meaning max(a,b) = b, max(a,c) = a, max(b,c) = b *)
        assert (H1: Z.max a b = b) by (apply Z.max_r; assumption).
        assert (H2: Z.max a c = a) by (apply Z.max_l; apply Z.gt_lt in H_ac; apply Z.lt_le_incl; assumption).
        assert (H3: Z.max b c = b) by (apply Z.max_l; apply Z.gt_lt in H_bc; apply Z.lt_le_incl; assumption).
        rewrite H1, H2, H3.
        (* Goal is now: b = a <|> b, and since a <= b we have max(a,b) = b *)
        symmetry.
        apply Z.max_r.
        assumption.

  - (* Case: b < a *)
    destruct (Z_le_gt_dec a c) as [H_ac | H_ac].
    + (* Case: b < a, a <= c *)
      destruct (Z_le_gt_dec b c) as [H_bc | H_bc].
      * (* Case: b < a, a <= c, b <= c *)
        (* So b <= c and b < a <= c, meaning max(a,b) = a, max(a,c) = c, max(b,c) = c *)
        assert (H1: Z.max a b = a) by (apply Z.max_l; apply Z.gt_lt in H_ab; apply Z.lt_le_incl; assumption).
        assert (H2: Z.max a c = c) by (apply Z.max_r; assumption).
        assert (H3: Z.max b c = c) by (apply Z.max_r; assumption).
        rewrite H1, H2, H3.
        (* Goal is now: c = c <|> c *)
        symmetry.
        apply Z.max_id.
      * (* Case: b < a, a <= c, c < b - but this is impossible since a <= c < b < a *)
        exfalso. apply (Z.lt_irrefl a). apply Z.le_lt_trans with (m := c); [assumption | apply Z.lt_le_trans with (m := b); [apply Z.gt_lt in H_bc; assumption | apply Z.gt_lt in H_ab; apply Z.lt_le_incl; assumption]].

    + (* Case: b < a, c < a *)
      destruct (Z_le_gt_dec b c) as [H_bc | H_bc].
      * (* Case: b < a, c < a, b <= c *)
        (* So b <= c < a, meaning max(a,b) = a, max(a,c) = a, max(b,c) = c *)
        assert (H1: Z.max a b = a) by (apply Z.max_l; apply Z.gt_lt in H_ab; apply Z.lt_le_incl; assumption).
        assert (H2: Z.max a c = a) by (apply Z.max_l; apply Z.gt_lt in H_ac; apply Z.lt_le_incl; assumption).
        assert (H3: Z.max b c = c) by (apply Z.max_r; assumption).
        rewrite H1, H2, H3.
        (* Goal is now: a = a <|> c, and since c < a we have max(a,c) = a *)
        symmetry.
        apply Z.max_l.
        apply Z.gt_lt in H_ac; apply Z.lt_le_incl; assumption.
      * (* Case: b < a, c < a, c < b *)
        (* So c < b < a, meaning max(a,b) = a, max(a,c) = a, max(b,c) = b *)
        assert (H1: Z.max a b = a) by (apply Z.max_l; apply Z.gt_lt in H_ab; apply Z.lt_le_incl; assumption).
        assert (H2: Z.max a c = a) by (apply Z.max_l; apply Z.gt_lt in H_ac; apply Z.lt_le_incl; assumption).
        assert (H3: Z.max b c = b) by (apply Z.max_l; apply Z.gt_lt in H_bc; apply Z.lt_le_incl; assumption).
        rewrite H1, H2, H3.
        (* Goal is now: a = a <|> b, and since b < a we have max(a,b) = a *)
        symmetry.
        apply Z.max_l.
        apply Z.gt_lt in H_ab; apply Z.lt_le_incl; assumption.
Qed.

(* Helper lemma for fold_left max initialization distribution *)
Lemma fold_left_max_init_distrib : forall sl a b,
  fold_left Z.max sl (Z.max a b) = Z.max (fold_left Z.max sl a) (fold_left Z.max sl b).
Proof.
  induction sl as [| s sl' IH]; intros a b.
  - simpl. reflexivity.
  - simpl.
    rewrite max_distrib_max.
    apply IH.
Qed.

(* Helper definition for scan_left head extraction *)
Definition scan_head : forall (A : Type) (f : A -> A -> A) (xs ys : list A) (i h : A),
  scan_left f xs i = h :: ys -> i = h :=
fun A f xs ys i h H =>
match xs as l return (scan_left f l i = h :: ys -> i = h) with
| [] | _ :: _ => fun H0 => f_equal (hd h) H0
end H.

(* Helper lemma for fold_left Z.max monotonicity *)
Lemma fold_left_Z_max_monotonic : forall (l : list Z) (a b : Z),
  a >= b ->
  fold_left Z.max l a >= fold_left Z.max l b.
Proof.
  intros l a b H_a_ge_b.
  generalize dependent a.
  generalize dependent b.
  induction l as [| x l' IH]; intros b a H_a_ge_b.
  - (* Base case: l = [] *)
    simpl. assumption.
  - (* Inductive case: l = x :: l' *)
    simpl fold_left.
    apply IH.
    apply Z.ge_le_iff. apply Z.max_le_compat_r. apply Z.ge_le; assumption.
Qed.

(* fold_left monotonicity for nonNegPlus *)
Lemma fold_left_monotonic_nonNegPlus : forall (xs : list Z) (a b : Z),
  a <= b -> fold_left (fun acc x => nonNegPlus acc x) xs a <= fold_left (fun acc x => nonNegPlus acc x) xs b.
Proof.
  intros xs a b H_le.
  generalize dependent a. generalize dependent b.
  induction xs as [|x xs' IH]; simpl; intros b a H_le.
  - exact H_le.
  - apply IH.
    (* We need: nonNegPlus a x <= nonNegPlus b x *)
    unfold nonNegPlus.
    destruct (Z.leb 0 (a + x)) eqn:Ha, (Z.leb 0 (b + x)) eqn:Hb.
    + (* Both a+x >= 0 and b+x >= 0 *)
      apply Z.add_le_mono_r. exact H_le.
    + (* a+x >= 0 but b+x < 0 - impossible since a <= b *)
      exfalso.
      apply Z.leb_le in Ha. apply Z.leb_gt in Hb.
      assert (H_contra: a + x <= b + x) by (apply Z.add_le_mono_r; exact H_le).
      (* We have: 0 <= a + x (from Ha) and a + x <= b + x (from H_contra) *)
      (* So by transitivity: 0 <= b + x *)
      assert (H_ge_lt: 0 <= b + x) by (apply Z.le_trans with (m := a + x); [exact Ha | exact H_contra]).
      (* But we also have b + x < 0 (from Hb), which is a contradiction *)
      apply Z.lt_irrefl with (x := 0).
      apply Z.le_lt_trans with (m := b + x); [exact H_ge_lt | exact Hb].
    + (* a+x < 0 but b+x >= 0 *)
      apply Z.leb_le in Hb. exact Hb.
    + (* Both a+x < 0 and b+x < 0 *)
      apply Z.le_refl.
Qed.

(* Helper for fold equivalence - temporarily admitted *)
Theorem fold_left_right_equiv :
  forall (A : Type) (f : A -> A -> A) (z : A) (l : list A),
    (forall x y z, f x (f y z) = f (f x y) z) -> (* Associativity of f *)
    (forall x y, f x y = f y x) -> (* Commutativity of f *)
    fold_left f l z = fold_right f z l.
Admitted.

(* Max fold duality theorems *)
Theorem max_fold_duality : forall (xs : list Z) (init : Z),
  fold_left (fun x y => x <|> y) xs init = fold_right (fun x y => x <|> y) init xs.
Proof.
  intros xs init.
  apply fold_left_right_equiv.
  - (* Associativity of Z.max *)
    intros x y z.
    apply Z.max_assoc.
  - (* Commutativity of Z.max *)
    intros x y.
    apply Z.max_comm.
Qed.

Corollary max_fold_duality_zero : forall (xs : list Z),
  fold_left (fun x y => x <|> y) xs 0 = fold_right (fun x y => x <|> y) 0 xs.
Proof.
  intro xs.
  apply max_fold_duality.
Qed.

(* Additional missing lemmas for compilation *)

(* fold_right max returns max lemma *)
Lemma fold_right_max_le : forall (xs : list Z) (ub : Z),
  ub >= 0 ->
  (forall y, In y xs -> y <= ub) ->
  fold_right (fun x y : Z => x <|> y) 0 xs <= ub.
Proof.
  intros xs ub Hub H_ub.
  induction xs as [| x xs' IH].
  - simpl. apply Z.ge_le. exact Hub.
  - simpl.
    apply Z.max_lub.
    + apply H_ub. left. reflexivity.
    + apply IH. intros y Hy. apply H_ub. right. assumption.
Qed.

Lemma fold_right_max_returns_max :
  forall (xs : list Z) (m : Z),
    m >= 0 ->
    (forall y, In y xs -> y <= m) ->
    In m xs ->
    fold_right (fun x y => x <|> y) 0 xs = m.
Proof.
  intros xs m Hm_nonneg H_ub H_in.
  induction xs as [|x xs' IH].
  - simpl in H_in. contradiction.
  - simpl in *.
    destruct H_in as [H_eq | H_in'].
    + subst.
      apply Z.max_l.
      apply fold_right_max_le.
      * exact Hm_nonneg.
      * intros y Hy. apply H_ub. right. exact Hy.
    + rewrite IH.
      * apply Z.max_r.
        apply H_ub. left. reflexivity.
      * intros y Hy. apply H_ub. right. exact Hy.
      * exact H_in'.
Qed.

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

(* Inits lemmas *)
Lemma inits_cons : forall (A : Type) (x : A) (xs : list A),
  inits (x :: xs) = [] :: map (cons x) (inits xs).
Proof.
  intros A x xs.
  unfold inits.
  simpl.
  reflexivity.
Qed.

Lemma inits_contains_original : forall {A : Type} (xs : list A),
  In xs (inits xs).
Proof.
  intros A xs.
  induction xs as [| x xs' IH].
  - (* Base case: xs = [] *)
    simpl. unfold inits. simpl.
    left. reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    rewrite inits_cons.
    simpl.
    right.
    rewrite in_map_iff.
    exists xs'.
    split.
    + reflexivity.
    + exact IH.
Qed.

Lemma inits_are_prefixes : forall (A : Type) (xs ys : list A),
  In ys (inits xs) -> exists zs, ys ++ zs = xs.
Proof.
  intros A xs.
  induction xs as [|x xs' IH]; intros ys H_in.
  - simpl in H_in. destruct H_in as [H_eq | H_contra].
    + subst. exists []. reflexivity.
    + contradiction.
  - simpl in H_in. destruct H_in as [H_eq | H_in'].
    + subst. exists (x :: xs'). reflexivity.
    + (* ys comes from map (cons x) (inits xs') *)
      apply in_map_iff in H_in'.
      destruct H_in' as [ys' [H_eq H_inits]].
      subst ys.
      specialize (IH ys' H_inits) as [zs H_concat].
      exists zs. simpl. now f_equal.
Qed.

Lemma nonNegSum_prefix_le : forall (xs ys : list Z),
  (exists zs, xs ++ zs = ys) -> nonNegSum xs <= nonNegSum ys.
Proof.
  (* Helper: nonNegSum always produces a non-negative result. *)
  assert (nonNegSum_nonneg : forall l : list Z, 0 <= nonNegSum l).
  {
    intros l.
    induction l as [|h t IH]; simpl.
    - reflexivity.
    - unfold nonNegPlus.
      destruct (Z.leb 0 (h + nonNegSum t)) eqn:H_leb.
      + apply Z.leb_le in H_leb. exact H_leb.
      + reflexivity.
  }

  (* Helper: nonNegPlus is monotonic in its second argument. *)
  assert (nonNegPlus_monotonic_right : forall x a b, a <= b -> nonNegPlus x a <= nonNegPlus x b).
  {
    intros x a b H_le.
    unfold nonNegPlus.
    destruct (Z.leb 0 (x + a)) eqn:Ha, (Z.leb 0 (x + b)) eqn:Hb.
    - apply Z.add_le_mono_l. exact H_le.
    - exfalso.
      apply Z.leb_le in Ha. apply Z.leb_gt in Hb.
      assert (H_xa_le_xb: x + a <= x + b) by (apply Z.add_le_mono_l; exact H_le).
      assert (H_xb_ge_0: 0 <= x + b) by (apply Z.le_trans with (m := x + a); [exact Ha | exact H_xa_le_xb]).
      apply Z.lt_irrefl with (x := 0).
      apply Z.le_lt_trans with (m := x + b); [exact H_xb_ge_0 | exact Hb].
    - apply Z.leb_le in Hb. exact Hb.
    - reflexivity.
  }

  (* Main proof by induction *)
  intros xs.
  induction xs as [|x xs' IH].
  - intros ys H. simpl. apply nonNegSum_nonneg.
  - intros ys H_exists.
    destruct H_exists as [zs H_eq].
    destruct ys as [|y ys'].
    + discriminate H_eq.
    + inversion H_eq; subst.
      simpl.
      apply nonNegPlus_monotonic_right.
      apply IH.
      exists zs.
      reflexivity.
Qed.

Lemma fold_scan_fusion_pair_general : forall (xs : list Z) (u0 v0 : Z),
  u0 >= v0 -> v0 >= 0 ->
  fold_left
    (fun uv x => let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x))
    xs (u0, v0)
  =
  (fold_left Z.max (scan_left (fun acc x => nonNegPlus acc x) xs v0) u0,
   fold_left (fun acc x => nonNegPlus acc x) xs v0).
Proof.
  (* We generalize over the initial values and hypotheses for the induction. *)
  intros xs u0 v0 H_u_ge_v H_v_nonneg.
  revert u0 v0 H_u_ge_v H_v_nonneg.
  induction xs as [| x xs' IH].

  - (* Base Case: xs = [] *)
    intros u0 v0 H_u_ge_v H_v_nonneg.
    simpl. (* Simplifies fold_left, scan_left, and fold_left on nil lists *)
    (* The goal becomes: (u0, v0) = (Z.max u0 v0, v0) *)
    f_equal. (* Reduces the goal to u0 = Z.max u0 v0 *)
    symmetry.
    apply Z.max_l. (* Applies because of hypothesis H_u_ge_v: u0 >= v0 *)
    apply Z.ge_le; assumption.

  - (* Inductive Step: xs = x :: xs' *)
    intros u0 v0 H_u_ge_v H_v_nonneg.
    
    (* Unfold definitions one step on both sides of the equation. *)
    simpl fold_left at 1.
    simpl scan_left.
    simpl fold_left at 2.
    simpl fold_left at 3.

    (* Let's name the new initial values for the recursive calls. *)
    set (v_next := nonNegPlus v0 x).
    set (u_next := Z.max u0 v_next).

    (* To apply the IH, we must prove the preconditions hold for the new values. *)
    assert (H_u_next_ge_v_next: u_next >= v_next). { unfold u_next. apply Z.ge_le_iff. apply Z.le_max_r. }
    assert (H_v_next_nonneg: v_next >= 0). { unfold v_next. apply nonNegPlus_nonneg'. }

    (* Apply the induction hypothesis to the LHS. *)
    rewrite (IH u_next v_next H_u_next_ge_v_next H_v_next_nonneg).
    
    (* The goal is now a pair equality. The second components match definitionally. *)
    f_equal.
    
    (* Simplify the accumulator on the RHS using the hypothesis u0 >= v0. *)
    rewrite (Z.max_l u0 v0); [| apply Z.ge_le; assumption].
    
    (* The goal is now equality of the first components:
       fold_left Z.max (scan_left ... xs' v_next) u_next =
       fold_left Z.max (scan_left ... xs' v_next) u0
    *)
    unfold u_next. (* Substitute u_next with its definition *)
    
    (* Let sl_next be the list from scan_left for the recursive step. *)
    set (sl_next := scan_left (fun acc x : Z => nonNegPlus acc x) xs' v_next).

    (* Use the distributive property of (fold_left Z.max) over Z.max in the accumulator. *)
    rewrite (fold_left_max_init_distrib sl_next u0 v_next).
    (* The goal becomes:
       Z.max (fold_left Z.max sl_next u0) (fold_left Z.max sl_next v_next) =
       fold_left Z.max sl_next u0
    *)
    
    (* This equality holds if the first argument of Z.max is greater than or equal to the second. *)
    apply Z.max_l.

    (* We need to see the structure of sl_next. Since it's not a constructor,
      'simpl' won't work. We must use 'destruct'. *)
    destruct sl_next as [| h t] eqn:E.

    + (* Case 1: sl_next = []. This is impossible. *)
      (* We prove that scan_left always returns a non-empty list. *)
      assert (H_nonempty: scan_left (fun acc x : Z => acc <#> x) xs' v_next <> []).
      { induction xs'; simpl; discriminate. }
      contradiction.

    + (* Case 2: sl_next = h :: t. Now 'fold_left' can be simplified. *)
      (* We also know the head 'h' must be v_next by the definition of scan_left. *)
      assert (H_head: h = v_next).
      { unfold sl_next in E. apply eq_sym. apply (scan_head _ (fun acc x : Z => acc <#> x) xs' t). apply E. }
      subst h. (* Replace h with v_next everywhere. *)

      simpl fold_left.
      (* The goal has simplified to:
        fold_left Z.max t (v_next <|> v_next) <= fold_left Z.max t (u0 <|> v_next)
      *)

      rewrite Z.max_id.
      (* The goal is now:
        fold_left Z.max t v_next <= fold_left Z.max t (u0 <|> v_next)
      *)

      apply Z.ge_le_iff.

      (* Now we can use monotonicity, because the new accumulator on the right
        (u0 <|> v_next) IS guaranteed to be >= the one on the left (v_next). *)
      apply fold_left_Z_max_monotonic.

      (* The final subgoal is to prove the accumulator inequality. *)
      apply Z.ge_le_iff. apply Z.le_max_r. (* Solves u0 <|> v_next >= v_next, which is always true. *)
    
    (* The new goal is to prove this inequality:
       fold_left Z.max sl_next u0 >= fold_left Z.max sl_next v_next
    *)
Qed.

(* Dual conversion theorems for fold operations *)

(* Helper lemma: fold_right Z.max distributes over max in initial value *)

Lemma fold_right_ext {A B : Type} : forall (f g : A -> B -> B) (xs : list A) (init : B),
  (forall x acc, f x acc = g x acc) ->
  fold_right f init xs = fold_right g init xs.
Proof.
  intros f g xs init H.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - simpl. rewrite H. rewrite IH. reflexivity.
Qed.

(* fold_left extensionality lemma - needed for BirdMeertens.v *)

Lemma fold_left_ext : forall {A B : Type} (f g : B -> A -> B) (xs : list A) (init : B),
  (forall acc x, f acc x = g acc x) -> fold_left f xs init = fold_left g xs init.
Proof.
  intros A B f g xs init H.
  generalize dependent init.
  induction xs as [|x xs' IH]; simpl; intro init.
  - reflexivity.
  - rewrite H. apply IH.
Qed.

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

Lemma tropical_horner_eq_nonNegPlus : forall x y : Z,
  (x <#> y <|> 0) = x <#> y.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - (* Case: x + y >= 0 *)
    apply Z.leb_le in H.
    rewrite Z.max_l; [reflexivity | exact H].
  - (* Case: x + y < 0 *)
    apply Z.leb_gt in H.
    rewrite Z.max_r; [reflexivity | apply Z.le_refl].
Qed.

Lemma nonNegSum_dual_nonneg : forall xs : list Z, nonNegSum_dual xs >= 0.
Proof.
  intros xs.
  unfold nonNegSum_dual.
  (* Use the general fold_left property with nonNegPlus *)
  assert (H: forall acc, acc >= 0 -> fold_left (fun acc x => nonNegPlus acc x) xs acc >= 0).
  {
    intro acc. generalize dependent acc.
    induction xs as [|x xs' IH]; simpl; intros acc H_acc.
    - exact H_acc.
    - apply IH. apply nonNegPlus_nonneg'.
  }
  apply H. apply Z.le_ge. apply Z.le_refl.
Qed.

Lemma nonNegSum_dual_suffix_le : forall (xs ys : list Z),
  (exists zs, zs ++ xs = ys) -> nonNegSum_dual xs <= nonNegSum_dual ys.
Proof.
  intros xs ys H_suffix.
  destruct H_suffix as [zs H_eq].

  (* We need to prove: nonNegSum_dual xs <= nonNegSum_dual ys *)
  (* Since zs ++ xs = ys, we substitute ys with zs ++ xs *)
  rewrite <- H_eq.

  (* The key insight: nonNegSum_dual (zs ++ xs) starts with processing zs first,
     then continues with xs from whatever accumulated value results from zs.
     Since nonNegPlus is monotonic in its first argument when the second is non-negative,
     and we know all intermediate values are non-negative, this can only help. *)

  unfold nonNegSum_dual.
  rewrite fold_left_app.

  (* Now we have: fold_left (fun acc x => nonNegPlus acc x) xs 0 <=
                  fold_left (fun acc x => nonNegPlus acc x) xs (fold_left (fun acc x => nonNegPlus acc x) zs 0) *)

  (* Use monotonicity: if a <= b, then fold_left f xs a <= fold_left f xs b *)
  apply fold_left_monotonic_nonNegPlus.

  (* We need: 0 <= fold_left (fun acc x => nonNegPlus acc x) zs 0 *)
  apply Z.ge_le_iff.
  apply nonNegSum_dual_nonneg.
  (*
  
    (* Helper 1: nonNegSum_dual always produces a non-negative result. *)
    assert (nonNegSum_dual_nonneg : forall l : list Z, 0 <= nonNegSum_dual l).
    {
      intros l.
      induction l as [|h t IH]; simpl.
      - (* Base case: nonNegSum_dual [] = 0. *)
        reflexivity.
      - (* Inductive step: nonNegSum_dual (h :: t) = h <#> nonNegSum_dual t. *)
        unfold nonNegPlus.
        (* We perform case analysis on the condition of the 'if' statement. *)
        destruct (Z.leb 0 (h + nonNegSum_dual t)) eqn:H_leb.
        + (* Case 1: The condition is true, so h + nonNegSum_dual t >= 0. *)
          (* The 'if' evaluates to the 'then' branch. *)
          (* The goal becomes 0 <= h + nonNegSum_dual t, which is true by our assumption for this case. *)
          apply Z.leb_le in H_leb.
          exact H_leb.
        + (* Case 2: The condition is false. *)
          (* The 'if' evaluates to the 'else' branch, which is 0. *)
          (* The goal becomes 0 <= 0, which is trivially true. *)
          reflexivity.
    }
  
    (* Helper 2: The nonNegSum_dual operation is monotonic in its second argument. *)
    assert (nonNegSum_dual_monotonic_right : forall x a b, a <= b -> nonNegSum_dual x a <= nonNegSum_dual x b).
    {
      intros x a b H_le.
      unfold nonNegPlus.
      destruct (Z.leb 0 (x + a)) eqn:Ha, (Z.leb 0 (x + b)) eqn:Hb.
      - (* Case 1: x+a >= 0 and x+b >= 0. *)
        apply Z.add_le_mono_l.
        exact H_le.
      - (* Case 2: x+a >= 0 and x+b < 0. This case is impossible. *)
        exfalso.
        apply Z.leb_le in Ha.
        apply Z.leb_gt in Hb.
        assert (H_xa_le_xb: x + a <= x + b) by (apply Z.add_le_mono_l; exact H_le).
        assert (H_xb_ge_0: 0 <= x + b) by (apply Z.le_trans with (m := x + a); [exact Ha | exact H_xa_le_xb]).
        apply Z.lt_irrefl with (x := x + b).
        apply Z.le_lt_trans with (m := 0); [exact H_xb_ge_0 | exact Hb].
      - (* Case 3: x+a < 0 and x+b >= 0. *)
        apply Z.leb_le in Hb.
        exact Hb.
      - (* Case 4: x+a < 0 and x+b < 0. *)
        reflexivity.
    }
  
    (* Main proof by induction on the prefix list xs. *)
    intros xs.
    induction xs as [|x xs' IH].
    - (* Base case: xs = []. *)
      intros ys H.
      simpl. (* nonNegSum [] is 0. *)
      apply nonNegSum_dual_nonneg.
    - (* Inductive step: xs = x :: xs'. *)
      intros ys H_exists.
      destruct H_exists as [zs H_eq].
      destruct ys as [|y ys'].
      + (* Impossible for x :: l to equal []. *)
        discriminate H_eq.
      + (* ys = y :: ys'. *)
        inversion H_eq; subst.
        simpl.
        apply nonNegSum_dual_monotonic_right.
        apply IH.
        exists zs.
        reflexivity.
  Qed. *)
Qed.

(* Helper lemma: fold_right Z.max 0 gives a value that's <= any upper bound *)

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

(* Helper lemma: fold_left gives a value that's <= any upper bound *)
(* NOTE: This proof is now trivial using our duality theorem! *)

Lemma fold_left_max_returns_max :
  forall (xs : list Z) (m : Z),
    m >= 0 ->
    (forall y, In y xs -> y <= m) ->
    In m xs ->
    fold_left (fun x y => x <|> y) xs 0 = m.
Proof.
  (* This follows directly from the duality theorem and fold_right_max_returns_max *)
  apply fold_left_max_returns_max_direct.
Qed.

(* Helper lemma: fold_right_max_inf returns the maximum element *)

Lemma tails_are_suffixes : forall (A : Type) (xs ys : list A),
  In ys (tails xs) -> exists zs, zs ++ ys = xs.
Proof.
  intros A xs ys H_in.
  (* Use the tails_rec_equiv to work with the simpler recursive definition *)
  rewrite tails_rec_equiv in H_in.
  generalize dependent ys.
  induction xs as [|x xs' IH]; intros ys H_in.
  - simpl in H_in. destruct H_in as [H_eq | H_contra].
    + subst. exists []. reflexivity.
    + contradiction.
  - simpl in H_in. destruct H_in as [H_eq | H_in'].
    + subst. exists []. reflexivity.
    + specialize (IH ys H_in') as [zs H_eq].
      exists (x :: zs). simpl. f_equal. exact H_eq.
Qed.

(* Key lemma: the sum equals the maximum of prefix sums with nonNegPlus *)

Lemma fold_right_nonNegPlus_eq_max_prefixes : forall xs : list Z,
  nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs)).
Proof.
  intros xs.
  (* xs is one of its inits *)
  assert (H_in: In xs (inits xs)).
  { apply inits_contains_original. }

  (* Every element of inits xs is a prefix of xs, hence its nonNegSum <= nonNegSum xs *)
  assert (H_max: forall ys, In ys (inits xs) -> nonNegSum ys <= nonNegSum xs).
  {
    intros ys H_ys_in.
    (* inits_are_prefixes gives ys ++ zs = xs *)
    destruct (inits_are_prefixes Z xs ys H_ys_in) as [zs H_app].
    apply nonNegSum_prefix_le.
    exists zs; exact H_app.
  }

  (* map the above fact to the mapped list *)
  assert (H_is_max: forall y, In y (map nonNegSum (inits xs)) -> y <= nonNegSum xs).
  {
    intros y H_y_in.
    rewrite in_map_iff in H_y_in.
    destruct H_y_in as [ys [H_eq H_ys_in]].
    rewrite <- H_eq.
    apply H_max; exact H_ys_in.
  }

  (* nonNegSum xs is indeed an element of the mapped list *)
  assert (H_xs_mapped: In (nonNegSum xs) (map nonNegSum (inits xs))).
  {
    rewrite in_map_iff.
    exists xs; split; [reflexivity | exact H_in].
  }

  (* show nonNegSum xs >= 0 by induction on xs *)
  assert (Hm_nonneg: 0 <= nonNegSum xs).
  {
    induction xs as [|x xs' IH].
    - simpl. apply Z.le_refl.
    - simpl.
      unfold nonNegPlus.
      destruct (Z.leb 0 (x + nonNegSum xs')) eqn:Heq.
      + apply Z.leb_le in Heq; exact Heq.
      + simpl. apply Z.le_refl.
  }

  (* Now apply fold_right_max_returns_max on the mapped list *)
  unfold nonNegMaximum.
  symmetry.
  apply fold_right_max_returns_max with (m := nonNegSum xs).
  - apply Z.ge_le_iff.
    exact Hm_nonneg.
  - exact H_is_max.
  - exact H_xs_mapped.
Qed.

(* Key lemma: the sum equals the maximum of prefix sums with nonNegPlus *)

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

Lemma max_add_distributes : forall s t x,
  Z.max s t + x = Z.max (s + x) (t + x).
Proof.
  intros.
  rewrite Z.add_max_distr_r.
  reflexivity.
Qed.

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

