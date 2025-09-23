(* Minimal Lemmas.v - ONLY indirect dependencies for MajorLemmas.v *)
(* Does NOT contain theorems already in MajorLemmas.v - only their dependencies *)

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

(* ===== CORE DEFINITIONS ===== *)
Notation "x <|> y" := (Z.max x y) (at level 50, left associativity).

Definition nonNegPlus (x y : Z) : Z :=
  if Z.leb 0 (x + y) then x + y else 0.

Notation "x <#> y" := (nonNegPlus x y) (at level 40, left associativity).

Definition nonNegSum (xs : list Z) : Z := fold_right nonNegPlus 0%Z xs.
Definition nonNegSum_dual (xs : list Z) : Z := fold_left (fun acc x => nonNegPlus acc x) xs 0.
Definition nonNegMaximum : list Z -> Z := fold_right (fun x y => x <|> y) 0.
Definition nonNegMaximum_dual (xs : list Z) : Z := fold_left (fun x y => x <|> y) xs 0.

Definition maxSoFarAndPreviousSum : Z -> (Z * Z) -> (Z * Z) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.

Definition maxSoFarAndPreviousSum_dual : (Z * Z) -> Z -> (Z * Z) := fun uv x => match uv with
  | (u, v) => let w := (v <#> x) in (u <|> w, w)
end.


(* ===== PROPERTIES ===== *)
Lemma nonNegPlus_nonneg' : forall x y : Z, nonNegPlus x y >= 0.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - apply Z.leb_le in H. apply Z.le_ge. exact H.
  - apply Z.le_ge. apply Z.le_refl.
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
  intros l1 l2.
  induction l1 as [|x xs IH]; simpl.
  - rewrite Z.max_r.
    + reflexivity.
    + apply fold_max_nonneg.
  - rewrite IH. rewrite Z.max_assoc. reflexivity.
Qed.

Lemma tropical_horner_eq_nonNegPlus : forall x y : Z,
  (x <#> y <|> 0) = x <#> y.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - apply Z.leb_le in H.
    rewrite Z.max_l; [reflexivity | exact H].
  - apply Z.leb_gt in H.
    rewrite Z.max_r; [reflexivity | apply Z.le_refl].
Qed.

Lemma fold_left_monotonic_nonNegPlus : forall (xs : list Z) (a b : Z),
  a <= b -> fold_left (fun acc x => nonNegPlus acc x) xs a <= fold_left (fun acc x => nonNegPlus acc x) xs b.
Proof.
  intros xs a b H_le.
  generalize dependent a. generalize dependent b.
  induction xs as [|x xs' IH]; simpl; intros b a H_le.
  - exact H_le.
  - apply IH.
    unfold nonNegPlus.
    destruct (Z.leb 0 (a + x)) eqn:Ha, (Z.leb 0 (b + x)) eqn:Hb.
    + apply Z.add_le_mono_r. exact H_le.
    + exfalso.
      apply Z.leb_le in Ha. apply Z.leb_gt in Hb.
      assert (H_contra: a + x <= b + x) by (apply Z.add_le_mono_r; exact H_le).
      assert (H_ge_lt: 0 <= b + x) by (apply Z.le_trans with (m := a + x); [exact Ha | exact H_contra]).
      apply Z.lt_irrefl with (x := 0).
      apply Z.le_lt_trans with (m := b + x); [exact H_ge_lt | exact Hb].
    + apply Z.leb_le in Hb. exact Hb.
    + apply Z.le_refl.
Qed.

(* ===== SUFFIX/PREFIX PROPERTIES ===== *)

Lemma nonNegSum_dual_suffix_le : forall (xs ys : list Z),
  (exists zs, zs ++ xs = ys) -> nonNegSum_dual xs <= nonNegSum_dual ys.
Proof.
  intros xs ys H_suffix.
  destruct H_suffix as [zs H_eq].
  rewrite <- H_eq.
  unfold nonNegSum_dual.
  rewrite fold_left_app.
  apply fold_left_monotonic_nonNegPlus.
  apply Z.ge_le_iff.
  apply nonNegSum_dual_nonneg.
Qed.

(* Inits properties *)
Lemma inits_contains_original : forall {A : Type} (xs : list A),
  In xs (inits xs).
Proof.
  intros A xs.
  induction xs as [| x xs' IH].
  - simpl. unfold inits. simpl. left. reflexivity.
  - rewrite inits_cons. simpl. right.
    rewrite in_map_iff. exists xs'. split; [reflexivity | exact IH].
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
    + apply in_map_iff in H_in'.
      destruct H_in' as [ys' [H_eq H_inits]].
      subst ys.
      specialize (IH ys' H_inits) as [zs H_concat].
      exists zs. simpl. now f_equal.
Qed.

Lemma nonNegSum_prefix_le : forall (xs ys : list Z),
  (exists zs, xs ++ zs = ys) -> nonNegSum xs <= nonNegSum ys.
Proof.
  (* First, we prove two helper lemmas inside this proof. *)

  (* Helper 1: nonNegSum always produces a non-negative result. *)
  assert (nonNegSum_nonneg : forall l : list Z, 0 <= nonNegSum l).
  {
    intros l.
    induction l as [|h t IH]; simpl.
    - (* Base case: nonNegSum [] = 0. *)
      reflexivity.
    - (* Inductive step: nonNegSum (h :: t) = h <#> nonNegSum t. *)
      unfold nonNegPlus.
      (* We perform case analysis on the condition of the 'if' statement. *)
      destruct (Z.leb 0 (h + nonNegSum t)) eqn:H_leb.
      + (* Case 1: The condition is true, so h + nonNegSum t >= 0. *)
        (* The 'if' evaluates to the 'then' branch. *)
        (* The goal becomes 0 <= h + nonNegSum t, which is true by our assumption for this case. *)
        apply Z.leb_le in H_leb.
        exact H_leb.
      + (* Case 2: The condition is false. *)
        (* The 'if' evaluates to the 'else' branch, which is 0. *)
        (* The goal becomes 0 <= 0, which is trivially true. *)
        reflexivity.
  }

  (* Helper 2: The nonNegPlus operation is monotonic in its second argument. *)
  assert (nonNegPlus_monotonic_right : forall x a b, a <= b -> nonNegPlus x a <= nonNegPlus x b).
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
      apply Z.lt_irrefl with (x := 0).
      apply Z.le_lt_trans with (m := x + b); [exact H_xb_ge_0 | exact Hb].
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
    apply nonNegSum_nonneg.
  - (* Inductive step: xs = x :: xs'. *)
    intros ys H_exists.
    destruct H_exists as [zs H_eq].
    destruct ys as [|y ys'].
    + (* Impossible for x :: l to equal []. *)
      discriminate H_eq.
    + (* ys = y :: ys'. *)
      inversion H_eq; subst.
      simpl.
      apply nonNegPlus_monotonic_right.
      apply IH.
      exists zs.
      reflexivity.
Qed.

Lemma tails_are_suffixes : forall (A : Type) (xs ys : list A),
  In ys (tails xs) -> exists zs, zs ++ ys = xs.
Proof.
  intros A xs ys H_in.
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

Theorem fold_left_right_equiv :
  forall (A : Type) (f : A -> A -> A) (z : A) (l : list A),
    (forall x y z, f x (f y z) = f (f x y) z) -> (* Associativity of f *)
    (forall x y, f x y = f y x) -> (* Commutativity of f *)
    fold_left f l z = fold_right f z l.
Proof.
  intros A f z l H_assoc H_comm.
  apply fold_symmetric.
  - apply H_assoc.
  - apply H_comm.
Qed.

Theorem max_fold_duality : forall (xs : list Z) (init : Z),
  fold_left (fun x y => x <|> y) xs init = fold_right (fun x y => x <|> y) init xs.
Proof.
  intros xs init.
  apply fold_left_right_equiv.
  - intros x y z. apply Z.max_assoc.
  - intros x y. apply Z.max_comm.
Qed.

Corollary max_fold_duality_zero : forall (xs : list Z),
  fold_left (fun x y => x <|> y) xs 0 = fold_right (fun x y => x <|> y) 0 xs.
Proof.
  intro xs. apply max_fold_duality.
Qed.

Lemma fold_right_max_le : forall (xs : list Z) (ub : Z),
  ub >= 0 ->
  (forall y, In y xs -> y <= ub) ->
  fold_right (fun x y : Z => x <|> y) 0 xs <= ub.
Proof.
  intros xs ub Hub H_ub.
  induction xs as [| x xs' IH].
  - simpl. apply Z.ge_le. exact Hub.
  - simpl. apply Z.max_lub.
    + apply H_ub. left. reflexivity.
    + apply IH. intros y Hy. apply H_ub. right. assumption.
Qed.

(* Helper lemmas for fold_scan_fusion_pair_general *)
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

Lemma fold_left_max_init_distrib : forall sl a b,
  fold_left Z.max sl (Z.max a b) = Z.max (fold_left Z.max sl a) (fold_left Z.max sl b).
Proof.
  induction sl as [| s sl' IH]; intros a b.
  - simpl. reflexivity.
  - simpl.
    (* After simpl, the goal is:
       fold_left Z.max sl' (Z.max (Z.max a b) s) =
       Z.max (fold_left Z.max sl' (Z.max a s)) (fold_left Z.max sl' (Z.max b s))
    *)
    (* First, apply max_distrib_max to transform (Z.max a b) in the LHS *)
    assert (Z.max (Z.max a b) s = Z.max (Z.max a s) (Z.max b s)) as H_distrib.
    { apply max_distrib_max. }
    rewrite H_distrib.
    (* Now the goal is:
       fold_left Z.max sl' (Z.max (Z.max a s) (Z.max b s)) =
       Z.max (fold_left Z.max sl' (Z.max a s)) (fold_left Z.max sl' (Z.max b s))
    *)
    (* Apply IH to distribute fold_left over Z.max *)
    apply IH.
Qed.

Definition scan_head : forall (A : Type) (f : A -> A -> A) (xs ys : list A) (i h : A),
  scan_left f xs i = h :: ys -> i = h :=
fun A f xs ys i h H =>
match xs as l return (scan_left f l i = h :: ys -> i = h) with
| [] | _ :: _ => fun H0 => f_equal (hd h) H0
end H.

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

(* Helper lemma for distributivity - used by horners_rule_right *)
Lemma fold_right_map_mult_dist : forall (x : Z) (f : list Z -> Z) (lss : list (list Z)),
  x * fold_right Zplus 0 (map f lss) = fold_right Zplus 0 (map (fun ls => x * f ls) lss).
Proof.
  intros x f lss.
  induction lss as [| ls lss' IH].
  - simpl.
    (* Goal: x * 0 = 0 *)
    apply Z.mul_0_r.
  - simpl. rewrite <- IH.
    (* Goal: x * (f ls + fold_right Z.add 0 (map f lss')) = x * f ls + fold_right Z.add 0 (map (fun ls0 => x * f ls0) lss') *)
    rewrite Z.mul_add_distr_l.
    reflexivity.
Qed.
