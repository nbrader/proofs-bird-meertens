Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

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
Definition nonNegPlus (x y : Z) : Z :=
  if Z.leb 0 (x + y) then x + y else 0.

Notation "x <#> y" := (nonNegPlus x y) (at level 50, left associativity).
Notation "x <|> y" := (Z.max x y) (at level 50, left associativity).

Definition nonNegSum (xs : list Z) : Z := fold_right nonNegPlus 0%Z xs.

Definition nonNegMaximum : list Z -> Z := fold_right (fun x y => x <|> y) 0.

Definition nonNegMaximum_dual (xs : list Z) : Z := fold_left (fun x y => x <|> y) xs 0.

(* Refs:
 - form8 -> (* Refs: NONE *)
*)
Definition maxSoFarAndPreviousSum : Z -> (Z * Z) -> (Z * Z) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.

Notation "x <.> y" := (maxSoFarAndPreviousSum x y) (at level 50, left associativity).

(* Dual helper functions (swap fold_right↔fold_left) *)
Definition nonNegSum_dual (xs : list Z) : Z := fold_left (fun acc x => nonNegPlus acc x) xs 0%Z.

Definition maxSoFarAndPreviousSum_dual : (Z * Z) -> Z -> (Z * Z) := fun uv x => match uv with
  | (u, v) => let w := (v <#> x) in (u <|> w, w)
end.

(* Refs:
 - form4_eq_form5 -> (* Refs: NONE *)
*)
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

(* Refs:
 - form2_eq_form3 -> (* Refs: NONE *)
*)
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

Lemma app_concat [A : Type] : forall (l : list (list A)),
  concat l = fold_right (@app A) [] l.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

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
    - apply IH. lia.
  }
  apply H. lia.
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


(* Instead, let's add a simple provable lemma about nonNegPlus *)
Lemma nonNegPlus_comm : forall x y : Z, nonNegPlus x y = nonNegPlus y x.
Proof.
  intros x y.
  unfold nonNegPlus.
  rewrite Z.add_comm.
  reflexivity.
Qed.

Definition distributes_over_max (op : Z -> Z -> Z) := forall s t x, op (Z.max s t) x = Z.max  (op s x) (op t x).

(* Helper lemma: addition distributes over max *)
Lemma max_add_distributes : forall s t x,
  Z.max s t + x = Z.max (s + x) (t + x).
Proof.
  intros.
  rewrite Z.add_max_distr_r.
  reflexivity.
Qed.

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
Lemma inits_cons : forall (A : Type) (x : A) (xs : list A),
  inits (x :: xs) = [] :: map (cons x) (inits xs).
Proof.
  intros A x xs.
  unfold inits.
  simpl.
  reflexivity.
Qed.
    
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

Lemma nonNegPlus_nonneg : forall x y : Z, 
  x >= 0 -> y >= 0 -> nonNegPlus x y = x + y.
Proof.
  intros x y Hx Hy.
  unfold nonNegPlus.
  assert (H: Z.leb 0 (x + y) = true).
  { apply Z.leb_le. apply Z.add_nonneg_nonneg; [apply Z.ge_le_iff; exact Hx | apply Z.ge_le_iff; exact Hy]. }
  rewrite H.
  reflexivity.
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
Lemma nonNegPlus_nonneg' : forall x y : Z, nonNegPlus x y >= 0.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - (* Case: 0 <= x + y, so nonNegPlus returns x + y *)
    apply Z.leb_le in H.
    apply Z.le_ge.
    exact H.
  - (* Case: 0 > x + y, so nonNegPlus returns 0 *)
    apply Z.le_ge.
    apply Z.le_refl.
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

(* Helper theorem: scan_left corresponds to mapping fold_left over inits *)
Theorem scan_left_fold_correspondence : forall (xs : list Z),
  scan_left (fun acc x => nonNegPlus acc x) xs 0 =
  map (fun prefix => fold_left (fun acc x => nonNegPlus acc x) prefix 0) (inits_rec xs).
Proof.
  intro xs.
  exact (@scan_left_inits_rec_fold Z Z (fun acc x => nonNegPlus acc x) xs 0).
Qed.

Lemma Z_max_l' : forall a b, a >= b -> a <|> b = a.
Proof. intros; unfold Z.max; apply Z.max_l; lia. Qed.

(* Dual version of fold_scan_fusion_pair - works with fold_left and scan_left *)
(* This would require a more complex proof due to the left-fold structure *)
(* For now, we'll admit this to demonstrate the dual structure *)
Lemma fold_scan_fusion_pair_dual :
  forall (xs : list Z),
    fold_left
      (fun uv x => let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x))
      xs (0, 0)
    =
    (fold_left Z.max (scan_left (fun acc x => nonNegPlus acc x) xs 0) 0,
     fold_left (fun acc x => nonNegPlus acc x) xs 0).
Proof.
  intros xs.
  (* Generalized form with arbitrary accumulators *)
  assert (H_general: forall ys u_acc v_acc,
    v_acc >= 0 -> u_acc >= v_acc ->
    fold_left
      (fun uv x => let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x))
      ys (u_acc, v_acc)
    =
    (fold_left Z.max (scan_left (fun acc x => nonNegPlus acc x) ys v_acc) u_acc,
     fold_left (fun acc x => nonNegPlus acc x) ys v_acc)).
  {
    induction ys as [|y ys' IH]; intros u_acc v_acc H_v_nonneg H_u_ge_v.
    - (* Base case: ys = [] *)
      simpl. f_equal.
      symmetry.
      apply Z_max_l'. lia.
    - (* Inductive case: ys = y :: ys' *)
      simpl fold_left at 1. simpl scan_left at 1.
      set (v_new := nonNegPlus v_acc y).
      set (u_new := Z.max u_acc v_new).

      assert (H_v_new_nonneg: v_new >= 0) by (apply nonNegPlus_nonneg').
      assert (H_u_new_ge_v_new: u_new >= v_new).
        { subst u_new. lia. }

      rewrite (IH u_new v_new H_v_new_nonneg H_u_new_ge_v_new). clear IH.
      simpl.
      subst v_new.
      subst u_new.
      repeat (rewrite fold_left_right_equiv).
      + f_equal.
        admit.
      + intros a b c. apply Z.max_assoc.
      + intros a b. apply Z.max_comm.
      + intros a b c. admit.
      + intros a b. admit.
      + intros a b c. apply Z.max_assoc.
      + intros a b. apply Z.max_comm.
  }
  (* Specialize with (0,0) *)
  specialize (H_general xs 0 0).
  replace 0 with (Z.of_nat 0) by reflexivity.
  apply H_general; lia.
Admitted.

(* fold_right extensionality lemma - needed for BirdMeertens.v *)
Lemma fold_right_ext : forall {A B : Type} (f g : A -> B -> B) (xs : list A) (init : B),
  (forall x acc, f x acc = g x acc) -> fold_right f init xs = fold_right g init xs.
Proof.
  intros A B f g xs init H.
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

(* Monoid framework for Horner's rule using TailsMonoid *)
Section HornerViaMonoids.

(*
To Do:
 - Make a max monoid with negative infinity element
 - Test the max monoid with negative infinity element in variation of Bird Meertens proof
*)

End HornerViaMonoids.

(* Key insight: the tropical Horner operation is equivalent to nonNegPlus *)
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

(* This approach was incorrect - the distributivity property doesn't hold in general *)
(* Let me try a different approach for the main proof *)

(* Helper lemma: inits xs contains xs as its last element *)
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

(* Helper lemma: removing elements from a list can only decrease nonNegSum *)
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


(* Helper lemma: nonNegSum_dual is always non-negative *)
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

(* Helper lemma: fold_left is monotonic in initial value for nonNegPlus *)
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

(* Helper lemma: removing elements from a list can only decrease nonNegSum *)
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
Lemma fold_right_max_le : forall (xs : list Z) (ub : Z),
  ub >= 0 ->
  (forall y, In y xs -> y <= ub) -> fold_right (fun x y : Z => x <|> y) 0 xs <= ub.
Proof.
  intros xs ub Hub_nonneg H_ub.
  induction xs as [| x xs' IH].
  - simpl. apply Z.ge_le_iff. assumption.
  - simpl.
    apply Z.max_lub.
    + apply H_ub. left. reflexivity.
    + apply IH. intros y Hy. apply H_ub. right. assumption.
Qed.

(* Helper lemma: fold_right Z.max 0 returns the maximum element when it's in the list *)
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
      (* Goal: Z.max m (fold_right Z.max 0 xs') = m *)
      (* We have m >= 0 and forall y in xs', y <= m *)
      (* Strategy: prove fold_right Z.max 0 xs' <= m, then use Z.max_l *)
      apply Z.max_l.
      (* Now need to prove: fold_right Z.max 0 xs' <= m *)
      apply fold_right_max_le.
      * exact Hm_nonneg.
      * intros y Hy. apply H_ub. right. exact Hy.
    + (* m is in xs', so by IH: fold_right Z.max 0 xs' = m *)
      rewrite IH.
      * (* Goal: Z.max x m = m *)
        apply Z.max_r.
        (* Need: x <= m *)
        apply H_ub. left. reflexivity.
      * (* IH precondition: forall y, In y xs' -> y <= m *)
        intros y Hy. apply H_ub. right. exact Hy.
      * (* IH precondition: In m xs' *)
        exact H_in'.
Qed.

(* ========== DUALITY THEOREMS FOR REUSING PROOFS ========== *)

(* Import the fold_left_right_equiv theorem from CoqUtilLib *)
From Coq Require Import Arith.

(* Key duality theorem: for max operations, fold_left and fold_right are equivalent *)
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

(* Specialized version for our common pattern with init = 0 *)
Corollary max_fold_duality_zero : forall (xs : list Z),
  fold_left (fun x y => x <|> y) xs 0 = fold_right (fun x y => x <|> y) 0 xs.
Proof.
  intro xs.
  apply max_fold_duality.
Qed.

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
Lemma fold_promotion_dual : nonNegMaximum_dual ∘ (concat (A:=Z)) = nonNegMaximum_dual ∘ map nonNegMaximum_dual.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros x.
  unfold nonNegMaximum_dual.
  (* Convert both sides to fold_right using duality *)
  rewrite max_fold_duality_zero.
  rewrite max_fold_duality_zero.
  (* Convert the map function to use fold_right instead of fold_left *)
  assert (H_map_eq: map (fun xs => fold_left (fun x y : Z => x <|> y) xs 0) x =
                    map (fun xs => fold_right (fun x y : Z => x <|> y) 0 xs) x).
  {
    induction x as [|xs xss IH].
    - simpl. reflexivity.
    - simpl. f_equal.
      + rewrite max_fold_duality_zero. reflexivity.
      + exact IH.
  }
  rewrite H_map_eq.
  (* Now we can apply the original fold_promotion *)
  unfold nonNegMaximum.
  assert (H_promotion := fold_promotion).
  unfold compose in H_promotion.
  unfold nonNegMaximum in H_promotion.
  apply (equal_f H_promotion x).
Qed.

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

(* Helper lemma: elements of tails are suffixes *)
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
  nonNegSum_dual xs = nonNegMaximum_dual (map nonNegSum_dual (tails xs)).
Proof.
  (* intros xs.
  (* xs is one of its inits *)
  assert (H_in: In xs (inits xs)).
  { apply inits_contains_original. }

  (* Every element of inits xs is a prefix of xs, hence its nonNegSum_dual <= nonNegSum_dual xs *)
  assert (H_max: forall ys, In ys (inits xs) -> nonNegSum_dual ys <= nonNegSum_dual xs).
  {
    intros ys H_ys_in.
    (* inits_are_prefixes gives ys ++ zs = xs *)
    destruct (inits_are_prefixes Z xs ys H_ys_in) as [zs H_app].
    apply nonNegSum_dual_suffix_le.
    exists zs; exact H_app.
  }

  (* map the above fact to the mapped list *)
  assert (H_is_max: forall y, In y (map nonNegSum_dual (inits xs)) -> y <= nonNegSum_dual xs).
  {
    intros y H_y_in.
    rewrite in_map_iff in H_y_in.
    destruct H_y_in as [ys [H_eq H_ys_in]].
    rewrite <- H_eq.
    apply H_max; exact H_ys_in.
  }

  (* nonNegSum_dual xs is indeed an element of the mapped list *)
  assert (H_xs_mapped: In (nonNegSum_dual xs) (map nonNegSum_dual (inits xs))).
  {
    rewrite in_map_iff.
    exists xs; split; [reflexivity | exact H_in].
  }

  (* show nonNegSum_dual xs >= 0 by induction on xs *)
  assert (Hm_nonneg: 0 <= nonNegSum_dual xs).
  {
    induction xs as [|x xs' IH].
    - simpl. apply Z.le_refl.
    - simpl.
      unfold nonNegPlus.
      destruct (Z.leb 0 (x + nonNegSum_dual xs')) eqn:Heq.
      + apply Z.leb_le in Heq; exact Heq.
      + simpl. apply Z.le_refl.
  }

  (* Now apply fold_right_max_returns_max on the mapped list *)
  unfold nonNegMaximum_dual.
  symmetry.
  apply fold_left_max_returns_max with (m := nonNegSum_dual xs).
  - apply Z.ge_le_iff.
    exact Hm_nonneg.
  - exact H_is_max.
  - exact H_xs_mapped.
Qed. *)
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

(* Dual versions of the generalised Horner's rule lemmas *)
(* These work with fold_left instead of fold_right and tails instead of inits *)

(* For the dual approach, we need to work with the complex tails structure *)
(* Since the tails structure is complex, we'll focus on proving the scan-fold fusion first *)

(* The key insight is that we need proper dual versions of the existing lemmas *)
(* Let's create a basic framework that builds up the needed proofs step by step *)

Lemma generalised_horners_rule_dual :
  (fun xs => fold_left (fun acc x => nonNegPlus acc x) xs 0) = nonNegMaximum_dual ∘ map nonNegSum_dual ∘ tails.
Proof.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  (* This follows directly from fold_left_nonNegPlus_eq_max_suffixes *)
  apply fold_left_nonNegPlus_eq_max_suffixes.
Qed.

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
