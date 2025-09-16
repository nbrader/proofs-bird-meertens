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
Require Import Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersTac.
Require Import Coq.Numbers.NatInt.NZAxioms.
Require Import Coq.Init.Nat.
Require Import Coq.Structures.GenericMinMax.

Open Scope Z_scope.

(* Define nonNegPlus using Qle_bool to convert the proposition to a boolean *)
Definition nonNegPlus (x y : Z) : Z :=
  if Z.leb 0 (x + y) then x + y else 0.

Notation "x <#> y" := (nonNegPlus x y) (at level 50, left associativity).
Notation "x <|> y" := (Z.max x y) (at level 50, left associativity).

Definition nonNegSum (xs : list Z) : Z := fold_right nonNegPlus 0%Z xs.

Definition nonNegMaximum : list Z -> Z := fold_right (fun x y => x <|> y) 0.

(* Refs:
 - form8 -> (* Refs: NONE *)
*)
Definition maxSoFarAndPreviousSum : Z -> (Z * Z) -> (Z * Z) := fun x uv => match uv with
  | (u, v) => let w := (v <#> x)  in (u <|> w, w)
end.

Notation "x <.> y" := (maxSoFarAndPreviousSum x y) (at level 50, left associativity).

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

Lemma fold_promotion : nonNegMaximum ∘ concat = nonNegMaximum ∘ map nonNegMaximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH].
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
    assert (H_sx_ge_tx: s + x >= t + x). { lia. }
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
    assert (H_tx_ge_sx: t + x >= s + x). { lia. }
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
    rewrite Z.max_r; [reflexivity | lia].
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
    rewrite Z.max_r; [reflexivity | lia].
Qed.

Lemma nonNegPlus_nonneg : forall x y : Z, 
  x >= 0 -> y >= 0 -> nonNegPlus x y = x + y.
Proof.
  intros x y Hx Hy.
  unfold nonNegPlus.
  assert (H: Z.leb 0 (x + y) = true).
  { apply Z.leb_le. lia. }
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

(* fold_right extensionality lemma - needed for BirdMeertens.v *)
Lemma fold_right_ext : forall {A B : Type} (f g : A -> B -> B) (xs : list A) (init : B),
  (forall x acc, f x acc = g x acc) -> fold_right f init xs = fold_right g init xs.
Proof.
  intros A B f g xs init H.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - simpl. rewrite H. rewrite IH. reflexivity.
Qed.

(* Monoid framework for Horner's rule using TailsMonoid *)
Section HornerViaMonoids.

(*
To Do:
 - Make a max monoid with negative infinity element
 - Test the max monoid with negative infinity element in variation of Bird Meertens proof
*)

End HornerViaMonoids.

Lemma generalised_horners_rule : fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits.
Proof.
Admitted.

Lemma generalised_horners_rule' : nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec = nonNegMaximum ∘ map nonNegSum ∘ tails_rec.
Proof.
  rewrite <- generalised_horners_rule.
Admitted.
