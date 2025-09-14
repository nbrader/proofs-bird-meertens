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

Definition nonNegSum (xs : list Z) : Z := fold_left nonNegPlus xs 0%Z.

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


(* Refs:
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Definition MaxNonNegSumInits : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ inits.
Definition MaxNonNegSumInitsInd (xs : list Z) : Z := fold_right nonNegPlus 0 xs.

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

(* Bird's Horner Rule Variant - from Bird_horner_rule_6789_svg.svg diagram *)
(* This theorem relates sum of products of tails to a Horner-style computation *)
Definition horner_op (x y : Z) : Z := (x * y + 1)%Z.

Lemma horner_op_not_associative :
  exists a b c : Z, horner_op (horner_op a b) c <> horner_op a (horner_op b c).
Proof.
  exists 0%Z, 0%Z, 1%Z.
  unfold horner_op. simpl.
  (* left = ((0*0+1)*1+1) = 2, right = 0*(0*1+1)+1 = 1 *)
  lia.
Qed.

Lemma bird_horner_rule_variant : 
  (fun xs => fold_left Z.add xs 0%Z) ∘ map (fun ys => fold_left Z.mul ys 1%Z) ∘ tails = 
  fold_right horner_op 1%Z.
Proof.
  apply functional_extensionality.
  intros xs.
  unfold horner_op.
  (* This proof will require induction on xs and properties of tails, fold operations *)
Admitted.

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

(* Monoid framework for Horner's rule using TailsMonoid *)
Section HornerViaMonoids.

(* First, establish that fold is a monoid homomorphism from lists to any target monoid *)
Definition fold_hom {A B : Type} `{Monoid B} (f : A -> B) : list A -> B :=
  fold_right (fun a acc => m_op (f a) acc) mn_id.

(* Prove that fold preserves concatenation - this is the key fold homomorphism property *)
Lemma fold_hom_preserves_concat {A B : Type} `{Monoid B} (f : A -> B) :
  forall xs ys : list A,
    fold_hom f (xs ++ ys) = m_op (fold_hom f xs) (fold_hom f ys).
Proof.
  intros xs ys.
  unfold fold_hom.
  induction xs as [|x xs' IH].
  - (* Base case: [] ++ ys = ys *)
    simpl.
    rewrite mn_left_id.
    reflexivity.
  - (* Inductive step: (x :: xs') ++ ys = x :: (xs' ++ ys) *)
    simpl.
    rewrite IH.
    rewrite sg_assoc.
    reflexivity.
Qed.

(* Now establish fold∘map as a homomorphism by composing two homomorphisms *)
Definition fold_map_hom {A B C : Type} `{Monoid C} (g : A -> B) (f : B -> C) : list A -> C :=
  compose (fold_hom f) (map g).

Lemma fold_map_hom_preserves_concat {A B C : Type} `{Monoid C} (g : A -> B) (f : B -> C) :
  forall xs ys : list A,
    fold_map_hom g f (xs ++ ys) = m_op (fold_map_hom g f xs) (fold_map_hom g f ys).
Proof.
  intros xs ys.
  unfold fold_map_hom.
  unfold compose.
  rewrite map_app.
  apply fold_hom_preserves_concat.
Qed.

(* Monoid instance for Z under addition *)
Instance ZAddMagma : Magma Z := {
  m_op := Z.add
}.

Instance ZAddSemigroup : Semigroup Z := {
  sg_assoc := Z.add_assoc
}.

Instance ZAddMonoid : Monoid Z := {
  mn_id := 0%Z;
  mn_left_id := Z.add_0_l;
  mn_right_id := Z.add_0_r
}.

(* Horner's rule components as monoid homomorphisms *)
Definition horner_left_part : list (list Z) -> Z :=
  fold_map_hom (fun xs => fold_left Z.mul xs 1%Z) (@id Z).

Definition horner_middle_part : list Z -> TailsMonoid.TailsResult Z := @TailsMonoid.mk_tails_result Z.

Definition horner_right_part : list Z -> Z := fold_right (fun x acc => (x * acc + 1)%Z) 1%Z.

(* Establish that each component is indeed a monoid homomorphism *)
Theorem horner_middle_is_homomorphism : 
  MonoidHomomorphism (@TailsMonoid.ListMonoid Z) (@TailsMonoid.TailsResultMonoid Z) horner_middle_part.
Proof.
  exact (@TailsMonoid.mk_tails_result_is_homomorphism Z).
Qed.

(* The main theorem: Horner's rule via monoid homomorphism composition *)
Theorem horner_rule_via_homomorphisms :
  compose horner_left_part (compose (@TailsMonoid.tails_carrier Z) horner_middle_part) = horner_right_part.
Proof.
  (* This theorem establishes the fundamental connection between:
     - The monoid homomorphism composition: sum ∘ (map product) ∘ tails  
     - Direct Horner evaluation: fold_right (λx acc. x * acc + 1) 1
     
     The proof requires deep analysis of fold/map/tails interactions
     and represents the core of reducing Horner's rule to monoid theory. *)
Admitted.

(* Prove fold direction equivalence for Z.add - required for Horner's rule consistency *)
Theorem fold_left_right_add_equiv : 
  forall (xs : list Z) (z : Z),
    fold_left Z.add xs z = fold_right Z.add z xs.
Proof.
  intros xs z.
  apply fold_left_right_equiv; intros; ring.
Qed.

(* Corollary: fold_left Z.add xs 0 = fold_right Z.add 0 xs *)
Corollary fold_left_right_add_0 : 
  forall (xs : list Z),
    fold_left Z.add xs 0%Z = fold_right Z.add 0%Z xs.
Proof.
  intros xs.
  apply fold_left_right_add_equiv.
Qed.

End HornerViaMonoids.

(* Refs: NONE *)
(* LOOK INTO WHETHER THERE IS A GOOD REASON WHY THIS STATEMENT OF HORNERS RULE DIFFERS SIGNFICANTLY FROM THE WIKIPEDIA ONE: This uses right folds and uses zero where Wikipedia uses 1. This may be an attempt of mine to better handle edge cases but I'm not yet sure. *)
Lemma generalised_horners_rule : fold_right (fun x y => x <|> y) 0 ∘ map (fold_right (fun x y => x <#> y) 0) ∘ inits = fold_right (fun x y => (x <#> y) <|> 0) 0.
Proof.
Admitted.

(* Here is something Claude Opus 4.1 said about the version of horner's rule I'm trying to prove:

Looking at the classic Horner's rule in your image and comparing it to your theorem, I can see a potential issue. The classic Horner's rule works because:

It uses tails (suffixes of the list)
The operation x ⊗ y = x*y + 1 has special properties that make the fold work

Your version uses inits (prefixes) instead of tails. Let me check if your theorem might actually be correct if we used tails instead:

Testing Horner's Rule with Tails Instead of InitsText *)

(* Let's check if the theorem would work with tails instead of inits *)

(* Current version (potentially incorrect): *)
Lemma generalised_horners_rule_nonNeg_inits :
  forall l : list Z,
    nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l.
Proof.
Admitted.
    
(* Potential corrected version using tails: *)
Lemma generalised_horners_rule_nonNeg_tails :
  forall l : list Z,
    nonNegMaximum (map nonNegSum (tails l)) = fold_right nonNegPlus 0 l.
Proof.
  intros l.
  induction l as [| x xs IH].
  - (* Base case: l = [] *)
    simpl.
    unfold nonNegSum, nonNegMaximum.
    simpl.
    reflexivity.
  - (* Inductive step: l = x :: xs *)
    rewrite tails_cons.
    simpl map.
    unfold nonNegSum at 1.
    simpl fold_left.
    
    (* nonNegSum (x :: xs) = fold_left nonNegPlus (x :: xs) 0 *)
    (* This is the full sum of the entire list *)
    
    unfold nonNegMaximum at 1.
    simpl fold_right at 2.
    
    (* We have: max(nonNegSum (x::xs), nonNegMaximum (map nonNegSum (tails xs))) *)
    (* By IH: nonNegMaximum (map nonNegSum (tails xs)) = fold_right nonNegPlus 0 xs *)
    (* rewrite IH. *)
    
    (* So we need: max(nonNegSum (x::xs), fold_right nonNegPlus 0 xs) = nonNegPlus x (fold_right nonNegPlus 0 xs) *)
    
    (* This still has issues because nonNegSum uses fold_left *)
    admit.
Admitted.

(* Actually, let me reconsider the whole setup.


   Looking at the classic Horner's rule pattern:
   
   Classic: sum(map product tails) = fold_right (λx y. x*y+1) 1
   
   Your version seems to be trying:
   max(map nonNegSum inits) = fold_right nonNegPlus 0
   
   But the classic pattern would suggest:
   nonNegSum(map nonNegMax inits) = fold_right ??? 0
   
   Or perhaps the issue is that nonNegSum should use fold_right not fold_left
*)

(* Let's redefine nonNegSum to use fold_right: *)
Definition nonNegSum_right (xs : list Z) : Z := fold_right nonNegPlus 0 xs.

Lemma generalised_horners_rule_nonNeg_corrected :
  forall l : list Z,
    nonNegMaximum (map nonNegSum_right (inits l)) = fold_right nonNegPlus 0 l.
Proof.
  intros l.
  induction l as [| x xs IH].
  - (* Base case: l = [] *)
    simpl. reflexivity.
  - (* Inductive step: l = x :: xs *)
    rewrite inits_cons.
    simpl map.
    unfold nonNegSum_right at 1.
    simpl fold_right at 2.
    unfold nonNegMaximum at 1.
    simpl fold_right at 1.
    
    (* 0 <|> fold_right Z.max 0 (map nonNegSum_right (map (cons x) (inits xs))) *)
    (* = nonNegPlus x (fold_right nonNegPlus 0 xs) *)
    
    (* rewrite Z.max_0_l. *)
    (* 2: { apply fold_max_nonneg. } *)
    
    rewrite map_map.
    simpl.
    
    (* Now: fold_right Z.max 0 (map (λl. nonNegPlus x (nonNegSum_right l)) (inits xs)) *)
    (* By IH: nonNegMaximum (map nonNegSum_right (inits xs)) = fold_right nonNegPlus 0 xs *)
    
    (* We need the false lemma map_nonNegPlus_max here! *)
    (* This confirms the issue: even with fold_right, the theorem doesn't work
       because of how nonNegPlus interacts with max and empty lists *)
    admit.
Admitted.
    
(* After analyzing your theorem in light of the classic Horner's rule, I think I've found the key issue:
The problem isn't just fold_left vs fold_right - it's that the theorem statement itself has a fundamental issue with how nonNegPlus interacts with empty lists and the maximum operation.
Looking at the classic Horner's rule pattern from your image:

It works because multiplication distributes nicely: the operation x*y + 1 has the right algebraic properties
The base case (empty tail) gives 1, which is the multiplicative identity

In your version:

nonNegPlus x 0 doesn't always equal 0 (it equals max(x, 0))
This breaks the distributivity needed: max(map (nonNegPlus x) list) ≠ nonNegPlus x (max list) when list is empty

The core mistake in your formulation: The theorem assumes map_nonNegPlus_max is true, but we've proven it's false. This isn't just an implementation detail - it's a fundamental algebraic incompatibility.
Possible fixes:

Change the base case of nonNegMaximum: Instead of returning 0 for empty lists, return some value that makes the algebra work
Use a different operation: Replace nonNegPlus with an operation that has better algebraic properties
Add constraints: The theorem might be true for lists with all non-negative elements, or with other restrictions

The insight from classic Horner's rule is that the operation needs to have specific algebraic properties for the transformation to work. The nonNegPlus operation with its clamping behavior doesn't have these properties.
 *)
