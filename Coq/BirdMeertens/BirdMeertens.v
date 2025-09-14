Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.

Require Import Coq.Structures.GenericMinMax.
Open Scope Z_scope.

Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import CoqUtilLib.ListFunctions.

(* Forms of MaxSegSum *)
Definition form1 : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ segs.
Definition form2 : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ concat ∘ map inits ∘ tails.
Definition form3 : list Z -> Z := nonNegMaximum ∘ concat ∘ map (map nonNegSum) ∘ map inits ∘ tails.
Definition form4 : list Z -> Z := nonNegMaximum ∘ map nonNegMaximum ∘ map (map nonNegSum) ∘ map inits ∘ tails.
Definition form5 : list Z -> Z := nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails.
Definition form6 : list Z -> Z := nonNegMaximum ∘ map (fold_right nonNegPlus 0) ∘ tails_rec.
Definition form7 : list Z -> Z := nonNegMaximum ∘ scan_right nonNegPlus 0.
Definition form8 : list Z -> Z := fst ∘ fold_right maxSoFarAndPreviousSum (0, 0).

Theorem form1_eq_form2 : form1 = form2.
Proof.
  reflexivity.
Qed.

Theorem form2_eq_form3 : form2 = form3.
Proof.
  unfold form2, form3.
  f_equal.
  rewrite compose_assoc.
  rewrite (compose_assoc _ _ _ _ (concat ∘ map inits) (map nonNegSum) nonNegMaximum).
  rewrite <- (compose_assoc _ _ _ _ (map inits) concat (map nonNegSum)).
  rewrite (map_promotion nonNegSum).
  reflexivity.
Qed.

Theorem form3_eq_form4 : form3 = form4.
Proof.
  unfold form3.
  unfold form4.
  rewrite compose_assoc.
  rewrite fold_promotion.
  reflexivity.
Qed.

Theorem form4_eq_form5 : form4 = form5.
Proof.
  unfold form4.
  unfold form5.
  f_equal.
  rewrite compose_assoc.
  rewrite compose_assoc.
  rewrite (map_distr (map nonNegSum) inits).
  rewrite (map_distr nonNegMaximum (compose (map nonNegSum) inits)).
  reflexivity.
Qed.

Lemma nonNegPlus_equiv : forall x y : Z, nonNegPlus x y = x <#> y.
Proof. intros. unfold nonNegPlus, "<#>". reflexivity. Qed.

Lemma nonNegMaximum_equiv : forall l : list Z,
  nonNegMaximum l = fold_right (fun x y => x <|> y) 0 l.
Proof.
  intros l.
  unfold nonNegMaximum.  (* if needed, otherwise just fold_right directly *)
  reflexivity.
Qed.

Lemma fold_left_nil :
  forall (A B : Type) (f : A -> B -> A) (a : A),
    fold_left f [] a = a.
Proof. reflexivity. Qed.

Lemma map_nonNegPlus_max_is_false : 
  ~ (forall x l, nonNegMaximum (map (fun ys => nonNegPlus x ys) l) = nonNegPlus x (nonNegMaximum l)).
Proof.
  intro H.
  (* Instantiate with x = 1 and l = [] *)
  specialize (H 1 []).
  
  (* Simplify the left side *)
  simpl in H.
  unfold nonNegMaximum in H.
  simpl in H.
  
  (* Now H states: 0 = nonNegPlus 1 0 *)
  unfold nonNegPlus in H.
  simpl in H.
  
  (* Since 1 + 0 = 1 and 0 <=? 1 is true *)
  (* We have nonNegPlus 1 0 = 1 *)
  (* So H becomes: 0 = 1 *)
  
  (* This is a contradiction *)
  discriminate H.
Qed.

Lemma generalised_horners_rule_nonNeg :
  forall l : list Z,
    nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l.
Proof.
  intros l.
  induction l as [| x xs IH].
  - (* Base case: l = [] *)
    simpl. reflexivity.
  - (* Inductive step: l = x :: xs *)
    simpl.
    unfold nonNegSum, nonNegMaximum, nonNegPlus.

    (* Step 1: fold_left on [] gives 0 *)
    rewrite (fold_left_nil Z Z (fun x0 y => if 0 <=? x0 + y then x0 + y else 0) 0).

    (* Step 2: rewrite map (cons x) (inits xs) pointwise *)
    rewrite map_map. (* outer map *)

    admit.
Admitted.

(* Auxiliary lemma to connect nonNegSum / nonNegMaximum with <#> / <|> *)
Lemma map_horner_sub :
  forall l : list Z,
    nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l.
Proof.
  intros l.
  (* This is exactly the same as generalised_horners_rule_nonNeg *)
  apply generalised_horners_rule_nonNeg.
Qed.

(* Now we can lift it over a list of lists using map_ext *)
Theorem form5_eq_form6 : form5 = form6.
Proof.
  unfold form5, form6.
  f_equal.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  f_equal.
  (* Need to show: map (nonNegMaximum ∘ map nonNegSum ∘ inits) (tails xs) 
                   = map (fold_right nonNegPlus 0) (tails_rec xs) *)
  (* Now both sides use tails xs *)
  apply map_ext.
  intros l.
  (* Need: nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l *)
  (* This is exactly what generalised_horners_rule_nonNeg states *)
  apply generalised_horners_rule_nonNeg.
  apply functional_extensionality.
  apply tails_rec_equiv.
Qed.

Theorem form6_eq_form7 : form6 = form7.
Proof.
  unfold form6, form7.
  (* Need to prove: nonNegMaximum ∘ map (fold_right nonNegPlus 0) ∘ tails_rec = nonNegMaximum ∘ scan_right nonNegPlus 0 *)
  (* The key insight: we need to show the inner functions are equal *)
  apply functional_extensionality.
  intro xs.
  unfold compose.
  (* Now the goal is: nonNegMaximum (map (fold_right nonNegPlus 0) (tails_rec xs)) = nonNegMaximum (scan_right nonNegPlus 0 xs) *)
  (* We need to lift the list-level equality to the nonNegMaximum level *)
  f_equal.
  (* This gives us: map (fold_right nonNegPlus 0) (tails_rec xs) = scan_right nonNegPlus 0 xs *)
  (* Which is exactly what scan_right_tails_rec_fold gives us, but in reverse *)
  symmetry.
  exact (@scan_right_tails_rec_fold Z Z nonNegPlus 0 xs).
Qed.

(* fold_right respects pointwise equality of functions *)
Lemma fold_right_ext {A B} (f g : A -> B -> B) (l : list A) (b : B) :
  (forall x y, f x y = g x y) -> fold_right f b l = fold_right g b l.
Proof.
  intros Hfg; induction l as [|x xs IH]; simpl; f_equal; auto.
Qed.

(* form7 = form8 *)
Theorem form7_eq_form8 : form7 = form8.
Proof.
  unfold form7, form8.
  apply functional_extensionality; intro xs.
  unfold compose, maxSoFarAndPreviousSum.

  (* Step 1: swap the lambda inside fold_right *)
  assert (Hswap : forall x uv,
            (fun (x : Z) (uv : Z * Z) => let (u, v) := uv in (u <|> (v <#> x), v <#> x)) x uv
            = (fun (x : Z) (uv : Z * Z) => let (u, v) := uv in (u <|> (x <#> v), x <#> v)) x uv).
  { intros x [u v]; simpl; f_equal.
    - rewrite nonNegPlus_comm; reflexivity.
    - apply nonNegPlus_comm. }

  (* Step 2: rewrite fold_right using pointwise equality *)
  rewrite (fold_right_ext _ _ xs (0,0) Hswap).

  (* Step 3: apply the fusion lemma *)
  pose proof fold_scan_fusion_pair xs as Hpair.

  (* Step 4: take fst of both sides *)
  now rewrite Hpair.
Qed.

(* MaxSegSum equivalence *)
Theorem MaxSegSum_Equivalence : form1 = form8.
Proof.
  rewrite form1_eq_form2.
  rewrite form2_eq_form3.
  rewrite form3_eq_form4.
  rewrite form4_eq_form5.
  rewrite form5_eq_form6.
  rewrite form6_eq_form7.
  rewrite form7_eq_form8.
  reflexivity.
Qed.

Print Assumptions MaxSegSum_Equivalence.
(*
Axioms:
generalised_horners_rule_nonNeg : forall l : list Z, nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l
functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
*)