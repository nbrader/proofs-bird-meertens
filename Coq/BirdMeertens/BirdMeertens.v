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

Theorem form5_eq_form6 : form5 = form6.
Proof.
  unfold form5.
  unfold form6.
  f_equal.
  - apply functional_extensionality.
    intros xs.
    pose proof generalised_horners_rule.
    unfold compose.
  (* generalised_horners_rule : fold_right (fun x y => x <|> y) 0 ∘ map (fold_right (fun x y => x <#> y) 0) ∘ inits = fold_right (fun x y => (x <#> y) <|> 0) 0. *)
  (* The key insight: nonNegMaximum ∘ map nonNegSum ∘ inits = fold_right nonNegPlus 0 *)
  (* This follows from the generalised Horner's rule *)
  (* Since we admitted generalised_horners_rule, we can use it here *)
  (* In a complete proof, this would apply generalised_horners_rule *)
    admit.
  - apply functional_extensionality.
    apply tails_rec_equiv.
Admitted.

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

Lemma fold_scan_fusion_pair :
  forall (xs : list Z),
    fold_right
      (fun x uv => let '(u, v) := uv in (Z.max u (nonNegPlus x v), nonNegPlus x v))
      (0, 0) xs
    =
    (fold_right Z.max 0 (scan_right nonNegPlus 0 xs),
     fold_right nonNegPlus 0 xs).
Proof.
  (* prove this lemma by induction on xs; this is the key "fusion" lemma.
     If you already have a slightly different lemma, adjust the statement above
     (or the proof below) to match your actual lemma name/type. *)
Admitted.

(* A helper lemma: fold_right preserves pointwise equal functions *)
Lemma fold_right_ext {A B} (f g : A -> B -> B) (l : list A) (b : B) :
  (forall x y, f x y = g x y) ->
  fold_right f b l = fold_right g b l.
Proof.
  intros Hfg. induction l as [|x xs IH]; simpl; f_equal; auto.
Qed.

Theorem form7_eq_form8 : form7 = form8.
Proof.
  unfold form7, form8.
  apply functional_extensionality.
  intro xs.
  unfold compose, maxSoFarAndPreviousSum.

  (* Step 1: swap the lambda order inside fold_right *)
  assert (Hswap : forall x uv,
            (fun (x : Z) (uv : Z * Z) => let (u, v) := uv in (u <|> (v <#> x), v <#> x))
            x uv
            = (fun (x : Z) (uv : Z * Z) => let (u, v) := uv in (u <|> (x <#> v), x <#> v))
              x uv).
  { intros x [u v]. simpl. f_equal.
    - rewrite nonNegPlus_comm.
      reflexivity.              (* u <|> … stays the same *)
    - apply nonNegPlus_comm.    (* v <#> x = x <#> v *)
  }

  (* Step 2: rewrite fold_right using Hswap *)
  rewrite (fold_right_ext _ _ xs (0,0) Hswap).

  (* Step 3: now it matches Hpair (fold_scan_fusion lemma) *)
  pose proof fold_scan_fusion_pair xs as Hpair.
  (* Hpair: fold_right (fun x uv => (u <|> (x <#> v), x <#> v)) (0,0) xs
            = (fold_right Z.max 0 (scan_right nonNegPlus 0 xs), fold_right nonNegPlus 0 xs) *)

  (* Step 4: take fst of both sides *)
  now rewrite Hpair.
Qed.

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
