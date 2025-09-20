(* Proof Strategy and Helper Lemmas for Bird-Meertens Formalization *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import BirdMeertens.Lemmas.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

(* The key distributivity property we need *)
Lemma max_add_distributes : forall s t x,
  Z.max s t + x = Z.max (s + x) (t + x).
Proof.
  intros. 
  rewrite Z.add_max_distr_r.
  reflexivity.
Qed.

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
