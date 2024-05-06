Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Open Scope R_scope.

Notation "g ∘ f" := (compose g f) (at level 40, left associativity).

Fixpoint tails {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | _ :: xs' => xs :: tails xs'
end.

(* Define the inits function using reverse and tails *)
Definition inits {A : Type} (xs : list A) : list (list A) :=
  map (@rev A) (tails (rev xs)).

Definition concat {A : Type} : list (list A) -> list A := @List.concat A.

Definition segs {A : Type} : list A -> list (list A) := concat ∘ map tails ∘ inits.

Definition foldl {A B : Type} (f : B -> A -> B) (i : B) (xs : list A) : B := fold_left f xs i.

Fixpoint scanl {A B : Type} (f : B -> A -> B) (i : B) (xs : list A) {struct xs} : list B :=
  i ::
    match xs with
    | nil => nil
    | x :: xs' => scanl f (f i x) xs'
    end.

(* Definition maximum : list R -> R := fun xs => match xs with
  | [] => 0 (* This would be incorrect for lists of negatives but:
                1) We consider only lists of at least 1 positive and 1 negative because alternatives are trivial:
                    - Lists without negatives have a MaxSegSum equal to the sum of the list
                    - Lists without positives have a MaxSegSum equal to the least negative member
                    To Do: Make this explicit in a more general MaxSegSum function which covers these other cases as described above.
                2) segs, inits and scanl don't map to the empty list and the only way to get the empty list
                      from map and concat is from the empty list and a list of empty lists respectively so nothing
                      we can get from proceeding functions in the forms below will trigger this case anyway. *)
  | x' :: xs' => (fold_left Rmax xs 0.)
end. *)
Definition maximum : list R -> R := fun xs => fold_left Rmax xs 0.

Definition Rsum : list R -> R := fun xs => fold_left (fun x acc => x + acc) xs 0.

(* x <#> y = (x + y) <|> 0 *)
Definition RnonzeroSum : R -> R -> R := fun x y => Rmax (x + y) 0.

(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
Definition RMaxSoFarAndPreviousNonzeroSum : (R * R) -> R -> (R * R) := fun uv x => match uv with
  | (u, v) => let w := RnonzeroSum v x in (Rmax u w, w)
end.


(* Forms of MaxSegSum *)
Definition form1 : list R -> R := maximum ∘ map Rsum ∘ segs.
Definition form2 : list R -> R := maximum ∘ map Rsum ∘ concat ∘ map tails ∘ inits.
Definition form3 : list R -> R := maximum ∘ concat ∘ map (map Rsum) ∘ map tails ∘ inits.
Definition form4 : list R -> R := maximum ∘ map maximum ∘ map (map Rsum) ∘ map tails ∘ inits.
Definition form5 : list R -> R := maximum ∘ map (maximum ∘ map Rsum ∘ tails) ∘ inits.
Definition form6 : list R -> R := maximum ∘ map (foldl RnonzeroSum 0) ∘ inits.
Definition form7 : list R -> R := maximum ∘ scanl RnonzeroSum 0.
Definition form8 : list R -> R := fst ∘ foldl RMaxSoFarAndPreviousNonzeroSum (0,0).

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
  - rewrite IH.    (* Apply the induction hypothesis *)
    reflexivity.
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

Lemma Rmax_assoc : forall (x y z : R), Rmax x (Rmax y z) = Rmax (Rmax x y) z.
Proof.
  intros x y z.
  unfold Rmax.
  destruct (Rle_dec x (Rmax y z)) eqn:Hxyz.
  - destruct (Rle_dec y z) eqn:Hyz.
    + (* Case x ≤ z ∧ y ≤ z *)
      simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r2).
              apply r0.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r1).
              apply r0.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
    + simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           reflexivity.
        -- assert (~ x <= z).
           ++ intro.
              assert (z < y).
              ** apply Rnot_le_lt.
                 apply n.
              ** assert (y < x).
                 --- apply Rnot_le_lt.
                     apply n0.
                 --- assert (z < x).
                     +++ apply (Rlt_trans z y x H0 H1).
                     +++ apply Rlt_not_le in H2.
                         contradiction.
          ++ destruct (Rle_dec x z) as [Htrue|Hfalse].
             +++ contradiction.
             +++ reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- destruct (Rle_dec y z).
           ++ contradiction.
           ++ reflexivity.
        -- destruct (Rle_dec x z).
          --- assert (~ x <= z).
            +++ intro.
                assert (z < y).
                *** apply Rnot_le_lt.
                  apply n.
                *** assert (y < x).
                  ---- apply Rnot_le_lt.
                      apply n1.
                  ---- assert (z < x).
                      ++++ apply (Rlt_trans z y x H0 H1).
                      ++++ apply Rlt_not_le in H2.
                          contradiction.
            +++ contradiction.
          --- reflexivity.
  - destruct (Rle_dec y z) eqn:Hyz.
    + (* Case x ≤ z ∧ y ≤ z *)
      simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r1).
              apply r.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r0).
              apply r.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
    + simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           reflexivity.
        -- assert (~ x <= z).
           ++ intro.
              assert (z < y).
              ** apply Rnot_le_lt.
                 apply n0.
              ** assert (y < x).
                 --- apply Rnot_le_lt.
                     apply n1.
                 --- assert (z < x).
                     +++ apply (Rlt_trans z y x H0 H1).
                     +++ apply Rlt_not_le in H2.
                         contradiction.
          ++ destruct (Rle_dec x z) as [Htrue|Hfalse].
             +++ contradiction.
             +++ reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- destruct (Rle_dec y z).
           ++ contradiction.
           ++ reflexivity.
        -- destruct (Rle_dec x z).
          --- assert (~ x <= z).
            +++ intro.
                assert (z < y).
                *** apply Rnot_le_lt.
                  apply n0.
                *** assert (y < x).
                  ---- apply Rnot_le_lt.
                      apply n2.
                  ---- assert (z < x).
                      ++++ apply (Rlt_trans z y x H0 H1).
                      ++++ apply Rlt_not_le in H2.
                          contradiction.
            +++ contradiction.
          --- reflexivity.
Qed.

(* To Do: Use the fact that Rmax forms a monoid and lists are the free monoid to show that maximum is the unique monoid homomorphism. *)
(* NOTE: I think I'm going to have to work with option types again and interpret the extra value as negative infinity for this to work because otherwise this gets needlessly inelegant.
         A consequence of this will be that I'll have to replace all the 0s in the theoresm with Nones. *)
Lemma maximum_distr (xs : list R) (ys : list R) : maximum (xs ++ ys) = Rmax (maximum xs) (maximum ys).
Proof.
  unfold maximum.
  rewrite fold_left_app.
  
Admitted.

Definition RfoldlSum := foldl (fun x y => x + y) 0.

Lemma foldl_promotion : RfoldlSum ∘ concat = RfoldlSum ∘ map RfoldlSum.
Proof.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - unfold compose.
    rewrite concat_cons.
    rewrite map_cons.
    unfold RfoldlSum.
    simpl.
    rewrite Rplus_0_l.
    unfold foldl.
    rewrite fold_left_app.
    fold RfoldlSum.
    induction xs.
    + simpl.
      reflexivity.
    + simpl.
      rewrite fold_left_app.
      admit.
Admitted.

Lemma foldl_promotion1 : RfoldlSum ∘ concat = RfoldlSum ∘ map RfoldlSum.
Proof.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - unfold compose.
    induction x, xs.
    + unfold concat, RfoldlSum.
      simpl.
      f_equal.
      ring.
    + rewrite concat_cons.
      rewrite app_nil_l.
      unfold compose in IH.
      unfold concat in IH.
      rewrite IH.
      rewrite map_cons.
      rewrite map_cons.
      rewrite map_cons.
      unfold RfoldlSum.
      simpl.
      rewrite Rplus_0_l.
      rewrite Rplus_0_l.
      rewrite Rplus_0_l.
      fold RfoldlSum.
      reflexivity.
    + rewrite map_cons.
      simpl.
      rewrite app_nil_r.
      unfold RfoldlSum.
      simpl.
      rewrite Rplus_0_l.
      rewrite Rplus_0_l.
      reflexivity.
    + admit.
Admitted.

Lemma fold_promotion : maximum ∘ concat = maximum ∘ map maximum.
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - 
Admitted.

Theorem form1_eq_form2 : form1 = form2.
Proof.
  reflexivity.
Qed.

Theorem form2_eq_form3 : form2 = form3.
Proof.
  unfold form2.
  unfold form3.
  f_equal.
  rewrite compose_assoc.
  rewrite (compose_assoc _ _ _ _ (concat ∘ map tails) (map Rsum) maximum).
  rewrite <- (compose_assoc _ _ _ _ (map tails) concat (map Rsum)).
  rewrite (map_promotion Rsum).
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
  rewrite (map_distr (map Rsum) tails).
  rewrite (map_distr maximum (compose (map Rsum) tails)).
  reflexivity.
Qed.
