Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Open Scope R_scope.

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

(* To Do: Use the fact that Rmax forms a monoid and lists are the free monoid to show that maximum is the unique monoid homomorphism. *)
(* NOTE: I think I'm going to have to work with option types again and interpret the extra value as negative infinity for this to work because otherwise this gets needlessly inelegant.
         A consequence of this will be that I'll have to replace all the 0s in the theoresm with Nones. *)
Lemma maximum_distr (xs : list R) (ys : list R) : maximum (xs ++ ys) = Rmax (maximum xs) (maximum ys).
Proof.
  unfold maximum.
  rewrite fold_left_app.
  
Admitted.

Definition Rsum : list R -> R := fun xs => fold_left (fun x acc => x + acc) xs 0.

(* x <#> y = (x + y) <|> 0 *)
Definition RnonzeroSum : R -> R -> R := fun x y => Rmax (x + y) 0.

(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
Definition RMaxSoFarAndPreviousNonzeroSum : (R * R) -> R -> (R * R) := fun uv x => match uv with
  | (u, v) => let w := RnonzeroSum v x in (Rmax u w, w)
end.