Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Open Scope R_scope.

(* tails' :: [a] -> [[a]]
tails' [] = [[]]
tails' xs@(_:xs') = xs : tails' xs' *)
Fixpoint tails {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | _ :: xs' => xs :: tails xs'
end.

Fixpoint init {A : Type} (xs : list A) : option (list A) :=
  match xs with
  | [] => None
  | [x] => Some []  (* The only initial segment of a single-element list is the empty list *)
  | x :: xs' => 
      match init xs' with
      | None => Some []  (* Should not happen since xs' is part of a non-empty list *)
      | Some xs'' => Some (x :: xs'')
      end
  end.

(* Definition NonEmpty {A : Type} (xs : list A) : Prop := xs <> []. *)

(* (* inits' :: [a] -> [[a]]
inits' [] = [[]]
inits' xs = inits' (init xs) ++ [xs] *)
Fixpoint inits {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | xs' => match init xs' with
    | None => [[]]
    | Some i => app (inits i) [xs']
  end
end.

Cannot guess decreasing argument of fix. *)

(* Define a recursive function to reverse a list *)
Fixpoint reverse {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => reverse xs ++ [x]
  end.

(* Reverse a list using an accumulator for efficiency *)
Fixpoint reverse_acc {A : Type} (l acc : list A) : list A :=
  match l with
  | [] => acc
  | x :: xs => reverse_acc xs (x :: acc)
  end.

(* Wrapper function to reverse a list by calling reverse_acc with an empty accumulator *)
Definition reverse' {A : Type} (l : list A) : list A :=
  reverse_acc l [].

(* Define the inits function using reverse and tails *)
Definition inits {A : Type} (xs : list A) : list (list A) :=
  map (reverse) (tails (reverse xs)).

(* Example list to evaluate *)
Definition example_list := [1; 2; 3].

(* Compute inits of the example list *)
Definition computed_inits := inits example_list.

(* Printing the computed inits for demonstration *)
(* Eval compute in (inits example_list). *)


Definition double : R -> R := fun x => 2*x.
Definition inc : R -> R := fun x => x+1.
Definition myFunc : R -> R := compose inc double.
Definition x := myFunc 10.

Theorem x_eval : x = 21.
Proof.
  unfold x.
  unfold myFunc.
  unfold inc.
  unfold double.
  unfold compose.
  ring.
Qed.

Definition concat {A : Type} : list (list A) -> list A := fun xs => fold_right (fun x acc => x ++ acc) [] xs.

(* segs :: [a] -> [[a]] *)
(* segs = concat . map tails . inits *)
Definition segs {A : Type} : list A -> list (list A) := compose concat (compose (map tails) inits).

Definition foldl {A B : Type} (f : B -> A -> B) (i : B) (xs : list A) : B := fold_left f xs i.

Fixpoint scanl {A B : Type} (f : B -> A -> B) (i : B) (xs : list A) {struct xs} : list B :=
  i ::
    match xs with
    | nil => nil
    | x :: xs' => scanl f (f i x) xs'
    end.

Definition maximum : list R -> R := fun xs => match xs with
  | [] => 0 (* This would be incorrect for lists of negatives but:
                1) We consider only lists of at least 1 positive and 1 negative because alternatives are trivial:
                    - Lists without negatives have a MaxSegSum equal to the sum of the list
                    - Lists without positives have a MaxSegSum equal to the least negative member
                    To Do: Make this explicit in a more general MaxSegSum function which covers these other cases as described above.
                2) segs, inits and scanl don't map to the empty list and the only way to get the empty list
                      from map and concat is from the empty list and a list of empty lists respectively so nothing
                      we can get from proceeding functions in the forms below will trigger this case anyway. *)
  | x' :: xs' => (fold_right (fun y acc => Rmax y acc) x' xs')
end.

Definition Rsum : list R -> R := fun xs => fold_right (fun x acc => x + acc) 0 xs.

(* x <#> y = (x + y) <|> 0 *)
Definition RnonzeroSum : R -> R -> R := fun x y => Rmax (x + y) 0.

(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
Definition RMaxSoFarAndPreviousNonzeroSum : (R * R) -> R -> (R * R) := fun uv x => match uv with
  | (u, v) => let w := RnonzeroSum v x in (Rmax u w, w)
end.


(* Forms of MaxSegSum *)
(* form1, form2, form3, form4, form5, form6, form7, form8 :: (Ord a, Num a) => [a] -> a *)
(* form1 = maximum . map sum . segs *)
Definition form1 : list R -> R := compose maximum (compose (map Rsum) segs).

(* form2 = maximum . map sum . concat . map tails . inits *)
Definition form2 : list R -> R := compose maximum (compose (map Rsum) (compose concat (compose (map tails) inits))).

(* form3 = maximum . concat . map (map sum) . map tails . inits *)
Definition form3 : list R -> R := compose maximum (compose concat (compose (map (map Rsum)) (compose (map tails) inits))).

(* form4 = maximum . map maximum . map (map sum) . map tails . inits *)
Definition form4 : list R -> R := compose maximum (compose (map maximum) (compose (map (map Rsum)) (compose (map tails) inits))).

(* form5 = maximum . map (maximum . map sum . tails) . inits *)
Definition form5 : list R -> R := compose maximum (compose (map (compose maximum (compose (map Rsum) tails))) inits).

(* form6 = maximum . map (foldl (<#>) 0) . inits *)
Definition form6 : list R -> R := compose maximum (compose (map (foldl RnonzeroSum 0)) inits).

(* form7 = maximum . scal (<#>) 0 *)
Definition form7 : list R -> R := compose maximum (scanl RnonzeroSum 0).

(* form8 = fst . foldl (<.>) (0,0) *)
Definition form8 : list R -> R := compose fst (foldl RMaxSoFarAndPreviousNonzeroSum (0,0)).

Lemma map_promotion {A : Type} : forall (f : (list A) -> A),
  compose (map f) concat = compose concat (map (map f)).
Proof.
  intros.
  unfold compose.
  f_equal.
  apply functional_extensionality.
  intros.
  induction x0 as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite map_app. (* Apply map_app to rewrite map f (x ++ concat xs) *)
    rewrite IH.    (* Apply the induction hypothesis *)
    reflexivity.
Qed.

Lemma map_distr {A B C : Type} : forall (f : B -> C) (g : A -> B),
  compose (map f) (map g) = map (compose f g).
Proof.
  intros.
  unfold compose.
  f_equal.
  apply functional_extensionality.
  intros.
  induction x0 as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - rewrite IH.    (* Apply the induction hypothesis *)
    reflexivity.
Qed.

Lemma maximum_distr (x : list R) (xs : list (list R)) : maximum (x ++ concat xs) = Rmax (maximum x) (maximum (concat xs)).
Proof.
  unfold fold_right.
Admitted.

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

Lemma fold_promotion : compose maximum concat = compose maximum (map maximum).
Proof.
  unfold compose.
  apply functional_extensionality.
  intros.
  induction x0 as [|x xs IH]; simpl.
  - reflexivity. (* Base case: both sides are empty *)
  - assert (maximum (x ++ (concat xs)) = maximum x \/ maximum (x ++ (concat xs)) <> maximum x).
    + tauto.
    + destruct H.
      * rewrite H.
        unfold maximum.
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
  rewrite <- compose_assoc.
  rewrite map_promotion.
  reflexivity.
Qed.

Theorem form3_eq_form4 : form3 = form4.
Proof.
  unfold form3.
  unfold form4.
  f_equal.
  rewrite <- compose_assoc.
Admitted.

Theorem form4_eq_form5 : form4 = form5.
Proof.
  unfold form4.
  unfold form5.
  f_equal.
  rewrite <- compose_assoc.
  rewrite <- compose_assoc.
  rewrite <- compose_assoc.
  rewrite (map_distr maximum (map Rsum)).
  rewrite (map_distr (compose maximum (map Rsum)) tails).
  reflexivity.
Qed.
