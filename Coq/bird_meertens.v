Require Import Coq.Program.Basics.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.

(* segs :: [a] -> [[a]] *)
(* segs = concat . map tails . inits *)
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

(* form1, form2, form3, form4, form5, form6, form7, form8 :: (Ord a, Num a) => [a] -> a *)
(* form1 = maximum . map sum . segs *)
(* form2 = maximum . map sum . concat . map tails . inits *)
(* form3 = maximum . concat . map (map sum) . map tails . inits *)
(* form4 = maximum . map maximum . map (map sum) . map tails . inits *)
(* form5 = maximum . map (maximum . map sum . tails) . inits *)
(* form6 = maximum . map (foldl (<#>) 0) . inits *)
(* form7 = maximum . scanl (<#>) 0 *)
(* form8 = fst . foldl (<.>) (0,0) *)

(* x <#> y = (x + y) <|> 0 *)
(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
(* x <|> y = max x y *)

(* -- QuickCheck property to compare all forms *)
(* prop_sameResults :: [Integer] -> Bool *)
(* prop_sameResults xs = all (== head results) results *)
  (* where results = [form1 xs, form2 xs, form3 xs, form4 xs, form5 xs, form6 xs, form7 xs, form8 xs] *)

(* -- Run QuickCheck *)
(* main :: IO () *)
(* main = quickCheck prop_sameResults *)
