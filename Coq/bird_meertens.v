Require Import Coq.Program.Basics.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import Coq.Lists.List.
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
Eval compute in (inits example_list).


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

Definition maximum : list R -> option R := fun xs => match xs with
  | [] => None
  | x' :: xs' => Some (fold_right (fun y acc => Rmax y acc) x' xs')
end.

Definition Rsum : list R -> R := fun xs => fold_right (fun x acc => x + acc) 0 xs.

(* Forms of MaxSegSum *)
(* form1, form2, form3, form4, form5, form6, form7, form8 :: (Ord a, Num a) => [a] -> a *)
(* form1 = maximum . map sum . segs *)
Definition form1 : (list R) -> option R := compose maximum (compose (map Rsum) segs).

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
