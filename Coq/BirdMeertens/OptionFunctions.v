Require Import Coq.Init.Datatypes.

Definition liftOption2 {A B C : Type} : (A -> B -> C) -> option A -> option B -> option C := fun op mx my => match mx with
  | None => None
  | Some x => match my with
    | None => None
    | Some y => Some (op x y)
  end
end.

Definition liftOptionOpWithNoneID {A: Type} : (A -> A -> A) -> option A -> option A -> option A := fun op mx my => match mx with
  | None => match my with
    | None => None
    | Some y => Some y
  end
  | Some x => match my with
    | None => Some x
    | Some y => Some (op x y)
  end
end.