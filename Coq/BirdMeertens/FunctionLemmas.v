Theorem functions_not_equal :
  forall (X Y : Type) (f g : X -> Y),
  (exists x : X, f x <> g x) -> f <> g.
Proof.
  intros X Y f g H.
  unfold not; intros Heq.
  destruct H as [x Hx].
  apply Hx.
  rewrite <- Heq.
  reflexivity.
Qed.
