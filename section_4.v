(* Exercise 4.3 *)
Section A_declared.
  Variables (A : Set) (P Q : A -> Prop) (R : A -> A -> Prop).

  Theorem all_perm : (forall (a b : A), R a b) -> forall (a b : A),  R b a.
  Proof.
    exact (fun (abR : forall (a b : A), R a b) (a b : A) => abR b a).
  Qed.

  Theorem all_imp_dist :
    (forall (a : A), P a -> Q a) -> (forall (a : A), P a) -> forall (a : A), Q a.
  Proof.
    exact (fun (aPaQa : forall (a : A), P a -> Q a) (aPa : forall (a : A), P a) (a : A) => aPaQa a (aPa a)).
  Qed.

  Theorem all_delta : (forall (a b : A), R a b) -> forall (a : A), R a a.
  Proof.
    exact (fun (Rab : forall (a b : A), R a b) (a : A) => Rab a a).
  Qed.
End A_declared.

(* Exercise 4.5 *)

Theorem all_perm2 :
  forall (A : Type) (P : A -> A -> Prop),
    (forall (x y : A), P x y) -> forall (x y : A), P y x.
Proof.
  intros A P H x y.
  apply H.
Qed.

Theorem resolution :
  forall (A : Type) (P Q R S : A -> Prop),
    (forall (a : A), Q a -> R a -> S a) ->
      (forall (b : A), P b -> Q b) ->
        forall (c : A), P c -> R c -> S c.
Proof.
  intros A P Q R S Hqrs Hpq c Pc Rc.
  apply Hqrs.
  apply Hpq.
  assumption. 
  assumption.
Qed.

