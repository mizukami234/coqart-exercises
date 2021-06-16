
(* exercise 3.2 *)

Section exercise_3_2.
  Variable (P Q R : Prop).

  Lemma id_P : P -> P.
  Proof.
    intro p.
    assumption.
  Qed.

  Lemma id_PP : (P -> P) -> (P -> P).
  Proof.
    intros pp p.
    assumption.
  Qed.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> (P -> R).
  Proof.
    intros pq qr p.
    apply qr.
    apply pq.
    assumption.
  Qed.

  Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
  Proof.
    intros pqr q r.
    apply pqr.
    assumption.
    assumption.
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
    intros pr p q.
    apply pr.
    assumption.
  Qed.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros ppq p.
    apply ppq.
    assumption.
    assumption.
  Qed.

  Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
  Proof.
    intros pq p p2.
    apply pq.
    assumption.
  Qed.

  Variable T : Prop.

  Lemma diamond : (P -> Q) -> (Q -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros pq qr qrt p.
    apply qrt.
    apply pq.
    assumption.
    apply qr.
    apply pq.
    assumption.
  Qed.

  Lemma weak_pierce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intro pqppq.
    apply pqppq.
    intro pqp.
    apply pqp.
    intro p.
    apply pqppq.
    intro pqp2.
    assumption.
  Qed.
End exercise_3_2.

