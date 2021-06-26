
(* exercise 5.1 *)

Lemma id_P : forall (P : Prop), P -> P.
Proof.
  intros P p.
  assumption.
Qed.

Lemma id_PP : forall (P : Prop), (P -> P) -> (P -> P).
Proof.
  intros P pp p.
  assumption.
Qed.

Lemma imp_trans : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R pq qr p.
  apply qr.
  apply pq.
  assumption.
Qed.

Lemma imp_perm : forall (P Q R : Prop), (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros P Q R pqr q r.
  apply pqr.
  assumption.
  assumption.
Qed.

Lemma ignore_Q : forall (P Q R : Prop), (P -> R) -> P -> Q -> R.
Proof.
  intros P Q R pr p q.
  apply pr.
  assumption.
Qed.

Lemma delta_imp : forall (P Q : Prop), (P -> P -> Q) -> P -> Q.
Proof.
  intros P Q ppq p.
  apply ppq.
  assumption.
  assumption.
Qed.

Lemma delta_impR : forall (P Q : Prop), (P -> Q) -> (P -> P -> Q).
Proof.
  intros P Q pq p p2.
  apply pq.
  assumption.
Qed.

Lemma diamond : forall (P Q R T : Prop), (P -> Q) -> (Q -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros P Q R T pq qr qrt p.
  apply qrt.
  apply pq.
  assumption.
  apply qr.
  apply pq.
  assumption.
Qed.

Lemma weak_pierce : forall (P Q : Prop), ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros P Q pqppq.
  apply pqppq.
  intro pqp.
  apply pqp.
  intro p.
  apply pqppq.
  intro pqp2.
  assumption.
Qed.

(* Exercise 5.3 *)

Goal (~False).
  intro.
  assumption.
Qed.

Goal (forall (P : Prop), ~~~P -> ~P).
  intros P nnnp p.
  apply nnnp.
  intros np.
  apply np.
  assumption.
Qed.

Goal (forall (P Q : Prop), ~~~P -> P -> Q).
  intros P Q nnnp p.
  apply False_ind.
  apply nnnp.
  intro np.
  apply np.
  assumption.
Qed.

Goal forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
  intros P Q pq nq p.
  apply nq.
  apply pq.
  assumption.
Qed.

Goal forall (P Q R : Prop), (P -> Q) -> (P -> ~Q) -> P -> R.
  intros P Q R pq pnq p.
  apply False_ind.
  apply pnq.
  assumption.
  apply pq.
  assumption.
Qed.


(* Exercise 5.4 *)

Definition dyslexic_imp := forall (P Q : Prop), (P -> Q) -> Q -> P.
Definition dyslexic_contrap := forall (P Q : Prop), (P -> Q) -> (~P -> ~Q).

(*

P->QからQ->Pという誤謬が成り立つとすれば矛盾する

恒真命題Tがあれば P -> T は任意のPに対し成り立つ。
dyslexicの命題からPを導ける

*)
Check False_ind.

Goal dyslexic_imp -> False.
  intro d.
  apply (d False True).
  exact (fun _ => I).
  exact I.
Qed.

Goal dyslexic_contrap -> False.
  intro d.
  apply (d False True).
  exact (fun _ => I).
  exact (fun x => x).
  exact I.
Qed.

