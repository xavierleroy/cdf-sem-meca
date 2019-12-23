From Coq Require Import ZArith Psatz Bool String List Wellfounded Program.Equality.
From CDF Require Import IMP.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 4.  Logiques de programmes *)

(** Assertions sur l'état mémoire *)

Definition assertion : Type := store -> Prop.

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

Definition aeqv (P Q: assertion) : Prop :=
  forall s, P s <-> Q s.

(** Triplets de Hoare faibles *)

Inductive triple: assertion -> com -> assertion -> Prop :=
  | triple_skip: forall P,
      triple P SKIP P
  | triple_assign: forall P x a,
      triple (aupdate x a P) (ASSIGN x a) P
  | triple_seq: forall P Q R c1 c2,
      triple P c1 Q -> triple Q c2 R ->
      triple P (c1;;c2) R
  | triple_ifthenelse: forall P Q b c1 c2,
      triple (aand (atrue b) P) c1 Q ->
      triple (aand (afalse b) P) c2 Q ->
      triple P (IFTHENELSE b c1 c2) Q
  | triple_while: forall P b c,
      triple (aand (atrue b) P) c P ->
      triple P (WHILE b c) (aand (afalse b) P)
  | triple_consequence: forall P Q P' Q' c,
      triple P c Q -> aimp P' P -> aimp Q Q' ->
      triple P' c Q'.

(** Interprétation sémantique *)

Definition sem_triple (P: assertion) (c: com) (Q: assertion) :=
  forall s s', cexec s c s' -> P s -> Q s'.

Lemma sem_triple_skip: forall P, sem_triple P SKIP P.
Proof.
  unfold sem_triple; intros. inversion H; subst. auto.
Qed.

Lemma sem_triple_assign: forall P x a,
      sem_triple (aupdate x a P) (ASSIGN x a) P.
Proof.
  unfold sem_triple, aupdate; intros. inversion H; subst. auto.
Qed.

Lemma sem_triple_seq: forall P Q R c1 c2,
      sem_triple P c1 Q -> sem_triple Q c2 R ->
      sem_triple P (c1;;c2) R.
Proof.
  unfold sem_triple; intros. inversion H1; subst. eauto.
Qed.

Lemma sem_triple_ifthenelse: forall P Q b c1 c2,
      sem_triple (aand (atrue b) P) c1 Q ->
      sem_triple (aand (afalse b) P) c2 Q ->
      sem_triple P (IFTHENELSE b c1 c2) Q.
Proof.
  unfold sem_triple, aand, atrue, afalse; intros. inversion H1; subst.
  destruct (beval b s) eqn:B; eauto.
Qed.

Lemma sem_triple_while: forall P b c,
      sem_triple (aand (atrue b) P) c P ->
      sem_triple P (WHILE b c) (aand (afalse b) P).
Proof.
  unfold sem_triple; intros P b c T s s' E. dependent induction E; intros.
- split; auto.
- eapply IHE2; eauto. apply T with s; auto. split; auto.
Qed.

Lemma sem_triple_consequence: forall P Q P' Q' c,
      sem_triple P c Q -> aimp P' P -> aimp Q Q' ->
      sem_triple P' c Q'.
Proof.
  unfold sem_triple, aimp; intros. eauto.
Qed.

Theorem triple_sound:
  forall P c Q, triple P c Q -> sem_triple P c Q.
Proof.
  induction 1; eauto using sem_triple_skip, sem_triple_assign, sem_triple_seq,
  sem_triple_ifthenelse, sem_triple_while, sem_triple_consequence.
Qed.

(** Complétude *)

Definition sem_wp (c: com) (Q: assertion) : assertion :=
  fun s => forall s', cexec s c s' -> Q s'.

Lemma sem_wp_skip: forall Q, aimp (sem_wp SKIP Q) Q.
Proof.
  unfold aimp, sem_wp; intros. apply H. constructor.
Qed.

Lemma sem_wp_assign: forall x a Q, aimp (sem_wp (ASSIGN x a) Q) (aupdate x a Q).
Proof.
  unfold aimp, sem_wp, aupdate; intros. apply H. constructor.
Qed.

Lemma sem_wp_seq: forall c1 c2 Q,
  aimp (sem_wp (c1;;c2) Q) (sem_wp c1 (sem_wp c2 Q)).
Proof.
  unfold aimp, sem_wp; intros. apply H. apply cexec_seq with s'; auto.
Qed.

(*
Lemma sem_wp_ifthenelse: forall b c1 c2 Q,
  aimp (sem_wp (IFTHENELSE b c1 c2) Q)
       (aor (aand (sem_wp c1 Q) (atrue b))
            (aand (sem_wp c2 Q) (afalse b))).
Proof.
  unfold aimp, aor, aand, sem_wp; intros. destruct (beval b s) eqn:B.
- left; split; auto. intros; apply H. apply cexec_ifthenelse. rewrite B; auto.
- right; split; auto. intros; apply H. apply cexec_ifthenelse. rewrite B; auto.
Qed.
*)

Lemma sem_wp_ifthenelse_1: forall b c1 c2 Q,
  aimp (aand (atrue b) (sem_wp (IFTHENELSE b c1 c2) Q)) (sem_wp c1 Q).
Proof.
  unfold aimp, aand, sem_wp; intros. destruct H as [B W].
  apply W. apply cexec_ifthenelse. rewrite B; auto.
Qed.

Lemma sem_wp_ifthenelse_2: forall b c1 c2 Q,
  aimp (aand (afalse b) (sem_wp (IFTHENELSE b c1 c2) Q)) (sem_wp c2 Q).
Proof.
  unfold aimp, aand, sem_wp; intros. destruct H as [B W].
  apply W. apply cexec_ifthenelse. rewrite B; auto.
Qed.

Lemma sem_wp_while_1: forall b c Q,
  aimp (aand (atrue b) (sem_wp (WHILE b c) Q)) (sem_wp c (sem_wp (WHILE b c) Q)).
Proof.
  unfold aimp, aand, sem_wp; intros. destruct H as [B W].
  apply W. apply cexec_while_loop with s'; auto.
Qed.
 

Lemma sem_wp_while_2: forall b c Q,
  aimp (aand (afalse b) (sem_wp (WHILE b c) Q)) Q.
Proof.
  unfold aimp, aand, sem_wp; intros. destruct H as [B W].
  apply W. apply cexec_while_done; auto.
Qed.

Lemma triple_cons_left: forall P' P c Q, triple P c Q -> aimp P' P -> triple P' c Q.
Proof.
  intros. apply triple_consequence with P Q; auto. red; auto.
Qed.

Lemma triple_sem_wp: forall c Q, triple (sem_wp c Q) c Q.
Proof.
  induction c; intros.
- eapply triple_cons_left. apply triple_skip. apply sem_wp_skip.
- eapply triple_cons_left. apply triple_assign. apply sem_wp_assign.
- apply triple_seq with (sem_wp c2 Q).
  + eapply triple_cons_left. apply IHc1. apply sem_wp_seq.
  + apply IHc2.
- apply triple_ifthenelse.
  + eapply triple_cons_left. apply IHc1. apply sem_wp_ifthenelse_1.
  + eapply triple_cons_left. apply IHc2. apply sem_wp_ifthenelse_2.
- eapply triple_consequence.
  + apply triple_while. eapply triple_cons_left. apply IHc. apply sem_wp_while_1.
  + instantiate (1 := Q); red; auto.
  + apply sem_wp_while_2.
Qed.  

Theorem triple_sem_complete:
  forall P c Q, sem_triple P c Q -> triple P c Q.
Proof.
  intros. apply triple_cons_left with (sem_wp c Q). apply triple_sem_wp. 
  unfold aimp, sem_wp; intros. apply H with s; auto.
Qed.

(** Triplets de Hoare forts *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun (s: store) => aeval a s = v.
Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun (s: store) => 0 <= aeval a s < v.

Inductive Triple: assertion -> com -> assertion -> Prop :=
  | Triple_skip: forall P,
      Triple P SKIP P
  | Triple_assign: forall P x a,
      Triple (aupdate x a P) (ASSIGN x a) P
  | Triple_seq: forall P Q R c1 c2,
      Triple P c1 Q -> triple Q c2 R ->
      Triple P (c1;;c2) R
  | Triple_ifthenelse: forall P Q b c1 c2,
      Triple (aand (atrue b) P) c1 Q ->
      Triple (aand (afalse b) P) c2 Q ->
      Triple P (IFTHENELSE b c1 c2) Q
  | Triple_while: forall P variant b c,
      (forall v,
        Triple (aand P (aand (atrue b) (aequal variant v)))
               c
               (aand P (alessthan variant v)))->
      Triple P (WHILE b c) (aand P (afalse b))
  | Triple_consequence: forall P Q P' Q' c,
      Triple P c Q -> aimp P' P -> aimp Q Q' ->
      Triple P' c Q'.

(** Interprétation sémantique *)

Definition sem_Triple (P: assertion) (c: com) (Q: assertion) :=
  forall s , P s -> exists s', cexec s c s' /\ Q s'.

Lemma sem_Triple_while: forall P variant b c,
      (forall v,
        sem_Triple (aand P (aand (atrue b) (aequal variant v)))
               c
               (aand P (alessthan variant v)))->
      sem_Triple P (WHILE b c) (aand P (afalse b)).
Proof.
  intros P variant b c T.
  assert (REC: forall v s, P s -> aeval variant s = v ->
               exists s', cexec s (WHILE b c) s' /\ (P s' /\ beval b s' = false)).
  { induction v using (well_founded_induction (Z.lt_wf 0)).
    intros. destruct (beval b s) eqn:B.
  - destruct (T v s) as (s1 & EXEC1 & (PS1 & LT1)). unfold aand, aequal, atrue; auto.
    destruct (H _ LT1 s1 PS1) as (s2 & EXEC2 & PS2). auto.
    exists s2; split; auto. apply cexec_while_loop with s1; auto.
  - exists s; split; auto. apply cexec_while_done; auto.
  }
  unfold sem_Triple; intros. apply REC with (v := aeval variant s); auto.
Qed.

(** VCG *)

Inductive com: Type :=
  | SKIP
  | ASSIGN (x: ident) (a: aexp)
  | SEQ (c1: com) (c2: com)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com)
  | WHILE (Inv: assertion) (b: bexp) (c1: com).

Inductive cexec: store -> com -> store -> Prop :=
  | cexec_skip: forall s,
      cexec s SKIP s
  | cexec_assign: forall s x a,
      cexec s (ASSIGN x a) (update x (aeval a s) s)
  | cexec_seq: forall c1 c2 s s' s'',
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (SEQ c1 c2) s''
  | cexec_ifthenelse: forall b c1 c2 s s',
      cexec s (if beval b s then c1 else c2) s' ->
      cexec s (IFTHENELSE b c1 c2) s'
  | cexec_while_done: forall Inv b c s,
      beval b s = false ->
      cexec s (WHILE Inv b c) s
  | cexec_while_loop: forall Inv b c s s' s'',
      beval b s = true -> cexec s c s' -> cexec s' (WHILE Inv b c) s'' ->
      cexec s (WHILE Inv b c) s''.

Fixpoint pre (c: com) (Q: assertion) : assertion :=
  match c with
  | SKIP => Q
  | ASSIGN x a => aupdate x a Q
  | SEQ c1 c2 => pre c1 (pre c2 Q)
  | IFTHENELSE b c1 c2 => aor (aand (atrue b) (pre c1 Q)) (aand (afalse b) (pre c2 Q))
  | WHILE Inv b c => Inv
  end.

Fixpoint vcg (c: com) (Q: assertion) : Prop :=
  match c with
  | SKIP => True
  | ASSIGN x a => True
  | SEQ c1 c2 => vcg c1 (pre c2 Q) /\ vcg c2 Q
  | IFTHENELSE b c1 c2 => vcg c1 Q /\ vcg c2 Q
  | WHILE Inv b c =>
       vcg c Inv
    /\ aimp (aand (afalse b) Inv) Q
    /\ aimp (aand (atrue b) Inv) (pre c Inv)
  end.

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  aimp P (pre c Q) /\ vcg c Q.

Fixpoint erase (c: com) : IMP.com :=
  match c with
  | SKIP => IMP.SKIP
  | ASSIGN x a => IMP.ASSIGN x a
  | SEQ c1 c2 => IMP.SEQ (erase c1) (erase c2)
  | IFTHENELSE b c1 c2 => IMP.IFTHENELSE b (erase c1) (erase c2)
  | WHILE Inv b c => IMP.WHILE b (erase c)
  end.

Lemma vcg_sound:
  forall c Q, vcg c Q -> triple (pre c Q) (erase c) Q.
Proof.
  induction c; cbn; intros.
- apply triple_skip.
- apply triple_assign.
- destruct H as (V1 & V2).
  apply triple_seq with (pre c2 Q); auto.
- destruct H as (V1 & V2). 
  apply triple_ifthenelse.
  + eapply triple_cons_left. apply IHc1; auto.
    unfold aimp, aand, aor, atrue, afalse. intuition congruence.
  + eapply triple_cons_left. apply IHc2; auto.
    unfold aimp, aand, aor, atrue, afalse. intuition congruence.
- destruct H as (V1 & V2 & V3).
  eapply triple_consequence.
  + apply triple_while. eapply triple_cons_left. apply IHc. eauto. auto.
  + red; auto.
  + auto.
Qed.

Theorem vcgen_correct:
  forall P c Q, vcgen P c Q -> triple P (erase c) Q.
Proof.
  unfold vcgen; intros. destruct H as (V1 & V2).
  eapply triple_cons_left. apply vcg_sound; auto. auto.
Qed.

Infix ";;" := SEQ (at level 80, right associativity).

(*
Definition Pre (s: store) :=
  s "a" >= 0 /\ s "b" > 0 .

Definition Inv (s: store) :=
  s "b" > 0 /\  s "r" >= 0 /\ s "a" = s "b" * s "q" + s "r".

Definition Post (s: store) :=
  s "q" = s "a" / s "b" /\ s "r" = s "a" mod s "b".

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE Inv (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

Theorem Euclidean_division_correct:
  triple Pre (erase Euclidean_division) Post.
Proof.
  apply vcgen_correct. red; cbn.
  unfold aimp, aupdate, aand, afalse, atrue, Pre, Post, Inv; cbn.
  intuition auto.
- ring.
- apply Z.leb_gt in H0. apply Zdiv_unique with (s "r"). lia. auto.
- apply Z.leb_gt in H0. apply Zmod_unique with (s "q"). lia. auto.
- apply Z.leb_le in H0. lia.
- rewrite H3. ring. 
Qed.
*)

Definition Pre (s: store) :=
  s "a" >= 0 /\ s "b" >= 0 .

Definition Inv (s: store) :=
  s "b" >= 0 /\  s "r" >= 0 /\ s "a" = s "b" * s "q" + s "r".

Definition Post (s: store) :=
  s "q" = s "a" / s "b" /\ s "r" = s "a" mod s "b".

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE Inv (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

Theorem Euclidean_division_correct:
  triple Pre (erase Euclidean_division) Post.
Proof.
  apply vcgen_correct. red; cbn.
  unfold aimp, aupdate, aand, afalse, atrue, Pre, Post, Inv; cbn.
  intuition auto.
- ring.
- apply Z.leb_gt in H0. apply Zdiv_unique with (s "r"). lia. auto.
- apply Z.leb_gt in H0. apply Zmod_unique with (s "q"). lia. auto.
- apply Z.leb_le in H0. lia.
- rewrite H3. ring. 
Qed.

