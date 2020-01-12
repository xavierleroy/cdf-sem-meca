From Coq Require Import ZArith Psatz Bool String List FMaps.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import Sequences IMP.
From CDF Require AbstrInterp.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 5.  Analyse statique par interprétation abstraite, version améliorée *)

(** ** 5.5.  Interface des domaines abstraits améliorés *)

(** Nous ajoutons à l'interface des valeurs abstraites des opérations
    abstraites pour l'analyse inverse des conditionnelles et pour
    l'élargissement. *)

Module Type VALUE_ABSTRACTION.

(** On reprend toutes les déclarations de l'interface simplifiée. *)

  Include AbstrInterp.VALUE_ABSTRACTION.

(** [meet] calcule un minorant de ses deux arguments. *)
  Parameter meet: t -> t -> t.
  Axiom meet_1: forall n N1 N2, In n N1 -> In n N2 -> In n (meet N1 N2).

(** [isIn] teste si une valeur concrète appartient à une valeur abstraite. *)
  Parameter isIn: Z -> t -> bool.
  Axiom isIn_1: forall n N, In n N -> isIn n N = true.

(** Opérateurs abstraits pour l'analyse inverse des comparaisons.
  Considérons un test [a1 = a2] qui s'évalue à vrai dans le programme.
  Soit [N1] une abstraction de [a1] et [N2] une abstraction de [a2].
  [eq_inv N1 N2] produit une paire de valeurs abstraites [N1', N2'].
  [N1'] est une abstraction possiblement plus précise pour [a1]
  qui prend en compte le fait que [a1 = a2].
  [N2'] est une abstraction possiblement plus précise pour [a2]
  qui prend en compte le fait que [a1 = a2]. *)

  Parameter eq_inv: t -> t -> t * t.
  Axiom eq_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 = n2 ->
    In n1 (fst (eq_inv N1 N2)) /\ In n2 (snd (eq_inv N1 N2)).

  Parameter ne_inv: t -> t -> t * t.
  Axiom ne_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 <> n2 ->
    In n1 (fst (ne_inv N1 N2)) /\ In n2 (snd (ne_inv N1 N2)).

  Parameter le_inv: t -> t -> t * t.
  Axiom le_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 <= n2 ->
    In n1 (fst (le_inv N1 N2)) /\ In n2 (snd (le_inv N1 N2)).

  Parameter gt_inv: t -> t -> t * t.
  Axiom gt_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 > n2 ->
    In n1 (fst (gt_inv N1 N2)) /\ In n2 (snd (gt_inv N1 N2)).

(** [widen N1 N2] calcule un majorant de son premier arguments, choisi
    de sorte à garantir et accélérer la convergence de l'itération
    de point fixe. *)

  Parameter widen: t -> t -> t.
  Axiom widen_1: forall N1 N2, le N1 (widen N1 N2).

(** Pour garantir la convergence, on fournit une mesure à valeurs 
    entières positives qui décroît strictement le long de l'itération
    de point fixe avec élargissement. *)
  Parameter measure: t -> nat.
  Axiom measure_top:
    measure top = 0%nat.
  Axiom widen_4:
    forall N1 N2, (measure (widen N1 N2) <= measure N1)%nat.
  Axiom widen_5:
    forall N1 N2, ble N2 N1 = false -> (measure (widen N1 N2) < measure N1)%nat.

End VALUE_ABSTRACTION.

(** Nous ajoutons à l'interface des états abstraits 
    une opération d'élargissement. *)

Module Type STORE_ABSTRACTION.

  Declare Module V: VALUE_ABSTRACTION.
  Parameter t: Type.
  Parameter get: ident -> t -> V.t.
  Definition In (s: store) (S: t) : Prop :=
    forall x, V.In (s x) (get x S).
  Parameter set: ident -> V.t -> t -> t.
  Axiom set_1: forall x n N s S,
    V.In n N -> In s S -> In (update x n s) (set x N S).
  Definition le (S1 S2: t) : Prop :=
    forall s, In s S1 -> In s S2.
  Parameter ble: t -> t -> bool.
  Axiom ble_1: forall S1 S2, ble S1 S2 = true -> le S1 S2.
  Parameter bot: t.
  Axiom bot_1: forall s, ~(In s bot).
  Parameter top: t.
  Parameter top_1: forall s, In s top.
  Parameter join: t -> t -> t.
  Axiom join_1: forall s S1 S2, In s S1 -> In s (join S1 S2).
  Axiom join_2: forall s S1 S2, In s S2 -> In s (join S1 S2).

(** Voici le nouvel opérateur d'élargissement. *)

  Parameter widen: t -> t -> t.
  Axiom widen_1: forall S1 S2, le S1 (widen S1 S2).

(** L'ordre ci-dessous correspond aux itérations successives de l'itération
    de point fixe avec élargissement.  Il faut qu'il soit bien fondé
    afin de garantir la terminaison. *)

  Definition widen_order (S S1: t) :=
    exists S2, S = widen S1 S2 /\ ble S2 S1 = false.

  Axiom widen_order_wf: well_founded widen_order.

End STORE_ABSTRACTION.

(** ** 5.6.  L'analyseur générique amélioré. *)

Module Analysis (ST: STORE_ABSTRACTION).

Module V := ST.V.

(** *** Calcul de post-points fixes avec élargissement et rétrécissement *)

Section FIXPOINT.

Variable F: ST.t -> ST.t.

Program Definition is_true (b: bool) : { b = true } + { b = false } :=
  match b with true => left _ | false => right _ end.

Lemma iter_up_acc:
  forall (S: ST.t) (acc: Acc ST.widen_order S) (S': ST.t),
  ST.ble S' S = false ->
  Acc ST.widen_order (ST.widen S S').
Proof.
  intros. eapply Acc_inv; eauto. exists S'. auto. 
Defined.

Fixpoint iter_up (S: ST.t) (acc: Acc ST.widen_order S) : ST.t :=
  let S' := F S in
  match is_true (ST.ble S' S) with
  | left LE => S
  | right NOTLE => iter_up (ST.widen S S') (iter_up_acc S acc S' NOTLE)
  end.

Fixpoint iter_down (n: nat) (S: ST.t) : ST.t :=
  match n with
  | O => S
  | S n => let S' := F S in
           if ST.ble (F S') S' then iter_down n S' else S
  end.

Definition niter_down := 3%nat.

Definition postfixpoint : ST.t :=
  iter_down niter_down (iter_up ST.bot (ST.widen_order_wf ST.bot)).

Lemma iter_up_sound:
  forall S acc, ST.le (F (iter_up S acc)) (iter_up S acc).
Proof.
  induction S using (well_founded_induction ST.widen_order_wf). 
  intros acc. destruct acc. cbn. destruct (is_true (ST.ble (F S) S)).
- apply ST.ble_1; auto.
- apply H. exists (F S); auto. 
Qed.

Lemma iter_down_sound:
  forall n S, ST.le (F S) S -> ST.le (F (iter_down n S)) (iter_down n S).
Proof.
  induction n; intros; cbn.
- auto.
- destruct (ST.ble (F (F S)) (F S)) eqn:BLE.
  + apply IHn. apply ST.ble_1; auto.
  + auto.
Qed.

Lemma postfixpoint_sound: ST.le (F postfixpoint) postfixpoint.
Proof.
  apply iter_down_sound. apply iter_up_sound.
Qed.

End FIXPOINT.

(** *** Interprétation abstraite des expressions arithmétiques *)

(** Même définition que dans la version simplifiée. *)

Fixpoint Aeval (a: aexp) (S: ST.t) : V.t :=
  match a with
  | CONST n => V.const n
  | VAR x => ST.get x S
  | PLUS a1 a2 => V.add (Aeval a1 S) (Aeval a2 S)
  | MINUS a1 a2 => V.sub (Aeval a1 S) (Aeval a2 S)
  end.

Lemma Aeval_sound:
  forall s S a,
  ST.In s S -> V.In (aeval a s) (Aeval a S).
Proof.
  induction a; cbn; intros.
- apply V.const_1.
- apply H.
- apply V.add_1; auto.
- apply V.sub_1; auto.
Qed.

(** *** Analyse inverse des expressions arithmétiques et booléennes *)

(** En supposant que la valeur concrète de [a] appartient à la valeur
    abstraite [Res], qu'apprenons-nous sur les valeurs des variables
    qui apparaissent dans [a]?  Les faits que nous apprenons
    sont utilisés pour affiner les valeurs abstraites de ces variables
    dans l'état abstrait [S]. *)

Fixpoint assume_eval (a: aexp) (Res: V.t) (S: ST.t) : ST.t :=
  match a with
  | CONST n =>
      if V.isIn n Res then S else ST.bot
  | VAR x =>
      ST.set x (V.meet Res (ST.get x S)) S
  | PLUS a1 a2 =>
      let N1 := Aeval a1 S in
      let N2 := Aeval a2 S in
      let Res1 := V.meet N1 (V.sub Res N2) in
      let Res2 := V.meet N2 (V.sub Res N1) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  | MINUS a1 a2 =>
      let N1 := Aeval a1 S in
      let N2 := Aeval a2 S in
      let Res1 := V.meet N1 (V.add Res N2) in
      let Res2 := V.meet N2 (V.sub N1 Res) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  end.

Lemma assume_eval_sound:
  forall a Res S s,
  V.In (aeval a s) Res -> ST.In s S -> ST.In s (assume_eval a Res S).
Proof.
  induction a; cbn; intros.
- (* CONST *)
  rewrite V.isIn_1 by auto. auto.
- (* VAR *)
  replace s with (update x (s x) s).
  apply ST.set_1; auto.
  apply V.meet_1; auto.
  apply functional_extensionality; intros y. 
  unfold update; destruct (string_dec x y); congruence.
- (* PLUS *)
  set (n1 := aeval a1 s) in *. set (n2 := aeval a2 s) in *.
  set (N1 := Aeval a1 S). set (N2 := Aeval a2 S).
  assert (V.In n1 N1) by (apply Aeval_sound; auto).
  assert (V.In n2 N2) by (apply Aeval_sound; auto).
  apply IHa1; fold n1.
  apply V.meet_1. auto. replace n1 with ((n1 + n2) - n2) by lia. apply V.sub_1; auto.
  apply IHa2; fold n2.
  apply V.meet_1. auto. replace n2 with ((n1 + n2) - n1) by lia. apply V.sub_1; auto.
  auto.
- (* MINUS *)
  set (n1 := aeval a1 s) in *. set (n2 := aeval a2 s) in *.
  set (N1 := Aeval a1 S). set (N2 := Aeval a2 S).
  assert (V.In n1 N1) by (apply Aeval_sound; auto).
  assert (V.In n2 N2) by (apply Aeval_sound; auto).
  apply IHa1; fold n1.
  apply V.meet_1. auto. replace n1 with ((n1 - n2) + n2) by lia. apply V.add_1; auto.
  apply IHa2; fold n2.
  apply V.meet_1. auto. replace n2 with (n1 - (n1 - n2)) by lia. apply V.sub_1; auto.
  auto.
Qed.

(** En supposant que l'expression booléenne [b] s'évalue concrètement à [res],
    qu'apprenons-nous sur les valeurs des variables
    qui apparaissent dans [b]?  Les faits que nous apprenons
    sont utilisés pour affiner les valeurs abstraites de ces variables
    dans l'état abstrait [S]. *)

Fixpoint assume_test (b: bexp) (res: bool) (S: ST.t): ST.t :=
  match b with
  | TRUE => if res then S else ST.bot
  | FALSE => if res then ST.bot else S
  | EQUAL a1 a2 =>
      let (Res1, Res2) :=
        if res
        then V.eq_inv (Aeval a1 S) (Aeval a2 S)
        else V.ne_inv (Aeval a1 S) (Aeval a2 S) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  | LESSEQUAL a1 a2 =>
      let (Res1, Res2) :=
        if res
        then V.le_inv (Aeval a1 S) (Aeval a2 S)
        else V.gt_inv (Aeval a1 S) (Aeval a2 S) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  | NOT b1 =>
      assume_test b1 (negb res) S
  | AND b1 b2 =>
      if res
      then assume_test b1 true (assume_test b2 true S)
      else ST.join (assume_test b1 false S) (assume_test b2 false S)
  end.

Lemma assume_test_sound:
  forall b res S s,
  beval b s = res -> ST.In s S -> ST.In s (assume_test b res S).
Proof.
  induction b; cbn; intros.
- (* TRUE *)
  subst res; auto.
- (* FALSE *)
  subst res; auto.
- (* EQUAL *)
  set (Res := if res
              then V.eq_inv (Aeval a1 S) (Aeval a2 S)
              else V.ne_inv (Aeval a1 S) (Aeval a2 S)).
  assert (A: V.In (aeval a1 s) (fst Res) /\ V.In (aeval a2 s) (snd Res)).
  { unfold Res; destruct res;
    [ apply V.eq_inv_1 | apply V.ne_inv_1 ]; auto using Aeval_sound.
  - apply Z.eqb_eq; auto.
  - apply Z.eqb_neq; auto.
  }
  destruct A as [A1 A2]. destruct Res as [Res1 Res2]. auto using assume_eval_sound.
- (* LESSEQUAL *)
  set (Res := if res
              then V.le_inv (Aeval a1 S) (Aeval a2 S)
              else V.gt_inv (Aeval a1 S) (Aeval a2 S)).
  assert (A: V.In (aeval a1 s) (fst Res) /\ V.In (aeval a2 s) (snd Res)).
  { unfold Res; destruct res;
    [ apply V.le_inv_1 | apply V.gt_inv_1 ]; auto using Aeval_sound.
  - apply Z.leb_le; auto.
  - apply Z.leb_nle in H. lia.
  }
  destruct A as [A1 A2]. destruct Res as [Res1 Res2]. auto using assume_eval_sound.
- (* NOT *)
  apply IHb; auto. rewrite <- H. rewrite negb_involutive; auto. 
- (* AND *)
  destruct res.
  + (* AND, true *)
    destruct (andb_prop _ _ H). 
    auto.
  + (* AND, false *)
    destruct (andb_false_elim _ _ H); [apply ST.join_1 | apply ST.join_2]; auto.
Qed.

(** *** Interprétation abstraite améliorée des commandes *)

(** On ajoute des appels à [assume_test] à chaque fois qu'une condition booléenne
    est connue comme vraie ou comme fausse. *)

Fixpoint Cexec (c: com) (S: ST.t) : ST.t :=
  match c with
  | SKIP => S
  | ASSIGN x a => ST.set x (Aeval a S) S
  | SEQ c1 c2 => Cexec c2 (Cexec c1 S)
  | IFTHENELSE b c1 c2 =>
      ST.join (Cexec c1 (assume_test b true S))
              (Cexec c2 (assume_test b false S))
  | WHILE b c =>
      assume_test b false
        (postfixpoint (fun X => ST.join S (Cexec c (assume_test b true X))))
  end.

Theorem Cexec_sound:
  forall c s s' S,
  ST.In s S -> cexec s c s' -> ST.In s' (Cexec c S).
Proof.
Opaque niter_down.
  induction c; intros s s' S PRE EXEC; cbn.
- (* SKIP *)
  inversion EXEC; subst. auto.
- (* ASSIGN *)
  inversion EXEC; subst. apply ST.set_1; auto. apply Aeval_sound; auto.
- (* SEQ *)
  inversion EXEC; subst. eauto.
- (* IFTHENELSE *)
  inversion EXEC; subst. destruct (beval b s) eqn:B.
  apply ST.join_1. eapply IHc1; eauto. apply assume_test_sound; auto.
  apply ST.join_2. eapply IHc2; eauto. apply assume_test_sound; auto.
- (* WHILE *)
  set (F := fun X => ST.join S (Cexec c (assume_test b true X))).
  set (X := postfixpoint F).
  assert (L : ST.le (F X) X) by (apply postfixpoint_sound).
  assert (REC: forall s1 c1 s2,
               cexec s1 c1 s2 ->
               c1 = WHILE b c ->
               ST.In s1 X ->
               ST.In s2 (assume_test b false X)).
  { induction 1; intro EQ; inversion EQ; subst; intros.
  - (* WHILE done *)
    apply assume_test_sound; auto.
  - (* WHILE loop *)
    apply IHcexec2; auto. apply L. unfold F. apply ST.join_2.
    eapply IHc; eauto. apply assume_test_sound; auto.
  }
  eapply REC; eauto. apply L. unfold F. apply ST.join_1. auto.
Qed.



