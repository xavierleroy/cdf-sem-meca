From Coq Require Import ZArith Psatz Bool String List FMaps.
From CDF Require Import Sequences IMP.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 5.  Analyse statique par interprétation abstraite, version simplifiée *)

(** ** 5.1.  Interface des domaines abstraits *)

(** L'analyseur calcule sur des valeurs abstraites: des approximations
    d'ensembles de valeurs entières.  Le type des valeurs abstraites
    et les opérations associées sont regroupés dans un module Coq,
    dont nous spécifions l'interface ci-dessous. *)

Module Type VALUE_ABSTRACTION.

(** Le type des valeurs abstraites. *)
  Parameter t: Type.

(** [In n N] est vrai si l'entier [n] appartient à l'ensemble représenté
    par la valeur abstraite [N].  C'est l'équivalent de la fonction
    de concrétisation [γ] : [In n N] signifie [n ∈ γ(N)]. *)
  Parameter In: Z -> t -> Prop.

(** Les valeurs abstraites sont ordonnées par inclusion des ensembles
    qu'elles représentent. *)
  Definition le (N1 N2: t) : Prop :=
    forall n, In n N1 -> In n N2.

(** [ble] est une fonction à valeurs booléennes qui décide la relation [le]. *)
  Parameter ble: t -> t -> bool.
  Axiom ble_1: forall N1 N2, ble N1 N2 = true -> le N1 N2.
  Axiom ble_2: forall N1 N2, le N1 N2 -> ble N1 N2 = true.

(** [const n] est la valeur abstraite pour l'ensemble singleton [{n}]. *)
  Parameter const: Z -> t.
  Axiom const_1: forall n, In n (const n).

(** [bot] représente l'ensemble vide. *)
  Parameter bot: t.
  Axiom bot_1: forall n, ~(In n bot).

(** [top] représente l'ensemble de tous les entiers. *)
  Parameter top: t.
  Parameter top_1: forall n, In n top.

(** [join] calcule un majorant de ses deux arguments. *)
  Parameter join: t -> t -> t.
  Axiom join_1: forall n N1 N2, In n N1 -> In n (join N1 N2).
  Axiom join_2: forall n N1 N2, In n N2 -> In n (join N1 N2).

(** Les opérateurs abstraits correspondant à l'addition et à la soustraction. *)
  Parameter add: t -> t -> t.
  Axiom add_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1+n2) (add N1 N2).

  Parameter sub: t -> t -> t.
  Axiom sub_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1-n2) (sub N1 N2).

End VALUE_ABSTRACTION.

(** Les abstractions des états mémoire sont définies dans le même style:
    un module définissant un type [t] des abstractions et les opérations
    abstraites associées.  Voici l'interface de ce module. *)

Module Type STORE_ABSTRACTION.

(** Une abstraction pour les valeurs entières. *)
  Declare Module V: VALUE_ABSTRACTION.

(** Le type des états abstraits. *)
  Parameter t: Type.

(** [get x S] est la valeur abstraite associée à [x] dans [S]. *)
  Parameter get: ident -> t -> V.t.

(** L'appartenance d'un état concret à un état abstrait. *)
  Definition In (s: store) (S: t) : Prop :=
    forall x, V.In (s x) (get x S).

(** Affectation abstraite à une variable. *)
  Parameter set: ident -> V.t -> t -> t.
  Axiom set_1: forall x n N s S,
    V.In n N -> In s S -> In (update x n s) (set x N S).

(** L'ordre entre états abstraits. *)
  Definition le (S1 S2: t) : Prop :=
    forall s, In s S1 -> In s S2.

  Parameter ble: t -> t -> bool.
  Axiom ble_1: forall S1 S2, ble S1 S2 = true -> le S1 S2.

(** Plus petit, plus grand état abstrait. *)
  Parameter bot: t.
  Axiom bot_1: forall s, ~(In s bot).

  Parameter top: t.
  Parameter top_1: forall s, In s top.

(** [join] calcule un majorant de ses deux arguments. *)
  Parameter join: t -> t -> t.
  Axiom join_1: forall s S1 S2, In s S1 -> In s (join S1 S2).
  Axiom join_2: forall s S1 S2, In s S2 -> In s (join S1 S2).

End STORE_ABSTRACTION.

(** ** 5.2.  L'analyseur générique *)

(** L'analyseur se présente comme un module paramétrisé par une abstraction
    des états, celle-ci contenant aussi une abstraction des valeurs. *)

Module Analysis (ST: STORE_ABSTRACTION).

Module V := ST.V.

(** *** Calcul de post-points fixes *)

(** Nous suivons la même approche qu'au 3ième cours, fichier [Optim]:
    une itération de point fixe qui part de [bot] et s'arrête au bout
    d'un nombre fixé de tours, renvoyant [top] si un post-point fixe
    n'a pas été atteint. *)

Section FIXPOINT.

Variable F: ST.t -> ST.t.

Fixpoint iter (n: nat) (S: ST.t) : ST.t :=
  match n with
  | O => ST.top
  | S n' => let S' := F S in 
            if ST.ble S' S then S else iter n' S'
  end.

Definition niter := 10%nat.

Definition postfixpoint : ST.t := iter niter ST.bot.

Lemma postfixpoint_sound:
  ST.le (F postfixpoint) postfixpoint.
Proof.
  unfold postfixpoint. generalize niter ST.bot. 
  induction n; intros S; cbn.
- red; intros; apply ST.top_1.
- destruct (ST.ble (F S) S) eqn:B.
  + apply ST.ble_1; auto.
  + apply IHn.
Qed.

End FIXPOINT.

(** *** Interprétation abstraite des expressions arithmétiques. *)

Fixpoint Aeval (a: aexp) (S: ST.t) : V.t :=
  match a with
  | CONST n => V.const n
  | VAR x => ST.get x S
  | PLUS a1 a2 => V.add (Aeval a1 S) (Aeval a2 S)
  | MINUS a1 a2 => V.sub (Aeval a1 S) (Aeval a2 S)
  end.

(** Cette interprétation abstraite est correcte par rapport à la sémantique
    concrète des expressions. *)

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

(** *** Interprétation abstraite des commandes. *)

(** L'interprétation abstraite d'une commande [c] est une fonction
    [ST.t -> ST.t] qui calcule l'état abstrait «après» exécution de [c]
    en fonction de l'état abstrait «avant».  
    Grâce à l'abstraction, ce calcul termine toujours et peut bien être
    défini comme une fonction. *)

Fixpoint Cexec (c: com) (S: ST.t) : ST.t :=
  match c with
  | SKIP => S
  | ASSIGN x a => ST.set x (Aeval a S) S
  | SEQ c1 c2 => Cexec c2 (Cexec c1 S)
  | IFTHENELSE b c1 c2 => ST.join (Cexec c1 S) (Cexec c2 S)
  | WHILE b c => postfixpoint (fun X => ST.join S (Cexec c X))
  end.

(** Cette interprétation abstraite est correcte par rapport à la sémantique
    opérationnelle d'IMP. *)

Theorem Cexec_sound:
  forall c s s' S,
  ST.In s S -> cexec s c s' -> ST.In s' (Cexec c S).
Proof.
Opaque niter.
  induction c; intros s s' S PRE EXEC; cbn.
- (* SKIP *)
  inversion EXEC; subst. auto.
- (* ASSIGN *)
  inversion EXEC; subst. apply ST.set_1; auto. apply Aeval_sound; auto.
- (* SEQ *)
  inversion EXEC; subst. eauto.
- (* IFTHENELSE *)
  inversion EXEC; subst. destruct (beval b s).
  apply ST.join_1; eauto.
  apply ST.join_2; eauto.
- (* WHILE *)
  set (F := fun X => ST.join S (Cexec c X)).
  set (X := postfixpoint F).
  assert (L : ST.le (F X) X) by (apply postfixpoint_sound).
  assert (REC: forall s1 c1 s2,
               cexec s1 c1 s2 ->
               c1 = WHILE b c ->
               ST.In s1 X ->
               ST.In s2 X).
  { induction 1; intro EQ; inversion EQ; subst; intros.
  - (* WHILE done *)
    auto.
  - (* WHILE loop *)
    apply IHcexec2; auto. apply L. unfold F. apply ST.join_2. eapply IHc; eauto.
  }
  eapply REC; eauto. apply L. unfold F. apply ST.join_1. auto.
Qed.

End Analysis.

(** 5.3.  Un domaine abstrait des états mémoire *)

(** On construit ici un domaine abstrait des états mémoire qui est
    utilisable pour toutes les analyses non relationnelles,
    en particulier les analyses de valeurs. *)

(** Moralement, les états mémoires abstraits sont des fonctions [ident -> V.t]
    des identificateurs vers des valeurs abstraites.  Cependant, il faut
    que la relation d'ordre entre états abstraits soit décidable.
    Pour ce faire, il faut utiliser des fonctions à support fini
    (les "maps" de la bibliothèque standard de Coq) et les compléter
    par [V.top] pour tous les points en dehors du domaine de la fonction. *)

(** Comme dans le fichier [Optim], nous équipons le type des identificateurs
    avec une égalité décidable, puis instancions les modules de fonctions
    finies de la bibliothèque standard sur ce domaine. *)

Module Ident_Decidable <: DecidableType with Definition t := ident.
  Definition t := ident.
  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End Ident_Decidable.

Module IdentMap := FMapWeakList.Make(Ident_Decidable).
Module IMFact := FMapFacts.WFacts(IdentMap).
Module IMProp := FMapFacts.WProperties(IdentMap).

(** Le domaine des états abstraits est paramétrisé par un module [VA]
    des valeurs abstraites. *)

Module StoreAbstr (VA: VALUE_ABSTRACTION) <: STORE_ABSTRACTION.

Module V := VA.

(** Un état abstrait est soit [Bot], associant [V.bot] à toutes les
    variables, soit [Top_except m], associant [V.top] aux variables
    qui ne sont pas décrites dans la fonction finie [m]. *)

Inductive abstr_state : Type :=
  | Bot
  | Top_except (m: IdentMap.t V.t).

Definition t := abstr_state.

Definition get (x: ident) (S: t) : V.t :=
  match S with
  | Bot => V.bot
  | Top_except m =>
      match IdentMap.find x m with
      | None => V.top
      | Some v => v
      end
  end.

Definition In (s: store) (S: t) : Prop :=
  forall x, V.In (s x) (get x S).

Definition set (x: ident) (v: V.t) (S: t): t :=
  match S with
  | Bot => Bot
  | Top_except m => Top_except (IdentMap.add x v m)
  end.

Lemma set_1:
  forall x n N s S,
  V.In n N -> In s S -> In (update x n s) (set x N S).
Proof.
  unfold In, get, set; intros. destruct S.
- elim (V.bot_1 (s "")). auto. 
- rewrite IMFact.add_o. change IdentMap.E.eq_dec with string_dec. unfold update.
  destruct (string_dec x x0); auto.
Qed. 

(** L'ordre entre les états abstraits. *)

Definition le (S1 S2: t) : Prop :=
  forall s, In s S1 -> In s S2.

Definition ble (S1 S2: t) : bool :=
  match S1, S2 with
  | Bot, _ => true
  | _, Bot => false
  | Top_except m1, Top_except m2 =>
      IMProp.for_all (fun x v => V.ble (get x S1) v) m2
  end.

Lemma ble_1: forall S1 S2, ble S1 S2 = true -> le S1 S2.
Proof.
  unfold ble, le; intros.
  destruct S1 as [ | m1].
- elim (V.bot_1 (s "")). apply H0. 
- destruct S2 as [ | m2]. discriminate.
  red; cbn; intros. destruct (IdentMap.find x m2) as [N2|] eqn:F2.
  + apply IdentMap.find_2 in F2. eapply IMProp.for_all_iff in H; eauto.
    apply V.ble_1 in H. apply H. apply H0.
    hnf. intros; subst x0. hnf; intros. subst x0. auto.
  + apply V.top_1.
Qed.

(** Les opérations de treillis. *)

Definition bot: t := Bot.

Lemma bot_1: forall s, ~(In s bot).
Proof.
  unfold In; cbn. intros s IN. apply (V.bot_1 (s "")). apply IN.
Qed.

Definition top: t := Top_except (IdentMap.empty V.t).

Lemma top_1: forall s, In s top.
Proof.
  unfold In, top, get; cbn. intros. apply V.top_1.
Qed. 

Definition join_aux (ov1 ov2: option V.t) : option V.t :=
  match ov1, ov2 with
  | Some v1, Some v2 => Some (V.join v1 v2)
  | _, _ => None
  end.

Definition join (S1 S2: t) : t :=
  match S1, S2 with
  | Bot, _ => S2
  | _, Bot => S1
  | Top_except m1, Top_except m2 =>
      Top_except (IdentMap.map2 join_aux m1 m2)
  end.

Lemma join_1:
  forall s S1 S2, In s S1 -> In s (join S1 S2).
Proof.
  unfold join; intros.
  destruct S1 as [ | m1]. elim (bot_1 s); auto.
  destruct S2 as [ | m2]. auto.
- red; unfold get; intros. rewrite IMFact.map2_1bis; auto.
  unfold join_aux. specialize (H x). unfold get in H.
  destruct (IdentMap.find x m1). 
  + destruct (IdentMap.find x m2).
    * apply V.join_1; auto.
    * apply V.top_1.
  + apply V.top_1.
Qed.

Lemma join_2:
  forall s S1 S2, In s S2 -> In s (join S1 S2).
Proof.
  unfold join; intros.
  destruct S1 as [ | m1]. auto.
  destruct S2 as [ | m2]. elim (bot_1 s); auto.
- red; unfold get; intros. rewrite IMFact.map2_1bis; auto.
  unfold join_aux. specialize (H x). unfold get in H.
  destruct (IdentMap.find x m1). 
  + destruct (IdentMap.find x m2).
    * apply V.join_2; auto.
    * apply V.top_1.
  + apply V.top_1.
Qed.

End StoreAbstr.

(** 5.4.  Une application: l'analyse de propagation des constantes *)

(** *** Le domaine abstrait «plat» des entiers *)

Module FlatInt <: VALUE_ABSTRACTION.

(** Les valeurs abstraites: vide, plein, ou ensemble singleton. *)

  Inductive abstr_value : Type := Bot | Just (n: Z) | Top.
  Definition t := abstr_value.

(** L'appartenance et l'inclusion *)

  Definition In (n: Z) (N: t) : Prop :=
    match N with
    | Bot => False
    | Just m => n = m
    | Top => True
    end.

  Definition le (N1 N2: t) : Prop :=
    forall n, In n N1 -> In n N2.

  Definition ble (N1 N2: t) : bool :=
    match N1, N2 with
    | Bot, _ => true
    | _, Top => true
    | Just n1, Just n2 => n1 =? n2
    | _, _ => false
    end.

  Lemma ble_1: forall N1 N2, ble N1 N2 = true -> le N1 N2.
  Proof.
    unfold ble, le, In; intros.
    destruct N1; try contradiction; destruct N2; try discriminate; auto.
    apply Z.eqb_eq in H. lia.
  Qed.

  Lemma ble_2: forall N1 N2, le N1 N2 -> ble N1 N2 = true.
  Proof.
    unfold ble, le, In; intros.
    destruct N1; auto.
  - specialize (H n refl_equal). destruct N2. contradiction. apply Z.eqb_eq; auto. auto.
  - destruct N2. elim (H 0); auto. specialize (H (n + 1)); lia. auto.
  Qed.

(** [const n] est la valeur abstraite pour l'ensemble singleton [{n}]. *)
  Definition const (n: Z) : t := Just n.

  Lemma const_1: forall n, In n (const n).
  Proof.
    intros; cbn; auto.
  Qed.

(** Les opérations de treillis: [bot], [top], [join]. *)

  Definition bot: t := Bot.

  Lemma bot_1: forall n, ~(In n bot).
  Proof.
    intros. cbn. tauto.
  Qed.
  Definition top: t := Top.

  Lemma top_1: forall n, In n top.
  Proof.
    intros. cbn; auto.
  Qed.

  Definition join (N1 N2: t) : t :=
    match N1, N2 with
    | Bot, _ => N2
    | _, Bot => N1
    | Top, _ => Top
    | _, Top => Top
    | Just n1, Just n2 => if n1 =? n2 then Just n1 else Top
    end.

  Lemma join_1:
    forall n N1 N2, In n N1 -> In n (join N1 N2).
  Proof.
    unfold In, join; intros; cbn.
    destruct N1, N2; try tauto.
    destruct (Z.eqb_spec n0 n1); auto.
  Qed.

  Lemma join_2:
    forall n N1 N2, In n N2 -> In n (join N1 N2).
  Proof.
    unfold In, join; intros; cbn.
    destruct N1, N2; try tauto.
    destruct (Z.eqb_spec n0 n1); auto. congruence.
  Qed.

(** Les opérations arithmétiques abstraites *)

  Definition lift (f: Z -> Z -> Z) : t -> t -> t :=
    fun N1 N2 =>
      match N1, N2 with
      | Bot, _ => Bot
      | _, Bot => Bot
      | Just n1, Just n2 => Just (f n1 n2)
      | _, _ => Top
    end.

  Lemma lift_1:
    forall f n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (f n1 n2) (lift f N1 N2).
  Proof.
    unfold In, lift; intros. destruct N1, N2; try tauto. congruence.
  Qed.

  Definition add := lift Z.add.

  Lemma add_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1+n2) (add N1 N2).
  Proof (lift_1 Z.add).

  Definition sub := lift Z.sub.

  Lemma sub_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1-n2) (sub N1 N2).
  Proof (lift_1 Z.sub).

End FlatInt.

(** *** L'analyse de propagation des constantes *)

(** Il suffit d'instancier l'analyseur sur le domaine plat des entiers
    et sur le domaine des états qui correspond. *)

Module SConstProp := StoreAbstr(FlatInt).
Module AConstProp := Analysis(SConstProp).

(** Un exemple de programme:
<<
    x := 0; y := 100; z := x + y;
    if x = 0
    then y := x + 10; x := 1
    else y := 10
>>
*)

Definition prog1 :=
  ASSIGN "x" (CONST 0) ;;
  ASSIGN "y" (CONST 100) ;;
  ASSIGN "z" (PLUS (VAR "x") (VAR "y")) ;;
  IFTHENELSE (EQUAL (VAR "x") (CONST 0))
    (ASSIGN "y" (PLUS (VAR "x") (CONST 10)) ;; ASSIGN "x" (CONST 1))
    (ASSIGN "y" (CONST 10)).

Compute (let S := AConstProp.Cexec prog1 SConstProp.top in
         (SConstProp.get "x" S, SConstProp.get "y" S, SConstProp.get "z" S)).

(** Résultat:
<<
     = (FlatInt.Top, FlatInt.Just 10, FlatInt.Just 100) 
>>
*)
