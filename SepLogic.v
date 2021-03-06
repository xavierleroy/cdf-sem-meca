From Coq Require Import ZArith Psatz Bool String List Wellfounded Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import IMP Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 4.  Logiques de programmes: logique de séparation *)

(** ** 4.9.  Les tas mémoire (heaps) *)

(** Un tas mémoire est une fonction partielle des adresses dans les
    valeurs, à domaine fini. *)

Definition addr := Z.

Record heap : Type := {
  contents :> addr -> option Z;
  isfinite :  exists i, forall j, i <= j -> contents j = None
}.

Lemma heap_extensionality:
  forall (h1 h2: heap),
  (forall l, h1 l = h2 l) -> h1 = h2.
Proof.
  intros. destruct h1 as [c1 fin1], h2 as [c2 fin2].
  assert (c1 = c2) by (apply functional_extensionality; auto).
  subst c2. f_equal. apply proof_irrelevance.
Qed.

(** Le tas vide. *)

Program Definition hempty : heap :=
  {| contents := fun l => None |}.
Next Obligation.
  exists 0; auto.
Qed.

(** Le tas qui contient [v] à l'adresse [l] est est égal à [h] ailleurs. *)

Program Definition hupdate (l: addr) (v: Z) (h: heap) : heap :=
  {| contents := fun l' => if Z.eq_dec l l' then Some v else h l' |}.
Next Obligation.
  destruct (isfinite h) as (i & fin).
  exists (Z.max i (l + 1)); intros.
  destruct (Z.eq_dec l j). lia. apply fin; lia.
Qed.

Lemma hupdate_same: forall l v h, (hupdate l v h) l = Some v.
Proof.
  intros; cbn. destruct (Z.eq_dec l l); congruence.
Qed.

Lemma hupdate_other: forall l v h l', l <> l' -> (hupdate l v h) l' = h l'.
Proof.
  intros; cbn. destruct (Z.eq_dec l l'); congruence.
Qed.

(** Le tas [h] après désallocation de l'adresse [l]. *)

Program Definition hfree (l: addr) (h: heap) : heap :=
  {| contents := fun l' => if Z.eq_dec l l' then None else h l' |}.
Next Obligation.
  destruct (isfinite h) as (i & fin).
  exists i; intros. destruct (Z.eq_dec l j); auto.
Qed.

(** Le tas [h] où les adresses [l, ..., l + sz - 1] sont initialisées à 0. *)

Fixpoint hinit (l: addr) (sz: nat) (h: heap) : heap :=
  match sz with O => h | S sz => hupdate l 0 (hinit (l + 1) sz h) end.

Lemma hinit_inside:
  forall h sz l l', l <= l' < l + Z.of_nat sz -> hinit l sz h l' = Some 0.
Proof.
  induction sz; intros; cbn.
- lia.
- destruct (Z.eq_dec l l'); auto. apply IHsz. lia.
Qed.

Lemma hinit_outside:
  forall h sz l l', l' < l \/ l + Z.of_nat sz <= l' -> hinit l sz h l' = h l'.
Proof.
  induction sz; intros; cbn.
- auto.
- destruct (Z.eq_dec l l'). lia. apply IHsz; lia.
Qed.

(** L'union disjointe de deux tas. *)

Definition hdisjoint (h1 h2: heap) : Prop :=
  forall l, h1 l = None \/ h2 l = None.

Lemma hdisjoint_sym:
  forall h1 h2, hdisjoint h1 h2 -> hdisjoint h2 h1.
Proof.
  unfold hdisjoint; intros. specialize (H l); tauto.
Qed.

Program Definition hunion (h1 h2: heap) : heap :=
  {| contents := fun l => if h1 l then h1 l else h2 l |}.
Next Obligation.
  destruct (isfinite h1) as (i1 & fin1), (isfinite h2) as (i2 & fin2).
  exists (Z.max i1 i2); intros. rewrite fin1, fin2 by lia. auto.
Qed.

Lemma hunion_comm:
  forall h1 h2, hdisjoint h1 h2 -> hunion h2 h1 = hunion h1 h2.
Proof.
  intros; apply heap_extensionality; intros; cbn.
  specialize (H l). destruct (h1 l), (h2 l); intuition congruence.
Qed.

Lemma hunion_assoc:
  forall h1 h2 h3, hunion (hunion h1 h2) h3 = hunion h1 (hunion h2 h3).
Proof.
  intros; apply heap_extensionality; intros; cbn. destruct (h1 l); auto.
Qed.

Lemma hunion_empty:
  forall h, hunion hempty h = h.
Proof.
  intros; apply heap_extensionality; intros; cbn. auto.
Qed.

(** ** 4.10.  Le langage IMP avec pointeurs et allocation dynamique *)

Inductive com: Type :=
  | SKIP
  | ASSIGN (x: ident) (a: aexp)
  | SEQ (c1: com) (c2: com)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com)
  | WHILE (b: bexp) (c1: com)
  | ALLOC (x: ident) (sz: nat)  (**r allocation de [sz] mots consécutifs *)
  | GET (x: ident) (a: aexp)    (**r lecture à l'adresse [a] *)
  | SET (a1: aexp) (a2: aexp)   (**r écriture de [a2] à l'adresse [a1] *)
  | FREE (a: aexp).             (**r désallocation de l'adresse [a] *)

(** La sémantique à réduction.  Elle opère sur des triplets [(c, s, h)],
    où [c] est une commande et [(s, h)] l'état mémoire courant. *)

(** Les 6 premières règles sont celles de IMP.  Le tas [h] est inchangé.
    Les 4 dernières règles donnent la sémantique des opérations sur le tas:
    [ALLOC], [GET], [SET], [FREE].
*)

Inductive red: com * store * heap -> com * store * heap -> Prop :=
  | red_assign: forall x a s h,
      red (ASSIGN x a, s, h) (SKIP, update x (aeval a s) s, h)
  | red_seq_done: forall c s h,
      red (SEQ SKIP c, s, h) (c, s, h)
  | red_seq_step: forall c1 c s1 h1 c2 s2 h2,
      red (c1, s1, h1) (c2, s2, h2) ->
      red (SEQ c1 c, s1, h1) (SEQ c2 c, s2, h2)
  | red_ifthenelse: forall b c1 c2 s h,
      red (IFTHENELSE b c1 c2, s, h) ((if beval b s then c1 else c2), s, h)
  | red_while_done: forall b c s h,
      beval b s = false ->
      red (WHILE b c, s, h) (SKIP, s, h)
  | red_while_loop: forall b c s h,
      beval b s = true ->
      red (WHILE b c, s, h) (SEQ c (WHILE b c), s, h)
  | red_alloc: forall x sz s (h: heap) l,
      (forall i, l <= i < l + Z.of_nat sz -> h i = None) ->
      l <> 0 ->
      red (ALLOC x sz, s, h) (SKIP, update x l s, hinit l sz h)
  | red_get: forall x a s (h: heap) l v,
      l = aeval a s -> h l = Some v ->
      red (GET x a, s, h) (SKIP, update x v s, h)
  | red_set: forall a1 a2 s (h: heap) l v,
      l = aeval a1 s -> h l <> None -> v = aeval a2 s ->
      red (SET a1 a2, s, h) (SKIP, s, hupdate l v h)
  | red_free: forall a s (h: heap) l,
      l = aeval a s -> h l <> None ->
      red (FREE a, s, h) (SKIP, s, hfree l h).

(** Les variables possiblement modifiées par l'exécution d'une commande. *)

Fixpoint modified_by (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | SEQ c1 c2 => modified_by c1 x \/ modified_by c2 x
  | IFTHENELSE b c1 c2 => modified_by c1 x \/ modified_by c2 x
  | WHILE b c1 => modified_by c1 x
  | ALLOC y sz => x = y
  | GET y a => x = y
  | SET a1 a2 => False
  | FREE a => False
  end.

(** ** 4.11.  Les assertions de la logique de séparation *)

(** Les assertions sont des prédicats sur les deux composantes de
    l'état mémoire. *)

Definition assertion : Type := store -> heap -> Prop.

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun s h => exists a: A, P a s h.

(** L'assertion "le tas est vide" *)

Definition emp : assertion :=
  fun s h => h = hempty.

(** L'assertion "l'adresse [l] contient la valeur [v]". 
    Le domaine du tas doit être le singleton [{l}]. *)

Definition contains (l: addr) (v: Z) : assertion :=
  fun s h => h = hupdate l v hempty.

(** L'assertion "l'adresse [l] est valide". *)

Definition valid (l: addr) : assertion := aexists (contains l).

(** La conjonction séparante. *)

Definition sepconj (P Q: assertion) : assertion :=
  fun s h => exists h1 h2, P s h1
                        /\ Q s h2
                        /\ hdisjoint h1 h2  /\ h = hunion h1 h2.

Notation "P ** Q" := (sepconj P Q) (at level 60, right associativity).

(** On utilise aussi des assertions simples, qui ne dépendent pas du tas
    mais seulement de l'état mémoire.  Ce sont les mêmes assertions
    que celles de la logique de Hoare. *)

Definition simple_assertion : Type := store -> Prop.

(** L'assertion "l'expression arithmétique [a] s'évalue en la valeur [v]". *)

Definition aequal (a: aexp) (v: Z) : simple_assertion :=
  fun s => aeval a s = v.

(** Les assertions "l'expression booléenne [b] s'évalue à vrai / à faux". *)

Definition atrue (b: bexp) : simple_assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : simple_assertion :=
  fun s => beval b s = false.

(** La conjonction d'une assertion pure et d'une assertion générale. *)

Definition pureconj (P: simple_assertion) (Q: assertion) : assertion :=
  fun s h => P s /\ Q s h.

Notation "P //\\ Q" := (pureconj P Q) (at level 60, right associativity).

(** L'égalité extensionnelle entre assertions. *)

Lemma assertion_extensionality:
  forall (P Q: assertion),
  (forall s h, P s h <-> Q s h) -> P = Q.
Proof.
  intros. apply functional_extensionality; intros s.
  apply functional_extensionality; intros h.
  apply propositional_extensionality. auto.
Qed.

(** Les propriétés essentielles de la conjonction séparante. *)

Lemma sepconj_comm: forall P Q, P ** Q = Q ** P.
Proof.
  assert (forall P Q s h, (P ** Q) s h -> (Q ** P) s h).
  { intros P Q s h (h1 & h2 & P1 & Q2 & EQ & DISJ); subst h.
    exists h2, h1; intuition auto.
    apply hdisjoint_sym; auto.
    symmetry; apply hunion_comm; auto. } 
  intros; apply assertion_extensionality; intros; split; auto.
Qed.

Lemma sepconj_assoc: forall P Q R, (P ** Q) ** R = P ** (Q ** R).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (hx & h3 & (h1 & h2 & P1 & Q2 & EQ & DISJ) & R3 & EQ' & DISJ'). subst hx h.
  rewrite hunion_assoc.
  exists h1, (hunion h2 h3); intuition auto.
  exists h2, h3; intuition auto.
  intros l. specialize (EQ l); specialize (EQ' l). cbn in EQ'.
  destruct EQ as [EQ|EQ]. rewrite EQ in EQ'; auto. auto.
  intros l. specialize (EQ l); specialize (EQ' l). cbn in *.
  destruct EQ as [EQ|EQ]. auto. rewrite EQ in *. destruct (h1 l); auto.
- intros (h1 & hx & P1 & (h2 & h3 & Q2 & R3 & EQ & DISJ) & EQ' & DISJ'). subst hx h.
  rewrite <- hunion_assoc.
  exists (hunion h1 h2), h3; intuition auto.
  exists h1, h2; intuition auto.
  intros l. specialize (EQ l); specialize (EQ' l). cbn in EQ'.
  destruct EQ' as [EQ'|EQ']. auto. destruct (h2 l); auto.
  intros l. specialize (EQ l); specialize (EQ' l). cbn in *.
  destruct EQ as [EQ|EQ]. rewrite EQ in *. destruct (h1 l); auto. auto.
Qed.

Lemma sepconj_emp: forall P, emp ** P = P.
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & EMP1 & P2 & EQ & DISJ). red in EMP1. subst h h1.
  rewrite hunion_empty; auto.
- intros. exists hempty, h; intuition auto. 
  red; auto.
  red; auto.
  rewrite hunion_empty; auto.
Qed.

Lemma lift_aexists: forall (A: Type) (P: A -> assertion) Q,
  aexists P ** Q = aexists (fun x => P x ** Q).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & (a & P1) & Q2 & DISJ & EQ).
  exists a, h1, h2; auto.
- intros (a & h1 & h2 & P1 & Q2 & DISJ & EQ).
  exists h1, h2; intuition auto. exists a; auto.
Qed.

Lemma lift_simple_conj: forall P Q R, (P //\\ Q) ** R = P //\\ (Q ** R).
Proof.
  intros; apply assertion_extensionality; intros; split.
- intros (h1 & h2 & (P1 & Q1) & R2 & DISJ & EQ). 
  split; auto. exists h1, h2; auto.
- intros (P1 & (h1 & h2 & Q1 & R2 & DISJ & EQ)). 
  exists h1, h2; intuition auto. split; auto.
Qed.

(** ** 4.12.  Les règles de la logique de séparation. *)

(** Nous voulons définir une logique "forte", qui garantit la terminaison
    sans erreurs des commandes.  Les erreurs possibles sont par exemple
    la lecture ou l'écriture à une adresse mémoire non allouée, ou
    la désallocation d'une adresse déjà désallouée.

    Une définition naturelle du triplet [[P] c [Q]] est la suivante.
*)

Definition triple_base (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s h,
  P s h -> exists s' h', star red (c, s, h) (SKIP, s', h') /\ Q s' h'.

(** Cette définition ne convient pas, car elle ne valide pas de manière
    évidente la règle d'encadrement (frame rule).
    Par exemple, si [c] est une allocation [x := ALLOC(1)],
    on a bien un triplet
<<
       [ emp ]  x := ALLOC(1)  [ aexists (fun l => aequal (VAR "x") l //\\ valid l ]
>>
    Cependant, si on encadre avec [R], l'adresse [l] de l'allocation
    peut tomber dans l'empreinte mémoire de [R].  Et donc la
    postcondition [R ** aexists ...]  peut être fausse. *)

(** Une manière élégante de contourner ce problème est de quantifier
    universellement sur tous les encadrements possibles dans la
    définition même du triplet. *)

Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall h s1 s2,
  (forall x, ~ vars x -> s2 x = s1 x) ->
  P s1 h -> P s2 h.

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall (R: assertion),
  independent_of R (modified_by c) ->
  triple_base (P ** R) c (Q ** R).

(** La règle d'encadrement est alors valide par construction.
    En revanche, les preuves des autres règles de la logique de séparation
    sont un peu plus difficiles, car elles doivent prendre en compte
    cet encadrement systématique par une assertion [R]. *)

Notation "[[ P ]] c [[ Q ]]" := (triple P c Q) (at level 90, c at next level).

Lemma triple_frame: forall P c Q R,
  [[ P ]] c [[ Q ]] ->
  independent_of R (modified_by c) ->
  [[ P ** R ]] c [[ Q ** R ]].
Proof.
  intros P c Q R TR INDR S INDS. rewrite ! sepconj_assoc. apply TR.
  intros h s1 s2 SAME (h1 & h2 & R1 & S2 & DISJ & EQ).
  exists h1, h2; intuition eauto.
Qed.

(** Les "petites règles" pour les opérations sur le tas. *)

Lemma triple_get: forall x a l v,
  [[ aequal a l //\\ contains l v ]]
  GET x a
  [[ aequal (VAR x) v //\\ contains l v ]].
Proof.
  intros; intros R IND s h (h1 & h2 & (P1 & P2) & R1 & DISJ & EQ).
  do 2 econstructor; split.
- apply star_one. apply red_get with (l := l) (v := v); auto. rewrite EQ, P2; cbn. destruct (Z.eq_dec l l); congruence. 
- exists h1, h2; intuition auto.
  + split. red; cbn. apply update_same. auto.
  + apply IND with s; auto. cbn; intros. apply update_other; auto.
Qed.

Lemma triple_set: forall a1 a2 l v,
  [[ aequal a1 l //\\ aequal a2 v //\\ valid l ]]
  SET a1 a2
  [[ contains l v ]].
Proof.
  intros; intros R IND s h (h1 & h2 & (P1 & P2 & P3) & R1 & DISJ & EQ). destruct P3 as (v0 & P3).
  do 2 econstructor; split.
- apply star_one. eapply red_set with (l := l) (v := v); auto. rewrite EQ, P3. cbn. destruct (Z.eq_dec l l); congruence.
- exists (hupdate l v hempty), h2; intuition auto.
  + red; auto. 
  + intros l'. specialize (DISJ l'). rewrite P3 in DISJ. cbn in *. destruct (Z.eq_dec l l'); intuition congruence.
  + rewrite EQ, P3. apply heap_extensionality; intros l'; cbn.
    destruct (Z.eq_dec l l'); auto.
Qed.

Fixpoint valid_N (l: addr) (sz: nat) : assertion :=
  match sz with O => emp | S sz => valid l ** valid_N (l + 1) sz end.

Lemma triple_alloc: forall x sz,
  [[ emp ]]
  ALLOC x sz
  [[ aexists (fun l => aequal (VAR x) l //\\ valid_N l sz) ]].
Proof.
  intros; intros R IND s h (h1 & h2 & EMP & R1 & DISJ & EQ). 
  destruct (isfinite h) as (l0 & FIN). 
  set (l := Z.max l0 1).
  do 2 econstructor; split.
- apply star_one. apply red_alloc with (l := l). intros; apply FIN; lia. lia.
- exists (hinit l sz hempty), h2; intuition auto.
  + exists l; split. red; cbn. apply update_same.
    assert (REC: forall s1 sz1 l1, valid_N l1 sz1 s1 (hinit l1 sz1 hempty)).
    { induction sz1; cbn; intros.
    * red; auto.
    * exists (hupdate l1 0 hempty), (hinit (l1 + 1) sz1 hempty); intuition auto.
      ** exists 0; red; auto.
      ** red; intros. cbn. destruct (Z.eq_dec l1 l2); auto.
         right; apply hinit_outside; lia.
      ** apply heap_extensionality; intros. cbn. destruct (Z.eq_dec l1 l2); auto.
    }
    apply REC.
  + apply IND with s; auto. cbn; intros. apply update_other; auto.
  + intros l'. destruct (Z.lt_ge_cases l' l).
    left; apply hinit_outside; auto.
    right.
    assert (L: h l' = None) by (apply FIN; lia).
    rewrite EQ in L; cbn in L. destruct (h1 l'); congruence.
  + rewrite EQ, EMP, hunion_empty. apply heap_extensionality; intros l'; cbn.
    destruct (Z.lt_ge_cases l' l). rewrite ! hinit_outside by auto. auto. 
    destruct (Z.lt_ge_cases l' (l + Z.of_nat sz)). rewrite ! hinit_inside by auto. auto.
    rewrite ! hinit_outside by auto. auto. 
Qed.

Lemma triple_free: forall a l,
  [[ aequal a l //\\ valid l ]]
  FREE a
  [[ emp ]].
Proof.
  intros; intros R IND s h (h1 & h2 & (P1 & P2) & R1 & DISJ & EQ). destruct P2 as (v0 & P2).
  do 2 econstructor; split.
- apply star_one. apply red_free with (l := l); auto.
  rewrite EQ; cbn. rewrite ! P2, hupdate_same. congruence.
- exists hempty, h2; intuition auto. 
  + red; auto.
  + red; auto.
  + rewrite EQ, P2. apply heap_extensionality; intros l'; cbn.
    destruct (Z.eq_dec l l'); auto.
    subst l'. generalize (DISJ l). rewrite P2, hupdate_same. intuition congruence.
Qed.

(** Les règles pour les autres constructions de IMP.  Elles sont proches
    de celles pour la logique de Hoare forte. *)

Lemma triple_skip:
  [[ emp ]]  SKIP  [[ emp ]].
Proof.
  intros R IND s h PRE. exists s, h; split; auto. apply star_refl.
Qed.

Lemma triple_assign: forall x a n,
  [[ aequal a n //\\ emp ]]
  ASSIGN x a
  [[ aequal (VAR x) n //\\ emp ]].
Proof.
  intros; intros R IND s h (h1 & h2 & (P1 & P2) & R1 & DISJ & EQ).
  do 2 econstructor; split.
- apply star_one. apply red_assign. 
- exists h1, h2; intuition auto.
  + split; auto. red; cbn. rewrite update_same; auto.
  + apply IND with s; auto. cbn; intros. apply update_other; auto.
Qed.

Remark star_red_seq_step:
  forall c1 s1 h1 c2 s2 h2, star red (c1, s1, h1) (c2, s2, h2) ->
  forall c, star red (SEQ c1 c, s1, h1) (SEQ c2 c, s2, h2).
Proof.
  intros until h2; intros STAR; dependent induction STAR; intros.
- apply star_refl.
- destruct b as [ [c' s'] h']. eapply star_step; eauto. apply red_seq_step; auto.
Qed. 

Lemma triple_seq: forall c1 c2 P Q R,
  [[ P ]] c1 [[ Q ]] -> [[ Q ]] c2 [[ R ]] -> [[ P ]] SEQ c1 c2 [[ R ]].
Proof.
  intros; intros S IND s h A0.
  assert (IND1: independent_of S (modified_by c1)).
  { red; intros; apply IND with s1; auto. cbn. intros; apply H1; tauto. }
  assert (IND2: independent_of S (modified_by c2)).
  { red; intros; apply IND with s1; auto. cbn. intros; apply H1; tauto. }
  destruct (H S IND1 s h A0) as (s1 & h1 & EXEC1 & A1).
  destruct (H0 S IND2 s1 h1 A1) as (s2 & h2 & EXEC2 & A2).
  exists s2, h2; split; auto.
  eapply star_trans. apply star_red_seq_step; eauto.
  eapply star_step. apply red_seq_done. auto.
Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  [[ atrue  b //\\ P ]] c1 [[ Q ]] ->
  [[ afalse b //\\ P ]] c2 [[ Q ]] ->
  [[ P ]] IFTHENELSE b c1 c2 [[ Q ]].
Proof.
  intros; intros R IND s h PRE. destruct (beval b s) eqn:B.
- assert (IND1: independent_of R (modified_by c1)).
  { red; intros. apply IND with s1; auto. cbn; intros; apply H1; tauto. }
  destruct (H R IND1 s h) as (s' & h' & EXEC & POST).
  rewrite lift_simple_conj. split; auto.
  exists s', h'; split; auto.
  eapply star_step. apply red_ifthenelse. rewrite B. auto.
- assert (IND2: independent_of R (modified_by c2)).
  { red; intros. apply IND with s1; auto. cbn; intros; apply H1; tauto. }
  destruct (H0 R IND2 s h) as (s' & h' & EXEC & POST).
  rewrite lift_simple_conj. split; auto.
  exists s', h'; split; auto.
  eapply star_step. apply red_ifthenelse. rewrite B. auto.
Qed.

Definition alessthan (a: aexp) (v: Z) : simple_assertion :=
  fun (s: store) => 0 <= aeval a s < v.

Lemma triple_while: forall P variant b c,
  (forall v,
     [[ atrue b //\\ aequal variant v //\\ P]]
     c
     [[ alessthan variant v //\\ P]])
  ->
     [[ P ]] WHILE b c [[ afalse b //\\ P ]].
Proof.
  intros P variant b c TR.
  assert (REC: forall v,
               [[ aequal variant v //\\ P ]]
               WHILE b c
               [[ afalse b //\\ P ]]).
  { induction v using (well_founded_induction (Z.lt_wf 0)).
    intros R IND s h PRE.
    assert (IND1: independent_of R (modified_by c)).
    { red; intros; apply IND with s1; auto. }
    destruct (beval b s) eqn:B.
  - destruct (TR v R IND1 s h) as (s1 & h1 & EXEC1 & POST1).
    rewrite lift_simple_conj. split; auto.
    rewrite lift_simple_conj in POST1. destruct POST1 as (LT & POST1).
    destruct (H (aeval variant s1) LT R IND s1 h1) as (s2 & h2 & EXEC2 & POST2).
    rewrite lift_simple_conj. split; auto. red; auto.
    exists s2, h2; split; auto.
    eapply star_step. apply red_while_loop. auto.
    eapply star_trans. apply star_red_seq_step. eexact EXEC1. 
    eapply star_step. apply red_seq_done.
    exact EXEC2.
  - rewrite lift_simple_conj in PRE. destruct PRE as (EQ & POST1).
    exists s, h; split.
    + apply star_one. apply red_while_done. auto.
    + rewrite lift_simple_conj. split; auto.
  }
  intros R IND s h PRE.
  apply (REC (aeval variant s) R IND s h).
  rewrite lift_simple_conj. split; auto. red; auto.
Qed.

(** La règle de conséquence. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s h, P s h -> Q s h.

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).

Remark aimp_sepconj: forall P P' Q,
  P -->> P' -> P ** Q -->> P' ** Q.
Proof.
  intros; red. intros s h (h1 & h2 & P1 & Q2 & DISJ & EQ). exists h1, h2; auto.
Qed.

Lemma triple_consequence: forall P P' c Q' Q,
  P -->> P'  ->  [[ P' ]] c [[ Q' ]]  ->  Q' -->> Q  ->
  [[ P ]] c [[ Q ]].
Proof.
  intros; intros R IND s h PRE.
  destruct (H0 R IND s h) as (s' & h' & EXEC & POST).
  apply aimp_sepconj with P; auto.
  exists s', h'; split; auto. apply aimp_sepconj with Q'; auto.
Qed.

