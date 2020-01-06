From Coq Require Import ZArith Psatz Bool String List Wellfounded Program.Equality.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import IMP Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 4.  Logiques de programmes: logique de Hoare *)

(** ** 4.1.  Prologue: vérifier directement un programme  *)

(** On peut vérifier la correction d'un programme en utilisant uniquement la
    sémantique opérationnelle du langage dans lequel il est écrit.  Par exemple,
    voici un programme IMP qui échange les valeurs de deux variables. *)

Definition swap_xy :=
  ASSIGN "t" (VAR "x");; ASSIGN "x" (VAR "y");; ASSIGN "y" (VAR "t").

(** On peut caractériser le comportement attendu du programme comme suit:
    démarré dans un état mémoire [s], il termine toujours et dans un état
    mémoire [s'] où ["x"] vaut [s "y"] et ["y"] vaut [s "x"]. *)

Lemma swap_xy_correct:
  forall s, exists s',
  star red (swap_xy, s) (SKIP, s') /\ s' "x" = s "y" /\ s' "y" = s "x".
Proof.
  intros. econstructor; split.
- eapply star_step. apply red_seq_step. apply red_assign.
  eapply star_step. apply red_seq_done.
  eapply star_step. apply red_seq_step. apply red_assign.
  eapply star_step. apply red_seq_done.
  eapply star_step. apply red_assign.
  apply star_refl.
- unfold update; cbn. auto.
Qed.

(** La démonstration est longue mais pas très difficile.  Dans un premier temps
    on fait l'exécution "symbolique" du programme en enchaînant les étapes
    de réduction.  Cela détermine l'état final [s'], qui vérifie facilement
    la propriété attendue. *)

(** Voici un exemple plus compliqué car il fait appel à une boucle.
    Le programme ajoute ["x"] à ["y"] en incrémentant ["y"] et décrémentant ["x"]
    jusqu'à ce que ["x"] tombe à zéro. *)

Definition slow_add :=
  WHILE (LESSEQUAL (CONST 1) (VAR "x"))
        (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
         ASSIGN "y" (PLUS  (VAR "y") (CONST 1))).

(** L'énoncé de correction du programme reste simple. *)

Lemma slow_add_correct:
  forall s,
  s "x" >= 0 ->
  exists s', star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x".
Proof.
  assert (REC: forall v, 0 <= v -> 
               forall s, s "x" = v ->
               exists s', star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x").
  { intros v0 v0POS. pattern v0. apply natlike_ind; auto.
  - intros. exists s; split.
    + apply star_one. apply red_while_done. cbn. rewrite H. apply Z.leb_nle. lia.
    + lia.
  - intros v VPOS REC s EQ.
    set (s1 := update "x" v s).
    set (s2 := update "y" (s "y" + 1) s1).
    destruct (REC s2) as (s' & REDS & EQ'). auto.
    exists s'; split.
    + eapply star_step. apply red_while_loop. cbn. rewrite EQ. apply Z.leb_le. lia.
      eapply star_step. apply red_seq_step. apply red_seq_step. apply red_assign.
      eapply star_step. apply red_seq_step. apply red_seq_done.
      eapply star_step. apply red_seq_step. apply red_assign.
      eapply star_step. apply red_seq_done.
      cbn. replace (s "x" - 1) with v by lia. apply REDS.
    + rewrite EQ'. cbn. lia.
  }
  intros. eapply REC; eauto. lia.
Qed.

(** En revanche, la démonstration devient difficile.  Il faut faire
    une récurrence explicite sur la valeur [v] de la variable ["x"].
    Pour exploiter l'hypothèse de récurrence, il faut déterminer
    manuellement certains états mémoire intermédiaires: l'exécution
    purement symbolique ne suffit plus.  On ne se voit pas vérifier
    des programmes beaucoup plus complexes avec ces techniques. *)

(** Les logiques de programmes fournissent des principes de plus haut
    niveau pour vérifier formellement des programmes.  En particulier,
    on peut raisonner sur les boucles sans faire de récurrence
    explicite.  *)

(** La logique de programmes la plus connue est la logique de Hoare.
    Dans ce fichier, nous construisons une logique de Hoare pour
    raisonner sur les programmes écrits en langage IMP. *)

(** ** 4.2.  Assertions sur l'état mémoire *)

(** La logique de Hoare manipule des formules / des énoncés / des assertions
    qui "parlent" des valeurs des variables du programme.  Une assertion typique
    est [0 <= x /\ x <= y], signifiant "à ce point du programme, la valeur de
    la variable [x] est positive et inférieure ou égale à la valeur de [y]".

    Dans notre développement Coq, nous représentons les assertions par
    des formules logique de Coq (type [Prop]) paramétrées par un état mémoire
    (type [store]) qui donne des valeurs aux variables.
  
    Par exemple, l'assertion [0 <= x /\ x <= y] ci-dessus est représentée par
    [fun s => 0 <= s "x" /\ s "x" <= s "y"]. *)
    
Definition assertion : Type := store -> Prop.

(** Voici quelques assertions utiles.  La conjonction et la disjonction de deux
    assertions. *)

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

(** L'assertion "l'expression arithmétique [a] s'évalue en la valeur [v]". *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun s => aeval a s = v.

(** Les assertions "l'expression booléenne [b] s'évalue à vrai / à faux". *)

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

(** L'assertion notée "P[x <- a]" dans les articles.  Substituer [x] par [a]
    dans [P], cela revient à évaluer [P] dans des états mémoire où
    la variable [x] est égale à la valeur de l'expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

(** L'implication point-à-point.  Contrairement à la conjonction et la disjonction,
    ce n'est pas une assertion sur l'état mémoire, juste une proposition Coq. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

(** Quelques notations pour faciliter la lecture. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

(** ** 4.3.  Règles de la logique de Hoare faible *)

(** Voici les règles de base de la logique de Hoare.
    Elles définissent une relation [Hoare P c Q], avec
  - [P] la précondition, que l'on suppose vraie "avant" l'exécution de [c];
  - [c] le programme ou le fragment de programme sur lequel on raisonne;
  - [Q] la postcondition, que l'on garantit vraie "après" l'exécution de [c].

  Il s'agit d'une logique "faible" au sens où elle ne garantit pas la terminaison
  de [c].  La seule garantie est que si [c] termine, alors l'état final
  satisfait la postcondition [Q]. *)

Inductive Hoare: assertion -> com -> assertion -> Prop :=
  | Hoare_skip: forall P,
      Hoare P SKIP P
  | Hoare_assign: forall P x a,
      Hoare (aupdate x a P) (ASSIGN x a) P
  | Hoare_seq: forall P Q R c1 c2,
      Hoare P c1 Q -> Hoare Q c2 R ->
      Hoare P (c1;;c2) R
  | Hoare_ifthenelse: forall P Q b c1 c2,
      Hoare (atrue b //\\ P) c1 Q ->
      Hoare (afalse b //\\ P) c2 Q ->
      Hoare P (IFTHENELSE b c1 c2) Q
  | Hoare_while: forall P b c,
      Hoare (atrue b //\\ P) c P ->
      Hoare P (WHILE b c) (afalse b //\\ P)
  | Hoare_consequence: forall P Q P' Q' c,
      Hoare P c Q ->  P' -->> P -> Q -->> Q' ->
      Hoare P' c Q'.

(** Quelques règles dérivées. *)

Lemma Hoare_consequence_pre: forall P P' Q c,
      Hoare P c Q -> P' -->> P ->
      Hoare P' c Q.
Proof.
  intros. apply Hoare_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      Hoare P c Q -> Q -->> Q' ->
      Hoare P c Q'.
Proof.
  intros. apply Hoare_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_ifthen: forall b c P Q,
    Hoare (atrue b //\\ P) c Q ->
    afalse b //\\ P -->> Q ->
    Hoare P (IFTHENELSE b c SKIP) Q.
Proof.
  intros. apply Hoare_ifthenelse; auto.
  apply Hoare_consequence_pre with Q; auto using Hoare_skip.
Qed.

(** Un exemple de dérivation. *)

Example Hoare_swap_xy: forall m n,
  Hoare (aequal (VAR "x") m //\\ aequal (VAR "y") n)
        swap_xy
        (aequal (VAR "x") n //\\ aequal (VAR "y") m).
Proof.
  intros.
  eapply Hoare_consequence_pre.
- unfold swap_xy. eapply Hoare_seq. apply Hoare_assign.
  eapply Hoare_seq. apply Hoare_assign. apply Hoare_assign.
- unfold aequal, aupdate, aand, aimp; cbn. tauto.
Qed.

(** *** Exercice (1 étoile) *)
(** Voici une autre manière d'échanger les valeurs de deux variables entières,
    sans utiliser de variable temporaire. *)

Definition swap_xy_2 :=
  ASSIGN "x" (PLUS (VAR "x") (VAR "y")) ;;
  ASSIGN "y" (MINUS (VAR "x") (VAR "y")) ;;
  ASSIGN "x" (MINUS (VAR "x") (VAR "y")).

(** Montrer que ce programme satisfait la même propriété que [swap_xy].
    Indication: reprendre le script de preuve de [Hoare_swap_xy],
    l'adaptation à effectuer est minimale. *)

Example Hoare_swap_xy_2: forall m n,
  Hoare (aequal (VAR "x") m //\\ aequal (VAR "y") n)
        swap_xy_2
        (aequal (VAR "x") n //\\ aequal (VAR "y") m).
Proof.
  (* A COMPLÉTER *)
Admitted.

(** 4.4.  Sûreté de la logique de Hoare *)

(** On va interpréter sémantiquement les énoncés [Hoare P c Q] de la
    logique de Hoare par la relation [triple P c Q] ci-dessous,
    définie en termes de la sémantique naturelle d'IMP
    (la relation [cexec s c s']). *)

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s s', cexec s c s' -> P s -> Q s'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

(** L'interprétation sémantique valide chacune des règles de la
    logique de Hoare. *)

Lemma triple_skip: forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold triple; intros. inversion H; subst. auto.
Qed.

Lemma triple_assign: forall P x a,
      {{aupdate x a P}} ASSIGN x a {{P}}.
Proof.
  unfold triple, aupdate; intros. inversion H; subst. auto.
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      {{P}} c1 {{Q}} -> {{Q}} c2 {{R}} ->
      {{P}} c1;;c2 {{R}}.
Proof.
  unfold triple; intros. inversion H1; subst. eauto.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      {{atrue b //\\ P}} c1 {{Q}} ->
      {{afalse b //\\ P}} c2 {{Q}} ->
      {{P}} IFTHENELSE b c1 c2 {{Q}}.
Proof.
  unfold triple, aand, atrue, afalse; intros. inversion H1; subst.
  destruct (beval b s) eqn:B; eauto.
Qed.

Lemma triple_while: forall P b c,
      {{atrue b //\\ P}} c {{P}} ->
      {{P}} WHILE b c {{afalse b //\\ P}}.
Proof.
  unfold triple; intros P b c T s s' E. dependent induction E; intros.
- split; auto.
- eapply IHE2; eauto. apply T with s; auto. split; auto.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      {{P}} c {{Q}} -> P' -->> P -> Q -->> Q' ->
      {{P'}} c {{Q'}}.
Proof.
  unfold triple, aimp; intros. eauto.
Qed.

(** Il s'ensuit que la logique de Hoare est sûre: tout triplet déductible par
    les règles de la logique est sémantiquement valide. *)

Theorem Hoare_sound:
  forall P c Q, Hoare P c Q -> {{P}} c {{Q}}.
Proof.
  induction 1; eauto using triple_skip, triple_assign, triple_seq,
  triple_ifthenelse, triple_while, triple_consequence.
Qed.

(** 4.5.  Complétude de la logique de Hoare *)

(** La réciproque du théorème [Hoare_sound] est vraie: un "triplet de Hoare"
    qui est vrai sémantiquement ([{{P}} c {{Q}}]) peut toujours être dérivé
    par les règles de Hoare ([Hoare P c Q]).  La démonstration utilise la
    notion de "plus faible précondition" ("weakest precondition", WP). *)

(** La plus faible précondition pour une commande [c] avec postcondition [Q]. *)

Definition wp (c: com) (Q: assertion) : assertion :=
  fun s => forall s', cexec s c s' -> Q s'.

(** C'est une précondition. *)

Lemma wp_precondition: forall c Q, {{wp c Q}} c {{Q}}.
Proof.
  unfold triple, wp; intros. auto.
Qed.

(** C'est la plus faible des préconditions: toute autre précondition l'implique. *)

Lemma wp_weakest: forall P c Q, {{P}} c {{Q}} -> P -->> wp c Q.
Proof.
  unfold triple, wp, aimp; intros. eauto.
Qed.

(** Les règles de la logique de Hoare sont suffisamment puissantes pour dériver
    le fait que [wp c Q] est une précondition valide pour [c] et [Q]. *)

Lemma Hoare_wp: forall c Q, Hoare (wp c Q) c Q.
Proof.
  induction c; intros Q.
- (* SKIP *)
  eapply Hoare_consequence_pre. apply Hoare_skip. 
  unfold aimp, wp; intros. apply H. apply cexec_skip.
- (* ASSIGN *)
  eapply Hoare_consequence_pre. apply Hoare_assign.
  unfold aimp, aupdate, wp; intros. apply H. apply cexec_assign.
- (* SEQ *)
  eapply Hoare_consequence_pre.
  eapply Hoare_seq with (wp c2 Q); eauto.
  unfold aimp, wp; intros. apply H. apply cexec_seq with s'; auto.
- (* IFTHENELSE *)
  apply Hoare_ifthenelse.
  + eapply Hoare_consequence_pre. apply IHc1.
    unfold atrue, aand, aimp, wp; intros. destruct H.
    apply H1. apply cexec_ifthenelse. rewrite H; auto.
  + eapply Hoare_consequence_pre. apply IHc2.
    unfold afalse, aand, aimp, wp; intros. destruct H.
    apply H1. apply cexec_ifthenelse. rewrite H; auto.
- (* WHILE *)
  eapply Hoare_consequence_post.
  + apply Hoare_while.
    eapply Hoare_consequence_pre. apply IHc.
    unfold atrue, aand, aimp, wp; intros. destruct H.
    apply H2. apply cexec_while_loop with s'; auto.
  + unfold afalse, aand, aimp, wp; intros. destruct H.
    apply H0. apply cexec_while_done; auto.
Qed.

(** Il s'ensuit que tout triplet [{{P}} c {{Q}}] sémantiquement valide 
    est dérivable par les règles de Hoare. *)

Theorem Hoare_complete: forall P c Q, {{P}} c {{Q}} -> Hoare P c Q.
Proof.
  intros. apply Hoare_consequence_pre with (wp c Q). 
- apply Hoare_wp.
- apply wp_weakest; auto.
Qed.

(** 4.6.  Autres règles utiles *)

(** Avec la définition sémantique des triplets de Hoare, il est très facile
    d'ajouter des règles de raisonnement supplémentaires.  Ce sont juste
    des lemmes que l'on démontre une fois pour toute.  Par exemple: *)

Lemma triple_conj:
  forall c P1 Q1 P2 Q2,
  {{P1}} c {{Q1}} -> {{P2}} c {{Q2}} -> {{P1 //\\ P2}} c {{Q1 //\\ Q2}}.
Proof.
  intros; red; intros. destruct H2 as [PRE1 PRE2]. split; eauto.
Qed.

Lemma triple_disj:
  forall c P1 Q1 P2 Q2,
  {{P1}} c {{Q1}} -> {{P2}} c {{Q2}} -> {{P1 \\// P2}} c {{Q1 \\// Q2}}.
Proof.
  intros; red; intros. destruct H2 as [PRE1|PRE2]; [left|right]; eauto.
Qed.

(** Nous pouvons aussi donner une règle de raisonnement sur l'affectation
    qui fonctionne "en avant" (la postcondition est déterminée à partir
    de la précondition) au lieu de "en arrière" comme la règle de Hoare. *)

Lemma triple_assign_fwd_1: forall x a P m n,
  {{ P //\\ aequal (VAR x) m //\\ aequal a n }}
  ASSIGN x a
  {{ aupdate x (CONST m) P //\\ aequal (VAR x) n }}.
Proof.
  unfold triple, aequal, aupdate; intros.
  destruct H0 as (PRE1 & PRE2 & PRE3). cbn in PRE2.
  inversion H; subst.
  cbn; split.
- replace (update x (s x) (update x (aeval a s) s)) with s. auto.
  apply functional_extensionality; intros y.
  unfold update. destruct (string_dec x y); congruence.
- apply update_same.
Qed.

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Lemma triple_assign_fwd: forall x a P,
  {{ P }}
  ASSIGN x a 
  {{ aexists (fun m => aexists (fun n =>
     aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) }}.
Proof.
  intros. unfold triple, aequal, aupdate; intros.
  inversion H; subst.
  exists (s x); exists (aeval a s); cbn.
  split. apply update_same.
  replace (update x (s x) (update x (aeval a s) s)) with s.
  split; auto.
  apply functional_extensionality; intros y.
  unfold update. destruct (string_dec x y); congruence.
Qed.

(** Pour finir, nous allons construire une règle d'encadrement
    ("frame rule" en anglais) qui permet de réutiliser une vérification
    déjà effectuée de [{{P} c {{Q}}]
    pour ajouter des faits supplémentaires [R]
    à la précondition et à la postcondition,
    obtenant une vérification de [{{P //\\ R}} c {{Q //\\ R}}]. *)

(** Par exemple: si on a montré la correction de [swap_xy] comme suit
<<<
    {{ aequal (VAR "x") m //\\ aequal (VAR "y") n }}
    swap_xy
    {{ aequal (VAR "x") n //\\ aequal (VAR "y") m }}
>>>
    on devrait pouvoir, sans refaire la vérification de [swap_xy],
    montrer un triplet plus informatif, comme par exemple
<<<
    {{ aequal (VAR "x") m //\\ aequal (VAR "y") n //\\ aequal (VAR "z") p }}
    swap_xy
    {{ aequal (VAR "x") n //\\ aequal (VAR "y") m //\\ aequal (VAR "z") p }}
>>>
    c'est à dire: "et en plus la valeur de la variable [z] est préservée". *)

(** Ce raisonnement est valide à condition que les faits supplémentaires [R]
    portent uniquement sur des variables qui sont pas modifiées
    pendant l'exécution de la commande [c], c'est-à-dire des variables
    qui n'apparaissent pas dans une construction [ASSIGN] de [c]. *)

Fixpoint modified_by (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | SEQ c1 c2 => modified_by c1 x \/ modified_by c2 x
  | IFTHENELSE b c1 c2 => modified_by c1 x \/ modified_by c2 x
  | WHILE b c1 => modified_by c1 x
  end.

Lemma cexec_modified:
  forall x s1 c s2,
  cexec s1 c s2 -> ~modified_by c x -> s2 x = s1 x.
Proof.
  induction 1; cbn; intros MB.
- auto.
- unfold update. destruct (string_dec x0 x); congruence.
- rewrite IHcexec2, IHcexec1 by tauto. auto.
- apply IHcexec. destruct (beval b s); tauto.
- auto.
- rewrite IHcexec2, IHcexec1 by tauto. auto.
Qed.

(** Syntaxiquement, une assertion [P] est indépendante d'un ensemble [vars]
    de variables si aucune de ces variables n'apparaît dans [P].
    Avec notre codage des assertions comme fonctions [store -> Prop],
    on ne peut pas exprimer cette condition de cette manière.
    Mais on peut dire que l'assertion prend la même valeur de vérité
    dans deux états [s1] et [s2] qui ne diffèrent que par les valeurs
    des variables dans [vars]. *)

Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall s1 s2,
  (forall x, ~ vars x -> s1 x = s2 x) ->
  (P s1 <-> P s2).

(** Finalement, on obtient la règle d'encadrement suivante. *)

Lemma triple_frame:
  forall c P Q R,
  {{P}} c {{Q}} ->
  independent_of R (modified_by c) ->
  {{P //\\ R}} c {{Q //\\ R}}.
Proof.
  intros; red; intros. destruct H2 as [PRE1 PRE2]. split.
- eapply H; eauto.
- apply (H0 s' s).
  + intros. apply cexec_modified with c; auto.
  + auto.
Qed.

(** 4.7.  Triplets de Hoare forts *)

(** La logique de Hoare que nous avons vue jusqu'ici est dite "faible"
    car elle ne garantit pas la terminaison des programmes, et ne peut
    donc montrer que des résultats de correction partielle. *)

(** En suivant les mêmes approches, nous allons maintenant construire
    une logique de Hoare "forte", qui garantit la terminaison
    et montre donc des résultats de correction totale. *)

(** Comme nous avons fait pour la logique "faible", nous pourrions
    donner les règles de la logique "forte" sous forme de prédicat
    inductif, puis les interpréter sémantiquement.  Pour simplifier,
    nous omettons le prédicat inductif et définissons la logique "forte"
    directement à partir de la sémantique opérationnelle, via la relation
    [ [[P]] c [[Q]] ] ci-dessous: *)

Definition Triple (P: assertion) (c: com) (Q: assertion) :=
  forall s, P s -> exists s', cexec s c s' /\ Q s'.

Notation "[[ P ]] c [[ Q ]]" := (Triple P c Q) (at level 90, c at next level).

(** Notons la différence avec la logique faible:
  - Pour la logique faible [ {{P}} c {{Q}} ], on conclut
    "si [c] termine alors l'état final [s'] satisfait [Q]".
  - Pour la logique forte [ [[P]] c [[Q]] ], on conclut
    "[c] termine et l'état final [s'] satisfait [Q]".
*)

(** Les règles de base de la logique forte sont les mêmes que celles de la
    logique faible, sauf pour les boucles. *)

Lemma Triple_skip: forall P,
      [[P]] SKIP [[P]].
Proof.
  intros P s PRE. exists s; split; auto. apply cexec_skip.
Qed.

Lemma Triple_assign: forall P x a,
      [[aupdate x a P]] ASSIGN x a [[P]].
Proof.
  intros P x a s PRE. exists (update x (aeval a s) s); split.
- apply cexec_assign.
- exact PRE.
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      [[P]] c1 [[Q]] -> [[Q]] c2 [[R]] ->
      [[P]] c1;;c2 [[R]].
Proof.
  intros; intros s PRE. 
  destruct (H s PRE) as (s1 & EXEC1 & MID).
  destruct (H0 s1 MID) as (s2 & EXEC2 & POST).
  exists s2; split.
- apply cexec_seq with s1; auto.
- exact POST.
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      [[atrue b //\\ P]] c1 [[Q]] ->
      [[afalse b //\\ P]] c2 [[Q]] ->
      [[P]] IFTHENELSE b c1 c2 [[Q]].
Proof.
  intros; intros s PRE. destruct (beval b s) eqn:B.
- destruct (H s) as (s' & EXEC & POST). split; auto.
  exists s'; split; auto. constructor; rewrite B; auto.
- destruct (H0 s) as (s' & EXEC & POST). split; auto.
  exists s'; split; auto. constructor; rewrite B; auto.
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      [[P]] c [[Q]] -> P' -->> P -> Q -->> Q' ->
      [[P']] c [[Q']].
Proof.
  intros; intros s PRE.
  destruct (H s) as (s' & EXEC & POST). apply H0; auto.
  exists s'; auto.
Qed.

(** Pour les boucles [WHILE b c], le triplet fort doit garantir la terminaison
    de la boucle pour tous les états initiaux satisfaisant la précondition.
    Une manière simple de garantir la terminaison est d'exhiber une "variante":
    une expression à valeurs entières qui décroît strictement à chaque
    tour de boucle tout en restant positive. *)

Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun (s: store) => 0 <= aeval a s < v.

Lemma Triple_while: forall P variant b c,
  (forall v,
     [[ P //\\ atrue b //\\ aequal variant v ]]
     c
     [[ P //\\ alessthan variant v ]])
  ->
     [[P]] WHILE b c [[P //\\ afalse b]].
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
  intros s PRE. apply REC with (v := aeval variant s); auto.
Qed.

(** *** Exercice (3 étoiles) *)

(** La technique de la "variante" et l'ordre sur les entiers positifs
    ne suffisent pas toujours à montrer la terminaison d'une boucle
    [WHILE].  Voici une règle qui utilise deux variantes et l'ordre
    lexicographique entre paires d'entiers positifs.  Montrer que
    cette règle est valide. *)

Lemma Triple_while_lexico: forall P variant1 variant2 b c,
  (forall v1 v2,
    [[ P //\\ atrue b //\\ aequal variant1 v1 //\\ aequal variant2 v2 ]]
    c
    [[ P //\\ (alessthan variant1 v1 \\// aequal variant1 v1 //\\ alessthan variant2 v2) ]])
  ->
    [[P]] WHILE b c [[P //\\ afalse b]].
Proof.
  intros P variant1 variant2 b c T.
  assert (REC: forall v1 v2 s, P s -> aeval variant1 s = v1 -> aeval variant2 s = v2 ->
               exists s', cexec s (WHILE b c) s' /\ (P s' /\ beval b s' = false)).
  (* A COMPLÉTER *)
Admitted.

(** ** 4.8.  Génération des conditions de vérification *)

(** Exceptée la règle pour les boucles [WHILE], les règles de la logique de Hoare
    pewuvent se lire comme un algorithme qui, étant données une commande [c]
    et une postcondition [Q], calcule une plus faible précondition [P].
    Par exemple, si [c] se compose de deux affectations en séquence
<<
    c = ASSIGN x1 a1 ;; ASSIGN x2 a2
>>
    la précondition [P] est déterminée comme
<<
    P = aupdate x1 a1 (aupdate x2 a2 Q)
>>
    Un tel calcul est beaucoup plus simple qu'une recherche de preuve
    générale, cette dernière pouvant faire intervenir la règle
    d'affaiblissement [triple_consequence] à tout moment. *)

(** Le problème est bien entendu les boucles [WHILE].  L'invariant de la boucle
    ne peut pas être déterminé automatiquement par calcul.

    Dans ce qui suit, nous développons une approche hybride où les boucles
    sont annotées manuellement par leurs invariants de boucle, mais où toutes
    les autres préconditions sont calculées automatiquement à partir des
    postconditions. *)

Module VCGEN.

(** Voici le langage des commandes avec les boucles [WHILE] annotées par
    un invariant [Inv]. *)

Inductive com: Type :=
  | SKIP
  | ASSIGN (x: ident) (a: aexp)
  | SEQ (c1: com) (c2: com)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com)
  | WHILE (Inv: assertion) (b: bexp) (c1: com).  (**r nouveau! *)

(** La fonction [pre c Q] calcule une précondition pour la commande [c]
    et la postcondition [Q], par "exécution en arrière" de la commande [c] et
    application des règles de la logique de Hoare.  Seule exception: pour
    les boucles [WHILE], on prend l'invariant déclaré pour la boucle comme
    précondition. *)

Fixpoint pre (c: com) (Q: assertion) : assertion :=
  match c with
  | SKIP => Q
  | ASSIGN x a => aupdate x a Q
  | SEQ c1 c2 => pre c1 (pre c2 Q)
  | IFTHENELSE b c1 c2 => atrue b //\\ pre c1 Q \\// afalse b //\\ pre c2 Q
  | WHILE Inv b c => Inv
  end.

(** Le triplet de Hoare [ {{ pre c Q }} c {{ Q }} ] n'est pas toujours vrai:
    il faut aussi s'assurer que les invariants déclarés pour les boucles sont
    bien des invariants.  Pour une boucle [WHILE Inv b c] de postcondition [Q],
    il faut que
  - [afalse b //\\ Inv -->> Q] : 
    quand on sort de la boucle, l'invariant implique la postcondition.
  - [atrue b //\\ Inv -->> pre c Inv] :
    quand on itère la boucle, l'invariant implique la précondition du corps
    de la boucle.

    La fonction [vcg] (Verification Condition Generator) ci-dessous collecte
    ces "conditions de vérification" pour toutes les boucles [WHILE]
    apparaissant dans la commande [c]. *)

Fixpoint vcg (c: com) (Q: assertion) : Prop :=
  match c with
  | SKIP => True
  | ASSIGN x a => True
  | SEQ c1 c2 => vcg c1 (pre c2 Q) /\ vcg c2 Q
  | IFTHENELSE b c1 c2 => vcg c1 Q /\ vcg c2 Q
  | WHILE Inv b c =>
       vcg c Inv
    /\ (afalse b //\\ Inv -->> Q)
    /\ (atrue b //\\ Inv -->> pre c Inv)
  end.

(** Le triplet [ {{P}} c {{Q}} ] est valide dès lors que
  - [P] implique la précondition [pre c Q]
  - les conditions [vcg c Q] sont toutes vraies.
*)

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  (P -->> pre c Q) /\ vcg c Q.

(** Pour montrer la correction de cet algorithme de vérification,
    nous définissons l'effacement [erase c] d'une commande annotée
    en commande IMP standard.  Il s'agit juste d'oublier les invariants
    de boucles qui annotent les noeuds [WHILE]. *)

Fixpoint erase (c: com) : IMP.com :=
  match c with
  | SKIP => IMP.SKIP
  | ASSIGN x a => IMP.ASSIGN x a
  | SEQ c1 c2 => IMP.SEQ (erase c1) (erase c2)
  | IFTHENELSE b c1 c2 => IMP.IFTHENELSE b (erase c1) (erase c2)
  | WHILE Inv b c => IMP.WHILE b (erase c)
  end.

(** Nous pouvons alors montrer que [pre c Q] est une précondition valide
    de [c] et de [Q], pourvu que les conditions [vcg c Q] soient vraies. *)

Lemma vcg_sound:
  forall c Q, vcg c Q -> {{pre c Q}} erase c {{Q}}.
Proof.
  induction c; cbn; intros.
- apply triple_skip.
- apply triple_assign.
- destruct H as (V1 & V2).
  apply triple_seq with (pre c2 Q); auto.
- destruct H as (V1 & V2). 
  apply triple_ifthenelse.
  + eapply triple_consequence. eapply IHc1; eauto.
    unfold aimp, aand, aor, atrue, afalse. intuition congruence.
    unfold aimp; auto.
  + eapply triple_consequence. eapply IHc2; eauto.
    unfold aimp, aand, aor, atrue, afalse. intuition congruence.
    unfold aimp; auto.
- destruct H as (V1 & V2 & V3).
  eapply triple_consequence.
  + apply triple_while. eapply triple_consequence. apply IHc; eauto.
    eauto. red; auto.
  + red; auto.
  + auto.
Qed.

(** On en déduit la correction de l'algorithme [vcgen]. *)

Theorem vcgen_correct:
  forall P c Q, vcgen P c Q -> {{P}} erase c {{Q}}.
Proof.
  unfold vcgen; intros. destruct H as (V1 & V2).
  eapply triple_consequence. eapply vcg_sound; eauto. auto. red; auto.
Qed.

(** Application: la division Euclidienne *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Voici la précondition, l'invariant de boucle, et la postcondition pour
    le programme de division euclidienne par soustraction itérée. *)

Definition Pre (s: store) :=
  s "a" >= 0 /\ s "b" > 0.

Definition Inv (s: store) :=
  s "r" >= 0 /\ s "b" > 0 /\ s "a" = s "b" * s "q" + s "r".

Definition Post (s: store) :=
  s "q" = s "a" / s "b" /\ s "r" = s "a" mod s "b".

(** Voici le programme IMP avec la boucle annotée par [Inv]. *)

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE Inv (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

(** Et voici la preuve de sa correction.  Elle n'applique explicitement aucune
    des règles de la logique de Hoare.  À la place, on applique le théorème
    [vcgen_correct], puis on fait calculer par Coq les conditions de
    vérification.  Il reste une formule de logique usuelle à démontrer,
    en utilisant les tactiques Coq standard. *)

Theorem Euclidean_division_correct:
  {{Pre}} erase Euclidean_division {{Post}}.
Proof.
  apply vcgen_correct. red; cbn.
  unfold aimp, aupdate, aand, afalse, atrue, Pre, Post, Inv; cbn.
  intuition auto.
  (* La précondition implique l'invariant de boucle. *)
  - lia.
  (* L'invariant et la sortie de boucle impliquent la postcondition. *)
  - apply Z.leb_gt in H0. apply Zdiv_unique with (s "r"). lia. auto.
  - apply Z.leb_gt in H0. apply Zmod_unique with (s "q"). lia. auto.
  (* L'invariant de boucle est préservé *)
  - apply Z.leb_le in H0. lia.
  - lia. 
Qed.

(** *** Exercice (1 étoile) *)
(** Refaire la vérification en supprimant l'hypothèse [s "b" > 0] de
    la précondition et de l'invariant.  Comment est-il possible que
    la vérification "passe" même quand le diviseur [b] est nul? *)

(** *** Exercice (3 étoiles) *)
(** Spécifier et vérifier le programme suivant.  Il calcule dans [r]
    la racine carrée entière de [a].
<<
    r := 0; s := 1;
    while s <= a do (r := r + 1; s := s + r + r + 1)
>>
*)

(** *** Exercice (3 étoiles) *)
(** Spécifier et vérifier le programme suivant.  Il met dans [r]
    la partie entière de la racine carrée de [a].
<<
    r := 0; s := 1;
    while s <= a do
        r := r + 1; s := s + r + r + 1
    done
>>
*)

End VCGEN.
