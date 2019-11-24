From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.
From CDF Require Import Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 1. Le langage IMP *)

(** ** 1.1 Expressions arithmétiques *)

Definition ident := string.

(** La syntaxe abstraite: une expression arithmétique est ou bien... *)

Inductive aexp : Type :=
  | CONST (n: Z)                   (**r une constante, ou*)
  | VAR (x: ident)                 (**r une variable, ou *)
  | PLUS (a1: aexp) (a2: aexp)     (**r la somme de deux expressions, ou *)
  | MINUS (a1: aexp) (a2: aexp).   (**r la différence de deux expressions. *)

(** La sémantique dénotationnelle: une fonction d'évaluation qui calcule
  la valeur entière dénotée par une expression.  La fonction est
  paramétrée par un état mémoire [s] qui donne la valeur de chaque variable. *)

Definition store : Type := ident -> Z.

Fixpoint aeval (a: aexp) (s: store) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

(** Ce genre de fonctions d'évaluation / de sémantique dénotationnelle
  ont de nombreux usages.  Tout d'abord, [aeval] permet d'évaluer une
  expression donnée dans un état mémoire donné. *)

Eval compute in (aeval (PLUS (VAR "x") (MINUS (VAR "x") (CONST 1)))  (fun x => 2)).

(** Résultat: [ = 3 : Z ]. *)

(** Nous pouvons aussi faire une évaluation partielle si l'état mémoire est inconnu. *)

Eval cbn in (aeval (PLUS (VAR "x") (MINUS (CONST 10) (CONST 1)))).

(** Résultat: [ = fun s : store => s "x" + 9 ]. *)

(** Nous pouvons démontrer des propriétés mathématiques d'une expression donnée. *)

Lemma aeval_xplus1:
  forall s x, aeval (PLUS (VAR x) (CONST 1)) s > aeval (VAR x) s.
Proof.
  intros. cbn. lia.
Qed.

(** Enfin, nous pouvons démontrer des propriétés "méta" de la sémantique,
  vraies pour toutes les expressions arithmétiques.  Par exemple:
  la valeur d'une expression dépend uniquement des valeurs de ses
  variables libres.

  Les variables libres d'une expression sont définies par le prédicat
  récursif suivant:
*)

Fixpoint free_in_aexp (x: ident) (a: aexp) : Prop :=
  match a with
  | CONST n => False
  | VAR y => y = x
  | PLUS a1 a2 | MINUS a1 a2 => free_in_aexp x a1 \/ free_in_aexp x a2
  end.

Theorem aeval_free:
  forall s1 s2 a,
  (forall x, free_in_aexp x a -> s1 x = s2 x) ->
  aeval a s1 = aeval a s2.
Proof.
  induction a; cbn; intros SAMEFREE.
- (* Cas a = CONST n *)
  auto.
- (* Cas a = VAR x *)
  apply SAMEFREE. auto.
- (* Cas a = PLUS a1 a2 *)
  rewrite IHa1, IHa2; auto.
- (* Case a = MINUS a1 a2 *)
  rewrite IHa1, IHa2; auto.
Qed.

(** Des langages comme Java ou OCaml calculent non pas avec des entiers mathématiques
  en précision arbitraire, mais avec des entiers "machine" pris modulo [2^N].
  Pour refléter cette arithmétique modulaire, il suffit de définir une autre
  fonction d'évaluation qui normalise toutes les valeurs entières par
  réduction modulo [2^N]. *)

Module AExp_modulo.

Definition N := 64.  (**r Exemple d'une machine 64 bits. *)

(** Reduce [x] modulo [2^N] to the range [[-2^(N-1), 2^(N-1) - 1]]. *)

Definition normalize (x: Z) :=
  let y := x mod (2^N) in if y <? 2^(N-1) then y else y - 2^N.

Fixpoint aeval (a: aexp) (s: store) : Z :=
  match a with
  | CONST n => normalize n
  | VAR x => normalize (s x)
  | PLUS a1 a2 => normalize (aeval a1 s + aeval a2 s)
  | MINUS a1 a2 => normalize (aeval a1 s - aeval a2 s)
  end.

Eval compute in (aeval (PLUS (CONST (2^N - 1)) (CONST 1)) (fun _ => 0)).

(** Résultat: [0 : Z]. *)

End AExp_modulo.

(** ** 1.2 Extensions du langage des expressions arithmétiques *)

(** On peut étendre le langage avec de nouvelles opérations de plusieurs
    manières.  La plus simple est via des formes dérivées qui s'expriment
    en termes d'opérateurs existants.  Par exemple, l'opérateur "opposé" est: *)

Definition OPP (a: aexp) : aexp := MINUS (CONST 0) a.

(** Sa sémantique est celle que nous attendions. *)

Lemma aeval_OPP: forall s a, aeval (OPP a) s = - (aeval a s).
Proof.
  intros; cbn. lia.
Qed.

(** Parfois, il faut ajouter des constructeurs au type [aexp]
    et des cas à la fonction [aeval].  Ajoutons par exemple la multiplication. *)

Module AExp_mul.

Inductive aexp : Type :=
  | CONST (n: Z)
  | VAR (x: ident)
  | PLUS (a1: aexp) (a2: aexp)
  | MINUS (a1: aexp) (a2: aexp)
  | TIMES (a1: aexp) (a2: aexp).      (**r NOUVEAU! *)

Fixpoint aeval (a: aexp) (s: store) : Z :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  | TIMES a1 a2 => aeval a1 s * aeval a2 s
  end.

End AExp_mul.

(** Ajoutons aussi la division... *)

Module AExp_div.

Inductive aexp : Type :=
  | CONST (n: Z)
  | VAR (x: ident)
  | PLUS (a1: aexp) (a2: aexp)
  | MINUS (a1: aexp) (a2: aexp)
  | TIMES (a1: aexp) (a2: aexp)
  | QUOT (a1: aexp) (a2: aexp).    (**r NOUVEAU! *)

(** Problème! l'évaluation d'une expression peut maintenant échouer,
  dans le cas d'une division par zéro.  Il faut donc changer le type de [aeval]
  pour refléter cette possibilité d'erreur.  Maintenant, [aeval] renvoie
  un type option [option Z].
  Le résultat [Some n] signifie "pas d'erreur, la valeur est [n]".
  Le résultat [None] signifie "erreur pendant l'évaluation".

  Si nous savons traiter les erreurs, nous pouvons rendre notre sémantique
  plus réaliste sur d'autres aspects du calcul:
  - les variables peuvent être non initialisées; utiliser une telle variable
    dans une expression est une erreur;
  - les opérations arithmétiques peuvent déborder de l'intervalle des
    entiers représentables en machine (p.ex. sur 64 bits); c'est aussi une erreur.
*)

Definition min_int := - (2 ^ 63).  (**r le plus petit entier représentable en machine *)
Definition max_int := 2 ^ 63 - 1.  (**r le plus grand entier représentable en machine *)

Definition machine_integer : Type := { n : Z | min_int <= n <= max_int }.

Program Definition check_for_overflow (n: Z): option machine_integer :=
  if Z_le_dec min_int n
  then if Z_le_dec n max_int then Some n else None
  else None.

Program Fixpoint aeval (s: ident -> option machine_integer) (a: aexp) : option machine_integer :=
  match a with
  | CONST n => check_for_overflow n
  | VAR x => s x
  | PLUS a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => check_for_overflow (n1 + n2)
      | _, _ => None
      end
  | MINUS a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => check_for_overflow (n1 - n2)
      | _, _ => None
      end
  | TIMES a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => check_for_overflow (n1 * n2)
      | _, _ => None
      end
  | QUOT a1 a2 =>
      match aeval s a1, aeval s a2 with
      | Some n1, Some n2 => if n2 =? 0 then None else check_for_overflow (n1 / n2)
      | _, _ => None
      end
  end.

End AExp_div.

(** ** 1.3 Expressions booléennes *)

(** Le langage IMP offre des boucles et des conditionnelles (if/then/else)
    qui utilisent comme conditions des expressions à valeur booléenne (true/false).
    Voici la syntaxe abstraite de ces expressions booléennes. *)

Inductive bexp : Type :=
  | TRUE                              (**r toujours vrai *)
  | FALSE                             (**r toujours faux *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r teste si [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r teste si [a1 <= a2] *)
  | NOT (b1: bexp)                    (**r négation *)
  | AND (b1: bexp) (b2: bexp).        (**r conjonction *)

(** De même que les expressions arithmétiques dénotent des entiers,
    les expressions booléennes dénotent les booléens [true] ou [false]. *)

Fixpoint beval (b: bexp) (s: store) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval a1 s =? aeval a2 s
  | LESSEQUAL a1 a2 => aeval a1 s <=? aeval a2 s
  | NOT b1 => negb (beval b1 s)
  | AND b1 b2 => beval b1 s && beval b2 s
  end.

(** Il y a de nombreuses formes dérivées utiles. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** *** Exercice (1 étoile) *)
(** Prouvez que la forme [OR] a bien la sémantique attendue. *)

Lemma beval_OR:
  forall s b1 b2, beval (OR b1 b2) s = beval b1 s || beval b2 s.
Proof.
  intros; cbn.
  (* Indication: taper "SearchAbout negb" pour voir les lemmes disponibles
     qui portent sur la négation booléenne. *)
  (* Indication: ou faites simplement une analyse de cas sur
     [beval b1 s] et [beval b2 s], il n'y a que 4 cas à considérer. *)
  (* À COMPLÉTER *)
Abort.

(** ** 1.4 Commandes *)

(** Pour finir la définition du langage IMP, voici la syntaxe abstraite
    des commandes, aussi appelés "statements" en Anglais. *)

Inductive com: Type :=
  | SKIP                                     (**r ne rien faire *)
  | ASSIGN (x: ident) (a: aexp)              (**r affectation: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r séquence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditionnelle: [if b then c1 else c2] *)
  | WHILE (b: bexp) (c1: com).               (**r boucle: [while b do c1 done] *)

(** Écrivons [c1 ;; c2] au lieu de [SEQ c1 c2], c'est plus lisible. *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Voici un programme IMP qui effectue la division euclidienne par
    soustractions successives.  À la fin du programme, la variable
    "q" contient le quotient de "a" par "b", et la variable "r"
    contient le reste de la division.  En pseudocode, cela s'écrit:
<<
       r := a; q := 0;
       while b <= r do r := r - b; q := q + 1 done
>>
    En syntaxe abstraite, on écrit:
*)

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

(** Une opération essentielle sur les états mémoire:
    [update x v s] est l'état où [x] vaut [v] et tout autre variable [y]
    vaut ce qu'elle vaut dans [s]. *)

Definition update (x: ident) (v: Z) (s: store) : store :=
  fun y => if string_dec x y then v else s y.

(** Naïvement, nous aimerions définir la sémantique d'une commande
    avec une fonction d'exécution [cexec s c] qui exécute la commande [c]
    dans l'état initial [s] et renvoie l'état final au moment où [c] termine. *)

Fail Fixpoint cexec (c: com) (s: store) : store :=
  match c with
  | SKIP => s
  | ASSIGN x a => update x (aeval a s) s
  | SEQ c1 c2 => let s' := cexec c1 s in cexec c2 s'
  | IFTHENELSE b c1 c2 => if beval b s then cexec c1 s else cexec c2 s
  | WHILE b c1 =>
      if beval b s
      then (let s' := cexec c1 s in cexec (WHILE b c1) s')
      else s
  end.

(** Coq rejette cette définition, à juste titre, car toutes les fonctions Coq
    doivent terminer.  Or, le cas [WHILE] peut boucler!  par exemple
    si nous avons la boucle infinie [WHILE TRUE SKIP].  
    Essayons un tout autre style de sémantique, à base de suites de réductions.
*)

(** ** 1.5 Sémantique à réductions *)

(** La relation [ red (c, s) (c', s') ] représente une réduction élémentaire,
    c'est à dire la première étape de calcul lorsqu'on exécute la commande [c]
    dans l'état mémoire initial [s].
    [s'] est l'état mémoire "après" l'étape de calcul.
    [c'] est une commande qui représente le résidu de la réduction:
    tous les calculs qui restent à faire ensuite.

    La relation de réduction est représentée par un prédicat inductif Coq,
    avec un cas (un "constructeur") pour chaque règle de réduction.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval b s then c1 else c2), s)
  | red_while_done: forall b c s,
      beval b s = false ->
      red (WHILE b c, s) (SKIP, s)
  | red_while_loop: forall b c s,
      beval b s = true ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s).

(** Une propriété intéressante de cette relation de réduction est qu'elle est
    fonctionnelle: une configuration [(c,s)] se réduit en au plus une configuration.
    Cela correspond au fait que le langage IMP est déterministe. *)

Lemma red_determ:
  forall cs cs1, red cs cs1 -> forall cs2, red cs cs2 -> cs1 = cs2.
Proof.
  induction 1; intros cs2 R2; inversion R2; subst; eauto.
- inversion H3.
- inversion H.
- assert (EQ: (c2, s2) = (c4, s3)) by auto. congruence.
- congruence.
- congruence.
Qed.

(** On définit la sémantique d'une commande en itérant les étapes de réduction.
    La commande [c] dans l'état initial [s] termine dans l'état final [s']
    si en un nombre fini de réductions on va de [(c, s)] à [(skip, s')].
*)

Definition terminates (s: store) (c: com) (s': store) : Prop :=
  star red (c, s) (SKIP, s').

(** L'opérateur [star] est défini dans la bibliothèque [Sequences].
    [star R] est la fermeture réflexive transitive d'une relation [R],
    que l'on note souvent [R*] sur papier.  La relation [star red]
    représente donc zéro, une ou plusieurs étapes de réduction. *)

(** De même, la commande [c] diverge (ne termine pas) dans l'état initial [s]
    s'il existe une suite infinie de réductions issue de [(c, s)].
    L'opérateur [infseq] est lui aussi défini dans la bibliothèque [Sequences].
*)

Definition diverges (s: store) (c: com) : Prop :=
  infseq red (c, s).

(** En général, un troisième type d'exécutions est possible: partir en erreur
   ("going wrong") après un nombre fini de réductions.
   Une configuration [(c', s')] est en erreur si elle ne se réduit pas
   et elle n'est pas terminale, c'est à dire [c' <> SKIP]. *)

Definition goes_wrong (s: store) (c: com) : Prop :=
  exists c', exists s',
  star red (c, s) (c', s') /\ irred red (c', s') /\ c' <> SKIP.

(** *** Exercice (2 étoiles) *)
(** Montrer que les commandes Imp ne partent jamais en erreur.
    Indication: commencer par montrer la propriété de "progression" ci-dessous,
    qui dit qu'une commande autre que [SKIP] peut toujours se réduire. *)

Lemma red_progress:
  forall c s, c = SKIP \/ exists c', exists s', red (c, s) (c', s').
Proof.
  induction c; intros.
  (* À COMPLÉTER *)
Abort.

Lemma not_goes_wrong:
  forall c s, ~(goes_wrong s c).
Proof.
  intros c s (c' & s' & STAR & IRRED & NOTSKIP).
  (* À COMPLÉTER *)
Abort.

(** Un lemme technique: les suites de réductions peuvent s'effectuer
   dans la partie gauche d'une séquence.  Cela généralise la règle [red_seq_step]. *)

Lemma red_seq_steps:
  forall c2 s c s' c',
  star red (c, s) (c', s') -> star red ((c;;c2), s) ((c';;c2), s').
Proof.
  intros. dependent induction H.
- apply star_refl.
- destruct b as [c1 st1].
  apply star_step with (c1;;c2, st1). apply red_seq_step. auto. auto.  
Qed.

(** ** 1.6 Sémantique naturelle *)

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
  | cexec_while_done: forall b c s,
      beval b s = false ->
      cexec s (WHILE b c) s
  | cexec_while_loop: forall b c s s' s'',
      beval b s = true -> cexec s c s' -> cexec s' (WHILE b c) s'' ->
      cexec s (WHILE b c) s''.

(** Le prédicat [cexec s c s'] est vrai ssi il existe une dérivation finie
    de cette conclusion au moyen des axiomes et des règles d'inférence ci-dessus.
    La structure de cette dérivation représente les calculs effectués par [c]
    sous forme d'arbre --- et non plus sous forme de suite de réductions.
    La finitude de la dérivation garantit que seules les exécutions qui terminent
    satisfont [cexec].  Et en effet [WHILE TRUE SKIP] ne satisfait pas [cexec]. *)

Lemma cexec_infinite_loop:
  forall s, ~ exists s', cexec s (WHILE TRUE SKIP) s'.
Proof.
  assert (A: forall s c s', cexec s c s' -> c = WHILE TRUE SKIP -> False).
  { induction 1; intros EQ; inversion EQ.
  - subst b c. cbn in H. discriminate.
  - subst b c. apply IHcexec2. auto.
  }
  intros s (s' & EXEC). apply A with (s := s) (c := WHILE TRUE SKIP) (s' := s'); auto.
Qed.

(** Nous allons montrer l'équivalence entre les évaluations qui terminent
    d'après la sémantique naturelle
        (existence d'une dérivation de [cexec s c s'])
    et d'après la sémantique par réductions
        (existence d'une suite de réductions de [(c,s)] vers [(SKIP, s')].

    Commençons par l'implication sémantique naturelle => suite de réductions,
    qui se montre par une jolie récurrence sur la dérivation de [cexec]. *)

Theorem cexec_to_terminates:
  forall s c s', cexec s c s' -> star red (c, s) (SKIP, s').
Proof.
  induction 1.
- (* SKIP *)
  apply star_refl.
- (* ASSIGN *)
  apply star_one. apply red_assign. 
- (* SEQ *)
  eapply star_trans. apply red_seq_steps. apply IHcexec1.
  eapply star_step.  apply red_seq_done.  apply IHcexec2.
- (* IFTHENELSE *)
  eapply star_step. apply red_ifthenelse. auto.
- (* WHILE stop *)
  apply star_one. apply red_while_done. auto.
- (* WHILE loop *)
  eapply star_step. apply red_while_loop. auto.
  eapply star_trans. apply red_seq_steps. apply IHcexec1.
  eapply star_step. apply red_seq_done. apply IHcexec2.
Qed.

(** L'implication réciproque, d'une suite de réductions vers une dérivation
    de [cexec], est plus subtile.  Voici le lemme clé, qui montre comment
    une étape de réduction suivie d'une exécution [cexec] peuvent se
    combiner en une exécution [cexec]. *)

Lemma red_append_cexec:
  forall c1 s1 c2 s2, red (c1, s1) (c2, s2) ->
  forall s', cexec s2 c2 s' -> cexec s1 c1 s'.
Proof.
  intros until s2; intros STEP. dependent induction STEP; intros.
- (* red_assign *)
  inversion H; subst. apply cexec_assign. 
- (* red_seq_done *)
  apply cexec_seq with s2. apply cexec_skip. auto.
- (* red seq step *)
  inversion H; subst. apply cexec_seq with s'0.
  eapply IHSTEP; eauto.
  auto.
- (* red_ifthenelse *)
  apply cexec_ifthenelse. auto.
- (* red_while_done *)
  inversion H0; subst. apply cexec_while_done. auto.
- (* red while loop *)
  inversion H0; subst. apply cexec_while_loop with s'0; auto.
Qed.

(** Il s'ensuit (par récurrence sur la suite de réductions)
    qu'une commande qui se réduit vers [SKIP] s'exécute
    d'après la sémantique naturelle avec le même état final. *)

Theorem reds_to_cexec:
  forall s c s',
  star red (c, s) (SKIP, s') -> cexec s c s'.
Proof.
  intros. dependent induction H.
- apply cexec_skip.
- destruct b as [c1 s1]. apply red_append_cexec with c1 s1; auto.
Qed.

(** ** 1.7 Interpréteur borné *)

(** Il s'est révélé impossible de définir la sémantique des commandes par
    une fonction d'exécution Coq.  Cependant, nous pouvons définir une
    approximation d'une telle fonction, en bornant a priori la profondeur
    de la récursion, à l'aide d'un paramètre supplémentaire [fuel] de type [nat].
    Le "fuel" est décrémenté de 1 à chaque appel récursif.  S'il tombe à zéro,
    l'exécution renvoie [None], ce qui signifie que l'état final à la fin
    de l'exécution de la commande n'a pas pu être calculé: soit la commande
    diverge, soit il faut davantage de "fuel" pour l'exécuter entièrement. *)

Fixpoint cexec_f (fuel: nat) (s: store) (c: com) : option store :=
  match fuel with
  | O => None
  | S fuel' =>
      match c with
      | SKIP => Some s
      | ASSIGN x a => Some (update x (aeval a s) s)
      | SEQ c1 c2 =>
          match cexec_f fuel' s c1 with
          | None  => None
          | Some s' => cexec_f fuel' s' c2
          end
      | IFTHENELSE b c1 c2 =>
          cexec_f fuel' s (if beval b s then c1 else c2)
      | WHILE b c1 =>
          if beval b s then
            match cexec_f fuel' s c1 with
            | None  => None
            | Some s' => cexec_f fuel' s' (WHILE b c1)
            end
          else Some s
      end
  end.

(** Cette fonction approchée est très utile pour calculer la sémantique
    sur des programmes de test.  Par exemple, calculons le quotient et
    le reste de 14 divisé par 3 avec le programme IMP de division euclidienne
    donné ci-dessus. *)

Eval compute in
  (let s := update "a" 14 (update "b" 3 (fun _ => 0)) in
   match cexec_f 100 s Euclidean_division with
   | None => None
   | Some s' => Some (s' "q", s' "r")
   end).

(** *** Exercice (3 étoiles) *)

(** Montrer que la fonction [cexec_f] est correcte vis-à-vis de la sémantique
    naturelle [cexec], en démontrant les deux lemmes suivants. *)

Lemma cexec_f_sound:
  forall fuel s c s', cexec_f fuel s c = Some s' -> cexec s c s'.
Proof.
  induction fuel as [ | fuel ]; cbn; intros.
- discriminate.
- destruct c.
  (* À COMPLÉTER *)
Abort.

Lemma cexec_f_complete:
  forall s c s', cexec s c s' ->
  exists fuel1, forall fuel, (fuel >= fuel1)%nat -> cexec_f fuel s c = Some s'.
Proof.
  induction 1.
  (* À COMPLÉTER *)
Abort.
