From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.
From CDF Require Import Sequences IMP Simulation.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 2. Compilation de IMP vers une machine à pile *)

(** ** 2.1.  Le langage cible: une machine à pile *)

(** Notre compilateur traduit IMP en le langage d'une machine très simple
    qui manipule une pile de nombres avec des instructions qui dépilent
    leurs arguments et empilent leur résultat.
    Cette machine ressemble aux anciennes calculatrices HP et leur
    "notation polonaise inversée".  Elle est aussi proche d'un
    sous-ensemble de la JVM, la machine virtuelle Java.
*)

(** *** 2.1.1.  Le jeu d'instructions *)

(** Voici le jeu d'instructions de la machine: *)

Inductive instr : Type :=
  | Iconst (n: Z)           (**r empile l'entier [n] *)
  | Ivar (x: ident)         (**r empile la valeur courante de la variable [x] *)
  | Isetvar (x: ident)      (**r dépile un entier, affecte-le à la variable [x] *)
  | Iadd                    (**r dépile deux entiers, empile leur somme *)
  | Iopp                    (**r dépile un entier, empile son opposé *)
  | Ibranch (d: Z)          (**r saute [d] instructions vers l'avant ou l'arrière *)
  | Ibeq (d1: Z) (d0: Z)    (**r dépile deux entiers, saute [d1] instructions si égaux, [d0] si différents *)
  | Ible (d1: Z) (d0: Z)    (**r dépile deux entiers, saute [d1] instructions si [<=], [d0] si [>] *)
  | Ihalt.                  (**r arrête l'exécution *)

(** Un code machine est une liste d'instructions. *)

Definition code := list instr.

(** La longueur (nombre d'instructions) d'un code machine. *)

Definition codelen (c: code) : Z := Z.of_nat (List.length c).

(** *** 2.1.2.  Sémantique opérationnelle *)

(** La machine opère sur un code [C] (une liste fixée d'instructions)
    et trois composants qui varient pendant l'exécution:
- un pointeur de code [pc], indiquant une position dans [C]
- une pile d'évaluation, contenant des nombres entiers
- un état mémoire, associant à chaque variable sa valeur entière.
*)

Definition stack : Type := list Z.

Definition config : Type := (Z * stack * store)%type.

(** [instr_at C pc = Some i] si [i] est l'instruction à la position
    [pc] dans le code [C]. *)

Fixpoint instr_at (C: code) (pc: Z) : option instr :=
  match C with
  | nil => None
  | i :: C' => if pc =? 0 then Some i else instr_at C' (pc - 1)
  end.

(** La sémantique de la machine est définie en style opérationnel "à petits pas"
    par une relation de transition.  Chaque transition représente l'exécution
    d'une instruction, à savoir, l'instruction à la position [pc] du code [C].
    La relation de transition relie les configurations de la machine
    "avant" et "après" l'exécution de l'instruction.  
    La relation est paramétrée par le code [C] pour le programme complet.
    Il y a un cas pour chaque type d'instruction, sauf [Ihalt], qui
    ne fait pas de transition.
*)

Inductive transition (C: code): config -> config -> Prop :=
  | trans_const: forall pc σ s n,
      instr_at C pc = Some(Iconst n) ->
      transition C (pc    , σ     , s) 
                   (pc + 1, n :: σ, s)
  | trans_var: forall pc σ s x,
      instr_at C pc = Some(Ivar x) ->
      transition C (pc    , σ       , s)
                   (pc + 1, s x :: σ, s)
  | trans_setvar: forall pc σ s x n,
      instr_at C pc = Some(Isetvar x) ->
      transition C (pc    , n :: σ, s)
                   (pc + 1, σ     , update x n s)
  | trans_add: forall pc σ s n1 n2,
      instr_at C pc = Some(Iadd) ->
      transition C (pc    , n2 :: n1 :: σ , s)
                   (pc + 1, (n1 + n2) :: σ, s)
  | trans_opp: forall pc σ s n,
      instr_at C pc = Some(Iopp) ->
      transition C (pc    , n :: σ    , s)
                   (pc + 1, (- n) :: σ, s)
  | trans_branch: forall pc σ s d pc',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , σ, s)
                   (pc', σ, s)
  | trans_beq: forall pc σ s d1 d0 n1 n2 pc',
      instr_at C pc = Some(Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 =? n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: σ, s)
                   (pc', σ            , s)
  | trans_ble: forall pc σ s d1 d0 n1 n2 pc',
      instr_at C pc = Some(Ible d1 d0) ->
      pc' = pc + 1 + (if n1 <=? n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: σ, s)
                   (pc', σ            , s).

(** Comme nous l'avions fait dans le cas de la sémantique à réduction d'IMP,
    nous définissons l'exécution d'un code machine en termes de suites
    de transitions. *)

Definition transitions (C: code): config -> config -> Prop :=
  star (transition C).

(** L'exécution démarre avec [pc = 0] et une pile vide.
    Elle s'arrête avec succès quand [pc] pointe sur une instruction [Ihalt]
    et la pile est vide. *)

Definition machine_terminates (C: code) (s_init: store) (s_final: store) : Prop :=
  exists pc, transitions C (0, nil, s_init) (pc, nil, s_final)
          /\ instr_at C pc = Some Ihalt.

(** La machine peut aussi diverger ("boucler") en faisant une infinité
    de transitions. *)

Definition machine_diverges (C: code) (s_init: store) : Prop :=
  infseq (transition C) (0, nil, s_init).

(** Enfin, la machine peut se bloquer en erreur après un nombre fini
    de transitions. *)

Definition machine_goes_wrong (C: code) (s_init: store) : Prop :=
  exists pc σ s,
      transitions C (0, nil, s_init) (pc, σ, s)
   /\ irred (transition C) (pc, σ, s)
   /\ (instr_at C pc <> Some Ihalt \/ σ <> nil).

(** *** Exercice (2 étoiles). *)

(** Pour tester l'exécution d'un code machine, il est pratique de définir
    la sémantique de la machine comme une fonction exécutable et non
    plus seulement par une relation.  Nous avons déjà vu cette approche
    dans le cadre du langage IMP avec la fonction [cexec_f].  

    Afin de garantir la terminaison de la fonction d'exécution,
    il faut borner a priori le nombre d'instruction exécutées
    à l'aide d'un paramètre [fuel] de type [nat].  Dès lors, il y a
    trois résultats possibles pour une exécution:
*)

Inductive machine_result : Type :=
  | OK (s: store)    (**r la machine s'arrête sur l'état final donné *)
  | Stuck            (**r la machine rencontre une erreur *)
  | Timeout.         (**r la machine n'a plus de fuel *)

(** Compléter les cas manquants dans la définition ci-dessous. *)

Fixpoint mach_exec (C: code) (fuel: nat)
                   (pc: Z) (σ: stack) (s: store) : machine_result :=
  match fuel with
  | O => Timeout
  | S fuel' =>
      match instr_at C pc, σ with
      | Some Ihalt, nil => OK s
      | Some (Iconst n), σ => mach_exec C fuel' (pc + 1) (n :: σ) s
      (* FILL IN HERE *)
      | _, _ => Stuck
      end
  end.

(** ** 2.2. Le schéma de compilation *)

(** Nous allons maintenant définir la compilation des expressions et des
    commandes IMP vers des morceaux de code machine. *)

(** Le code produit pour une expression arithmétique [a] s'exécute
    en séquence (sans faire de branchements) et laisse la valeur de [a]
    au sommet de la pile.

    C'est la traduction bien connue de la notation algébrique vers 
    la notation polonaise inverse.  La seule subtilité est que la machine
    n'a pas d'instruction de soustraction, et donc, pour calculer [a - b],
    il faut ajouter [a] et l'opposé de [b].
*)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | CONST n => Iconst n :: nil
  | VAR x => Ivar x :: nil
  | PLUS a1 a2  => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iopp :: Iadd :: nil
  end.

(** Exemples de code compilé *)

Eval compute in (compile_aexp (PLUS (CONST 1) (CONST 2))).

(** Résultat: [Iconst 1 :: Iconst 2 :: Iadd :: nil] *)

Eval compute in (compile_aexp (PLUS (VAR "x") (MINUS (VAR "y") (CONST 1)))).

(** Résultat: [Ivar "x" :: Ivar "y" :: Iconst 1 :: Iopp :: Iadd :: Iadd :: nil]. *)

(** Pour une expressions booléenne [b], notre premier réflexe serait
    de produire du code machine qui laisse [1] ou [0] au sommet de la
    pile, suivant que [b] est vraie ou fausse.  Le code produit pour
    les commandes [IFTHENELSE] et [WHILE] effectuerait alors un saut
    [Ibeq] conditionnel sur cette valeur 0/1 de [b].

    Cependant, il est plus simple et plus efficace de traduire l'expression
    booléenne [b] par un code machine qui saute [d1] ou [d0] instructions
    en avant, suivant que [b] est vraie ou fausse.  La valeur 0/1 de [b]
    n'est jamais calculée explicitement, et la pile est inchangée.
*)

Fixpoint compile_bexp (b: bexp) (d1: Z) (d0: Z) : code :=
  match b with
  | TRUE => if d1 =? 0 then nil else Ibranch d1 :: nil
  | FALSE => if d0 =? 0 then nil else Ibranch d0 :: nil
  | EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Ibeq d1 d0 :: nil
  | LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Ible d1 d0 :: nil
  | NOT b1 => compile_bexp b1 d0 d1
  | AND b1 b2 =>
      let code2 := compile_bexp b2 d1 d0 in
      let code1 := compile_bexp b1 0 (codelen code2 + d0) in
      code1 ++ code2
  end.

(** Se reporter aux transparents du cours pour une explication du
    mystérieux déplacement [codelen code2 + d0] dans le cas [AND]. *)

(** Vite des exemples. *)

Eval compute in (compile_bexp (EQUAL (VAR "x") (CONST 1)) 12 34).

(** Résultat: [ Ivar "x" :: Iconst 1 :: Ibeq 12 34 :: nil ]. *)

Eval compute in (compile_bexp (AND (LESSEQUAL (CONST 1) (VAR "x"))
                                   (LESSEQUAL (VAR "x") (CONST 10))) 0 10).

(** Résultat: [ Iconst 1 :: Ivar "x" :: Ible 0 13 ::
                Ivar "x" :: Iconst 10 :: Ible 0 10 :: nil ] *)

Eval compute in (compile_bexp (OR (LESSEQUAL (CONST 1) (VAR "x"))
                                  (LESSEQUAL (VAR "x") (CONST 10))) 0 10).

(** Résultat: [ Iconst 1 :: Ivar "x" :: Ible 3 0 ::
                Ivar "x" :: Iconst 10 :: Ible 0 10 :: nil ] *)

Eval compute in (compile_bexp (NOT (AND TRUE FALSE)) 12 34).

(** Résultat: [ Ibranch 12 :: nil ] *)

(** Pour finir, voici la compilation des commandes.  
    Le code produit pour la commande [c] met à jour l'état mémoire
    (les valeurs des variables) comme prescrit par la sémantique de [c].
    Il ne change pas la pile.

    Là encore, on se reportera aux transparents du cours pour une
    explication des déplacements sur les instructions de branchement.
*)

Fixpoint compile_com (c: com) : code :=
  match c with
  | SKIP =>
      nil
  | ASSIGN x a =>
      compile_aexp a ++ Isetvar x :: nil
  | SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ Ibranch (codelen code_ifnot)
      :: code_ifnot
  | WHILE b body =>
      let code_body := compile_com body in
      let code_test := compile_bexp b 0 (codelen code_body + 1) in
      code_test
      ++ code_body
      ++ Ibranch (- (codelen code_test + codelen code_body + 1)) :: nil
  end.

(** Le code compilé pour un programme complet [p] (une commande)
    est similaire, mais termine proprement sur une instruction [Ihalt]. *)

Definition compile_program (p: com) : code :=
  compile_com p ++ Ihalt :: nil.

(** Exemples de compilation: *)

Eval compute in (compile_program (ASSIGN "x" (PLUS (VAR "x") (CONST 1)))).

(** Résultat: [ Ivar "x" :: Iconst 1 :: Iadd :: Isetvar "x" :: Ihalt :: nil ] *)

Eval compute in (compile_program (WHILE TRUE SKIP)).

(** Résultat: [ Ibranch (-1) :: Ihalt :: nil ]. *)

Eval compute in (compile_program (IFTHENELSE (EQUAL (VAR "x") (CONST 1)) (ASSIGN "x" (CONST 0)) SKIP)).

(** Résultat: [ Ivar "x" :: Iconst 1 :: Ibeq 0 3 ::
                 Iconst 0 :: Isetvar "x" :: Ibranch 0 :: Ihalt :: nil ]. *)

(** *** Exercice (1 étoile) *)

(** Le dernier exemple ci-dessus montre une inefficacité mineure dans le code
    engendré pour [IFTHENELSE b c SKIP], à savoir l'instruction [Ibranch 0].
    Pouvez-vous modifier [compile_com] pour éviter cette inefficacité?
    Indication: la fonction ci-dessous vous sera utile. *)

Definition smart_Ibranch (d: Z) : code :=
  if d =? 0 then nil else Ibranch d :: nil.

(** ** 2.3.  Correction du code produit pour les expressions *)

(** Pour raisonner sur les étapes d'exécution du code compilé, il faut
    considérer des morceaux de code machine [C2] qui sont à la position [pc]
    dans le code produit pour le programme tout entier, [C = C1 ++ C2 ++ C3].
    Le prédicat [code_at C pc C2] ci-dessous décrit exactement cette situation. *)

Inductive code_at: code -> Z -> code -> Prop :=
  | code_at_intro: forall C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2.

(** Voici des lemmes utiles concernant les prédicats [instr_at] et [code_at]. *)

Lemma codelen_cons:
  forall i c, codelen (i :: c) = codelen c + 1.
Proof.
  unfold codelen; intros; cbn; lia.
Qed.

Lemma codelen_app:
  forall c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2.
Proof.
  induction c1; intros. 
- auto.
- cbn [app]. rewrite ! codelen_cons. rewrite IHc1. lia.
Qed.

Lemma instr_at_app:
  forall i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc.
- auto.
- assert (A: codelen (a :: c1) =? 0 = false). 
  { apply Z.eqb_neq. unfold codelen. cbn [length]. lia. }
  rewrite A. rewrite codelen_cons. apply IHc1. lia.
Qed.

Lemma code_at_head:
  forall C pc i C',
  code_at C pc (i :: C') ->
  instr_at C pc = Some i.
Proof.
  intros. inversion H. simpl. apply instr_at_app. auto.
Qed.

Lemma code_at_tail:
  forall C pc i C',
  code_at C pc (i :: C') ->
  code_at C (pc + 1) C'.
Proof.
  intros. inversion H. 
  change (C1 ++ (i :: C') ++ C3)
    with (C1 ++ (i :: nil) ++ C' ++ C3).
  rewrite <- app_ass. constructor. rewrite codelen_app. subst pc. auto.
Qed. 

Lemma code_at_app_left:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1.
Proof.
  intros. inversion H. rewrite app_ass. constructor. auto.
Qed.

Lemma code_at_app_right:
  forall C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2.
Proof.
  intros. inversion H. rewrite app_ass. rewrite <- app_ass.
  constructor. rewrite codelen_app. subst pc. auto.
Qed.

Lemma code_at_app_right2:
  forall C pc C1 C2 C3,
  code_at C pc (C1 ++ C2 ++ C3) ->
  code_at C (pc + codelen C1) C2.
Proof.
  intros. apply code_at_app_right. apply code_at_app_left with (C2 := C3).
  rewrite app_ass; auto. 
Qed.

Lemma code_at_nil:
  forall C pc C1,
  code_at C pc C1 -> code_at C pc nil.
Proof.
  intros. inversion H. subst. change (C1 ++ C3) with (nil ++ C1 ++ C3).
  constructor. auto.
Qed.

Lemma instr_at_code_at_nil:
  forall C pc i, instr_at C pc = Some i -> code_at C pc nil.
Proof.
  induction C; cbn; intros.
- discriminate.
- destruct (pc =? 0) eqn:PC.
+ assert (pc = 0) by (apply Z.eqb_eq; auto). subst pc. 
  change (a :: C) with (nil ++ nil ++ (a :: C)). constructor. auto.
+ assert (A: code_at C (pc - 1) nil) by eauto.
  inversion A; subst.
  apply code_at_intro with (C1 := a :: C1) (C3 := C3).
  rewrite codelen_cons. lia.
Qed.

(** Nous mettons ces lemmes dans une "base d'indices" ("hint database")
    afin que Coq puisse les utiliser automatiquement. *)

Hint Resolve code_at_head code_at_tail code_at_app_left code_at_app_right
             code_at_app_right2 code_at_nil instr_at_code_at_nil: code.
Hint Rewrite codelen_app codelen_cons Z.add_assoc Z.add_0_r : code.

(** Rappelons le contrat que nous avons donné pour le code
    compilé pour une expression arithmétique [a].  Il est censé
  - s'exécuter en séquence (pas de branchements)
  - laisser la valeur de [a] au sommet de la pile
  - préserver l'état mémoire.

    Démontrons que le code [compile_aexp a] respecte ce contrat.
    La démonstration est une jolie récurrence sur la forme de [a]. *)

Lemma compile_aexp_correct:
  forall C s a pc σ,
  code_at C pc (compile_aexp a) ->
  transitions C
       (pc, σ, s)
       (pc + codelen (compile_aexp a), aeval a s :: σ, s).
Proof.
  induction a; simpl; intros.

- (* CONST *)
  apply star_one. apply trans_const. eauto with code. 

- (* VAR *)
  apply star_one. apply trans_var. eauto with code. 

- (* PLUS *)
  eapply star_trans. apply IHa1. eauto with code.
  eapply star_trans. apply IHa2. eauto with code.
  apply star_one. autorewrite with code. apply trans_add. eauto with code.

- (* MINUS *)
  eapply star_trans. apply IHa1. eauto with code.
  eapply star_trans. apply IHa2. eauto with code.
  eapply star_trans.
  apply star_one. apply trans_opp. eauto with code.
  apply star_one.
  replace (aeval a1 s - aeval a2 s) 
     with (aeval a1 s + (- aeval a2 s))
       by lia.
  autorewrite with code. apply trans_add. eauto with code.
Qed.

(** La vérification de la compilation des expressions booléennes est similaire.
    On rappelle le contrat pour le code produit par [compile_bexp b d1 d0]:
  - il doit sauter [d1] instructions si [b] s'évalue à vrai,
    [d0] instruction si [b] s'évalue à faux;
  - il doit préserver la pile et l'état mémoire.
*)

Lemma compile_bexp_correct:
  forall C s b d1 d0 pc σ,
  code_at C pc (compile_bexp b d1 d0) ->
  transitions C
       (pc, σ, s)
       (pc + codelen (compile_bexp b d1 d0) + (if beval b s then d1 else d0), σ, s).
Proof.
  induction b; cbn; intros.

- (* TRUE *)
  destruct (d1 =? 0) eqn:Z.
  + (* déplacement = zéro: aucune instruction n'est produite *)
    assert (d1 = 0) by (apply Z.eqb_eq; auto). subst d1.
    autorewrite with code. apply star_refl.
  + (* un branchement est produit *)
    apply star_one. apply trans_branch with (d := d1). eauto with code. auto.

- (* FALSE *)
  destruct (d0 =? 0) eqn:Z.
  + (* déplacement = zéro: aucune instruction n'est produite *)
    assert (d0 = 0) by (apply Z.eqb_eq; auto). subst d0.
    autorewrite with code. apply star_refl.
  + (* un branchement est produit *)
    apply star_one. apply trans_branch with (d := d0). eauto with code. auto.

- (* EQUAL *)
  eapply star_trans. apply compile_aexp_correct with (a := a1). eauto with code.
  eapply star_trans. apply compile_aexp_correct with (a := a2). eauto with code.
  apply star_one. apply trans_beq with (d1 := d1) (d0 := d0). eauto with code.
  autorewrite with code. auto.

- (* LESSEQUAL *)
  eapply star_trans. apply compile_aexp_correct with (a := a1). eauto with code.
  eapply star_trans. apply compile_aexp_correct with (a := a2). eauto with code.
  apply star_one. apply trans_ble with (d1 := d1) (d0 := d0). eauto with code.
  autorewrite with code. auto.

- (* NOT *)
  replace (if negb (beval b s) then d1 else d0)
     with (if beval b s then d0 else d1).
  apply IHb. auto. 
  destruct (beval b s); auto.

- (* AND *)
  set (code2 := compile_bexp b2 d1 d0) in *.
  set (code1 := compile_bexp b1 0 (codelen code2 + d0)) in *.
  eapply star_trans. apply IHb1. eauto with code.
  fold code1. destruct (beval b1 s); cbn.
  + (* b1 s'évalue en true, le code pour b2 est exécuté *)
    autorewrite with code. apply IHb2. eauto with code.
  + (* b1 s'évalue en false, le code pour b2 est sauté *)
    autorewrite with code. apply star_refl.
Qed.

(** ** 2.4.  Correction du code produit pour les commandes qui terminent *)

(** Supposons que la commande [c], démarrée dans l'état [s], termine dans
    l'état [s'].  Montrons alors que la machine, à partir du début du
    code [compile_com c] produit pour [c] et à partir de l'état [s],
    effectue un nombre fini de transitions et atteint la fin du code
    [compile_com c] et l'état [s'].

    Pour caractériser la terminaison de la commande [c], nous utilisons
    la sémantique naturelle d'IMP et son prédicat [exec s c s'].
    La démonstration se fait sans peine par récurrence sur la dérivation
    de cette exécution [exec s c s'].  Une récurrence sur la structure 
    de [c] ne suffirait pas pour gérer le cas des boucles.
*)

Lemma compile_com_correct_terminating:
  forall s c s',
  cexec s c s' ->
  forall C pc σ,
  code_at C pc (compile_com c) ->
  transitions C
      (pc, σ, s)
      (pc + codelen (compile_com c), σ, s').
Proof.
  induction 1; cbn; intros.

- (* SKIP *)
  autorewrite with code. apply star_refl.

- (* ASSIGN *)
  eapply star_trans. apply compile_aexp_correct with (a := a). eauto with code. 
  apply star_one. autorewrite with code. apply trans_setvar. eauto with code.

- (* SEQUENCE *) 
  eapply star_trans.
  apply IHcexec1. eauto with code.
  autorewrite with code. apply IHcexec2. eauto with code.

- (* IFTHENELSE *)
  set (code1 := compile_com c1) in *.
  set (code2 := compile_com c2) in *.
  set (codeb := compile_bexp b 0 (codelen code1 + 1)) in *.
  eapply star_trans.
  apply compile_bexp_correct with (b := b). eauto with code.
  fold codeb. destruct (beval b s); autorewrite with code.
  + (* la branche "then" est exécutée *)
    eapply star_trans. apply IHcexec. eauto with code.
    fold code1. apply star_one. apply trans_branch with (d := codelen code2). eauto with code. lia.
  + (* la branche "else" est exécutée *)
    replace (pc + codelen codeb + codelen code1 + codelen code2 + 1)
       with (pc + codelen codeb + codelen code1 + 1 + codelen code2) by lia.
    apply IHcexec. eauto with code.

- (* WHILE stop *)
  set (code_body := compile_com c) in *.
  set (code_branch := compile_bexp b 0 (codelen code_body + 1)) in *.
  set (d := - (codelen code_branch + codelen code_body + 1)) in *.
  eapply star_trans. apply compile_bexp_correct with (b := b). eauto with code.
  rewrite H. fold code_branch. autorewrite with code. apply star_refl. 

- (* WHILE loop *)
  set (code_body := compile_com c) in *.
  set (code_branch := compile_bexp b 0 (codelen code_body + 1)) in *.
  set (d := - (codelen code_branch + codelen code_body + 1)) in *.
  eapply star_trans. apply compile_bexp_correct with (b := b). eauto with code.
  rewrite H. fold code_branch. autorewrite with code.
  eapply star_trans. apply IHcexec1. eauto with code.
  eapply star_trans.
  apply star_one. apply trans_branch with (d := d). eauto with code. eauto.
  replace (pc + codelen code_branch + codelen code_body + 1 + d)
     with pc
       by lia.
  replace (pc + codelen code_branch + codelen code_body + 1)
     with (pc + codelen (compile_com (WHILE b c)))
       by (cbn; autorewrite with code; auto).
  apply IHcexec2. auto.
Qed.

(** En corollaire, nous obtenons la correction du code compilé pour un
    programme complet [p], dans le cas où il termine. *)

Theorem compile_program_correct_terminating:
  forall s c s',
  cexec s c s' ->
  machine_terminates (compile_program c) s s'.
Proof.
  intros.
  set (C := compile_program c).
  assert (CODEAT: code_at C 0 (compile_com c ++ Ihalt :: nil)).
  { replace C with (nil ++ compile_program c ++ nil).
    apply code_at_intro. auto.
    rewrite app_nil_r; auto. }
  unfold machine_terminates.
  exists (0 + codelen (compile_com c)); split.
- apply compile_com_correct_terminating. auto. eauto with code.
- eauto with code.
Qed.

(** *** Exercice (2 étoiles) *)

(** Dans un exercice précédent, vous avez modifié [compile_com] afin
    d'utiliser [smart_Ibranch] au lieu de [Ibranch] et de produire
    du code plus efficace.  Il vous reste à adapter la démonstration
    de [compile_com_correct_terminating] en conséquence.
    Indication: montrer d'abord le lemme ci-dessous. *)

Lemma transitions_smart_Ibranch:
  forall C pc d pc' σ s,
  code_at C pc (smart_Ibranch d) ->
  pc' = pc + codelen (smart_Ibranch d) + d ->
  transitions C (pc, σ, s) (pc', σ, s).
Proof.
  unfold smart_Ibranch; intros.
  (* À COMPLÉTER *)
Abort.

(** *** Exercice (4 étoiles) *)

(** Le déroulage de boucle consiste à exécuter plusieurs itérations
    de la boucle avant de revenir au début par un saut arrière.
    Par exemple, la boucle [WHILE b c] déroulée deux fois produit le
    pseudo-code machine
<<
  Lloop:
    if b then skip else goto Lexit
    c
    if b then skip else goto Lexit
    c
    goto Lloop
  Lexit:
>>
    Le nombre de tests [if b] exécutés est le même que sans déroulement,
    mais le nombre de sauts en arrière [goto Lloop] est divisé par 2.
    De plus, le déroulage permet souvent d'appliquer davantage d'optimisations 
    dans le corps de la boucle.

    Dans cet exercice, on va dérouler deux fois toutes les boucles
    [WHILE] en remplaçant le cas [WHILE] de la fonction [compile_com] par
<<
  | WHILE b body =>
      let code_body := compile_com body in
      let len_body := codelen code_body in
      let code_test2 := compile_bexp b 0 (len_body + 1) in
      let len_test2 := codelen code_test2 in
      let code_test1 := compile_bexp b 0 (len_body + len_test2 + len_body + 1) in
      let len_test1 := codelen code_test1 in
      code_test1
      ++ code_body
      ++ code_test2
      ++ code_body
      ++ Ibranch (- (len_test1 + len_body + len_test2 + len_body + 1)) :: nil
>>
    Démontrer la correction de ce schéma de compilation en ajustant
    l'énoncé et la démonstration de [compile_com_correct_terminating].

    La difficulté, et la raison pour les 4 étoiles, est que l'hypothèse
    [code_at C pc (compile_com c)] n'est plus vraie si [c] est une boucle
    et nous sommes à la deuxième, quatrième, sixième, etc, itération
    de la boucle.  Il faut inventer une hypothèse plus faible, qui
    laisse plus de flexibilité dans la relation entre [c] et [pc]. *)

(** ** 2.5.  Correction du code produit pour les commandes, cas général *)

(** Nous allons maintenant renforcer le résultat de préservation sémantique
    de la section 2.4 afin qu'il ne soit plus restreint aux programmes IMP
    qui terminent, mais s'applique aussi aux programmes qui divergent.
    Pour ce faire, nous abandonnons la sémantique naturelle des commandes
    et passons à la sémantique par transitions et continuations.
    Ensuite, nous allons montrer un diagramme de simulation qui montre
    que chaque transition dans l'exécution du programme source est
    simulée (en un sens que nous allons définir) par zéro, une ou plusieurs
    transitions de la machine qui exécute le code compilé. *)

(** La première chose à faire est de relier les configurations [(c, k, s)]
    de la sémantique à continuations avec les configurations [(C, pc, σ, s)]
    de la machine.  Nous savons déjà comment relier une commande [c]
    et le code compilé qui lui correspond, à l'aide du prédicat [code_at].
    Il faut maintenant définir une relation entre une continuation [k]
    et le code compilé.

    Intuitivement, lorsque la machine a terminé l'exécution du code
    produit pour la commande [c], c'est-à-dire lorsqu'elle atteint
    le point de programme [pc + codelen(compile_com c)], la machine
    devrait ensuite exécuter des instructions qui effectuent les calculs
    en attente décrits par la continuation [k], pour enfin atteindre
    une instruction [Ihalt] qui arrête la machine.

    Le prédicat inductif [compile_cont C k pc] ci-dessous formalise cette
    intuition.  Il dit que, à partir du pointeur de code [pc],
    il y a dans [C] des instructions qui effectuent les calculs en attente
    décrits dans [k], puis atteignent une instruction [Ihalt].
*)

Inductive compile_cont (C: code): cont -> Z -> Prop :=
  | ccont_stop: forall pc,
      instr_at C pc = Some Ihalt ->
      compile_cont C Kstop pc
  | ccont_seq: forall c k pc pc',
      code_at C pc (compile_com c) ->
      pc' = pc + codelen (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (Kseq c k) pc
  | ccont_while: forall b c k pc d pc' pc'',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      code_at C pc' (compile_com (WHILE b c)) ->
      pc'' = pc' + codelen (compile_com (WHILE b c)) ->
      compile_cont C k pc'' ->
      compile_cont C (Kwhile b c k) pc
  | ccont_branch: forall d k pc pc',
      instr_at C pc = Some(Ibranch d) ->
      pc' = pc + 1 + d ->
      compile_cont C k pc' ->
      compile_cont C k pc.

(** Dès lors, une configuration [(c,k,s)] de la sémantique à continuations
    d'IMP est reliée à une configuration [(C, pc, σ, s')] de la machine
    si les conditions suivantes sont vraies:
    - Les états mémoire sont identiques: [s' = s].
    - La pile de la machine est vide: [σ = nil].
    - Le code machine au point [pc] est le code compilé de [c]:
      [code_at C pc (compile_com c)].
    - Le code machine au point [pc + codelen (compile_com c)] implémente
      la continuation [k], au sens du prédicat [compile_cont] ci-dessus.
*)

Inductive match_config (C: code): com * cont * store -> config -> Prop :=
  | match_config_intro: forall c k st pc,
      code_at C pc (compile_com c) ->
      compile_cont C k (pc + codelen (compile_com c)) ->
      match_config C (c, k, st) (pc, nil, st).

(** Tout est prêt pour démontrer la propriété de simulation attendue.
    Puisque certaines transitions au niveau IMP correspondent à zéro
    transitions de la machine, il nous faut un diagramme de simulation
    de type "étoile" (cf. les transparents).
<<
                      match_config
     c / k / st  ----------------------- machconfig
       |                                   |
       |                                   | + ou ( * et |c',k'| < |c,k} )
       |                                   |
       v                                   v
    c' / k' / st' ----------------------- machconfig'
                      match_config 
>>
    Remarquez la conclusion à droite du diagramme:
    - ou bien la machine effectue une ou plusieurs transitions,
    - ou bien la machine effectue zéro, une ou plusieurs transitions,
      mais la taille de la paire [c,k] décroît strictement.

    Il serait équivalent de montrer que:
    - ou bien la machine effectue une ou plusieurs transitions,
    - ou bien la machine effectue zéro transitions
      mais la taille de la paire [c,k] décroît strictement.

    Il se trouve que la première formulation, avec le cas "zéro une ou
    plusieurs" transitions, est plus facile à démontrer.
*)

(** Trouver la bonne mesure "anti-bégaiement" n'a rien d'évident.
    Après quelques tâtonnements, on tombe sur la mesure suivante.
    Elle est égale à la somme de la taille de la commande [c] en
    cours d'examen et des tailles des commandes apparaissant
    dans les noeuds [Kseq] de la continuation [k]. *)

Fixpoint com_size (c: com) : nat :=
  match c with
  | SKIP => 1%nat
  | ASSIGN x a => 1%nat
  | SEQ c1 c2 => (com_size c1 + com_size c2 + 1)%nat
  | IFTHENELSE b c1 c2 => (com_size c1 + com_size c2 + 1)%nat
  | WHILE b c1 => (com_size c1 + 1)%nat
  end.

Remark com_size_nonzero: forall c, (com_size c > 0)%nat.
Proof.
  induction c; cbn; lia.
Qed.

Fixpoint cont_size (k: cont) : nat :=
  match k with
  | Kstop => 0%nat
  | Kseq c k' => (com_size c + cont_size k')%nat
  | Kwhile b c k' => cont_size k'
  end.

Definition measure (impconf: com * cont * store) : nat :=
  match impconf with (c, k, m) => (com_size c + cont_size k)%nat end.

(** Nous aurons besoin de lemmes d'inversion sur le prédicat [compile_cont]. *)

Lemma compile_cont_Kstop_inv:
  forall C pc s,
  compile_cont C Kstop pc ->
  exists pc',
  star (transition C) (pc, nil, s) (pc', nil, s)
  /\ instr_at C pc' = Some Ihalt.
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_refl. auto.
- destruct IHcompile_cont as (pc'' & A & B); auto.
  exists pc''; split; auto. 
  eapply star_step; eauto. eapply trans_branch; eauto. 
Qed.

Lemma compile_cont_Kseq_inv:
  forall C c k pc s,
  compile_cont C (Kseq c k) pc ->
  exists pc',
  star (transition C) (pc, nil, s) (pc', nil, s)
  /\ code_at C pc' (compile_com c)
  /\ compile_cont C k (pc' + codelen(compile_com c)).
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_refl. split; congruence. 
- edestruct IHcompile_cont as (pc'' & A & B). eauto.
  exists pc''; split; auto.
  eapply star_step; eauto. eapply trans_branch; eauto. 
Qed.

Lemma compile_cont_Kwhile_inv:
  forall C b c k pc s,
  compile_cont C (Kwhile b c k) pc ->
  exists pc',
  plus (transition C) (pc, nil, s) (pc', nil, s)
  /\ code_at C pc' (compile_com (WHILE b c))
  /\ compile_cont C k (pc' + codelen(compile_com (WHILE b c))).
Proof.
  intros. dependent induction H.
- exists (pc + 1 + d); split.
  apply plus_one. eapply trans_branch; eauto. 
  split; congruence.
- edestruct IHcompile_cont as (pc'' & A & B & D). eauto.
  exists pc''; split; auto.
  eapply plus_left. eapply trans_branch; eauto. apply plus_star; auto. 
Qed.

Lemma match_config_skip:
  forall C k s pc,
  compile_cont C k pc ->
  match_config C (SKIP, k, s) (pc, nil, s).
Proof.
  intros. constructor.
- cbn. inversion H; eauto with code.
- cbn. autorewrite with code. auto.
Qed.

(** Voici enfin le diagramme de simulation et sa démonstration. *)

Lemma simulation_step:
  forall C impconf1 impconf2, step impconf1 impconf2 ->
  forall machconf1, match_config C impconf1 machconf1 ->
  exists machconf2,
      (plus (transition C) machconf1 machconf2
       \/ (star (transition C) machconf1 machconf2
           /\ (measure impconf2 < measure impconf1)%nat))
   /\ match_config C impconf2 machconf2.
Proof.
  destruct 1; intros machconf1 MATCH; inversion MATCH; clear MATCH; subst; cbn in *.

- (* assign *)
  econstructor; split.
+ left. eapply plus_right. eapply compile_aexp_correct; eauto with code. 
  eapply trans_setvar; eauto with code.
+ autorewrite with code in *. apply match_config_skip. auto.

- (* seq *)
  econstructor; split.
+ right; split. apply star_refl. lia.
+ autorewrite with code in *. constructor. eauto with code.
  eapply ccont_seq; eauto with code. 

- (* if *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b 0 (codelen code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  autorewrite with code in *.
  econstructor; split.
+ right; split.
  apply compile_bexp_correct with (b := b). eauto with code. 
  destruct (beval b s); lia.
+ fold codeb. destruct (beval b s).
  * autorewrite with code. constructor. eauto with code.
    eapply ccont_branch. eauto with code. eauto. 
    fold code1.
    replace (pc + codelen codeb + codelen code1 + 1 + codelen code2)
       with (pc + codelen codeb + codelen code1 + codelen code2 + 1) by lia.
    auto.
  * autorewrite with code. constructor. eauto with code. auto.
    fold code2.
    replace (pc + codelen codeb + codelen code1 + 1 + codelen code2)
       with (pc + codelen codeb + codelen code1 + codelen code2 + 1) by lia.
    auto.

- (* while stop *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b 0 (codelen codec + 1)) in *.
  econstructor; split.
+ right; split.
  apply compile_bexp_correct with (b := b). eauto with code.
  assert (com_size c > 0)%nat by apply com_size_nonzero. lia.
+ rewrite H. fold codeb. autorewrite with code in *. 
  apply match_config_skip. auto.

- (* while loop *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b 0 (codelen codec + 1)) in *.
  econstructor; split.
+ right; split.
  apply compile_bexp_correct with (b := b). eauto with code.
  lia.
+ rewrite H. fold codeb. autorewrite with code in *. 
  constructor. eauto with code.
  eapply ccont_while with (pc' := pc). eauto with code. fold codec. lia.
  auto.
  cbn. fold codec; fold codeb. eauto. 
  autorewrite with code. auto.

- (* skip seq *)
  autorewrite with code in *.
  edestruct compile_cont_Kseq_inv as (pc' & X & Y & Z). eauto.
  econstructor; split.
+ right; split. eauto. lia.
+ constructor; auto.

- (* skip while *)
  autorewrite with code in *.
  edestruct compile_cont_Kwhile_inv as (pc' & X & Y & Z). eauto.
  econstructor; split.
+ left. eauto.
+ constructor; auto.
Qed.

(** Le plus dur est fait!  De jolies conséquences vont suivre, à l'aide des
    théorèmes généraux sur les simulations fournis par le module [Simulation].

    Tout d'abord, nous obtenons une autre démonstration que les programmes
    qui terminent sont correctement compilés, utilisant la sémantique
    à continuations au lieu de la sémantique naturelle pour caractériser
    les programmes IMP qui terminent. *)

Lemma match_initial_configs:
  forall c s,
  match_config (compile_program c) (c, Kstop, s) (0, nil, s).
Proof.
  intros. set (C := compile_program c).
  assert (code_at C 0 (compile_com c ++ Ihalt :: nil)).
  { replace C with (nil ++ (compile_com c ++ Ihalt :: nil) ++ nil).
    constructor; auto.
    rewrite app_nil_r; auto. }
  constructor. 
- eauto with code.
- apply ccont_stop. eauto with code.
Qed.

Theorem compile_program_correct_terminating_2:
  forall c s s',
  star step (c, Kstop, s) (SKIP, Kstop, s') ->
  machine_terminates (compile_program c) s s'.
Proof.
  intros. set (C := compile_program c).
  edestruct (simulation_star _ _ _ _ _ _ (simulation_step C)) as (ms & A & B).
  eauto. apply match_initial_configs. 
  inversion B; subst. 
  edestruct compile_cont_Kstop_inv as (pc' & D & E). eauto.
  exists pc'; split; auto.
  eapply star_trans. eauto. cbn in D; autorewrite with code in D. eauto.
Qed.

(** Ensuite, et c'est plus nouveau, nous obtenons la preuve que les programmes
    qui divergent sont correctement compilés aussi: si le programme source
    fait une infinité de transitions dans la sémantique d'IMP, la machine
    exécutant le code compilé fait une infinité de transitions aussi. *)

Theorem compile_program_correct_diverging:
  forall c s,
  infseq step (c, Kstop, s) ->
  machine_diverges (compile_program c) s.
Proof.
  intros. set (C := compile_program c).
  eapply (simulation_infseq _ _ _ _ _ _ (simulation_step C)).
  eauto. apply match_initial_configs.
Qed.
