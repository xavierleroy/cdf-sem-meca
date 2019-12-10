From Coq Require Import ZArith Psatz Bool String Program.Equality FSets Wellfounded.
From CDF Require Import Sequences IMP Simulation.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 3. Optimisations et analyses statiques *)

(** ** 3.1.  Analyse de vivacité (liveness analysis) *)

(** *** Ensembles finis d'identificateurs *)

(** L'analyse statique que nous allons étudier travaille sur des
    ensembles finis de variables IMP.  La bibliothèque standard de Coq
    fournit une implémentation efficace des ensembles finis et
    démontre de nombreuses propriétés des opérations ensemblistes.
    Afin d'appliquer cette bibliothèque, nous devons lui fournir un
    module Coq qui décrit le type des éléments (les identificateurs
    d'IMP) et l'égalité entre éléments. *)

Module Ident_Decidable <: DecidableType with Definition t := ident.
  Definition t := ident.
  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End Ident_Decidable.

(** Nous pouvons alors instancier les modules d'ensembles finis
    de la bibliothèque standard Coq sur ce type d'éléments. *)

Module IdentSet := FSetWeakList.Make(Ident_Decidable).
Module ISFact := FSetFacts.WFacts(IdentSet).
Module ISProp := FSetProperties.WProperties(IdentSet).
Module ISDecide := FSetDecide.Decide(IdentSet).
Import ISDecide.

(** *** Variables libres *)

(** L'ensemble des variables mentionnées dans une expression. *)

Fixpoint fv_aexp (a: aexp) : IdentSet.t :=
  match a with
  | CONST n => IdentSet.empty
  | VAR v => IdentSet.singleton v
  | PLUS a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  | MINUS a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  end.

Fixpoint fv_bexp (b: bexp) : IdentSet.t :=
  match b with
  | TRUE => IdentSet.empty
  | FALSE => IdentSet.empty
  | EQUAL a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  | LESSEQUAL a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  | NOT b1 => fv_bexp b1
  | AND b1 b2 => IdentSet.union (fv_bexp b1) (fv_bexp b2)
  end.

(** L'ensemble des variables utilisées par une commande. *)

Fixpoint fv_com (c: com) : IdentSet.t :=
  match c with
  | SKIP => IdentSet.empty
  | ASSIGN x a => fv_aexp a
  | SEQ c1 c2 => IdentSet.union (fv_com c1) (fv_com c2)
  | IFTHENELSE b c1 c2 => IdentSet.union (fv_bexp b) (IdentSet.union (fv_com c1) (fv_com c2))
  | WHILE b c => IdentSet.union (fv_bexp b) (fv_com c)
  end.

(** *** Calcul de post-points fixes *)

Section FIXPOINT.

Variable F: IdentSet.t -> IdentSet.t.
Variable default: IdentSet.t.

(** Notre but est de calculer un ensemble de variables [x] tel que
    [F x] est un sous-ensemble de [x].  C'est ce qu'on appelle un
    post-point fixe de [F].

    Nous utilisons un algorithme naïf d'itération bornée:
    on itère [F] au plus [n] fois à partir de l'ensemble vide,
    en s'arrêtant dès qu'un post-point fixe est atteint.  
    Après [n] itérations infructueuse, on renvoie un résultat par défaut. *)

Fixpoint iter (n: nat) (x: IdentSet.t) : IdentSet.t :=
  match n with
  | O => default
  | S n' =>
      let x' := F x in
      if IdentSet.subset x' x then x else iter n' x'
  end.

Definition niter := 10%nat.

Definition postfixpoint : IdentSet.t := iter niter IdentSet.empty.

Lemma postfixpoint_charact:
  IdentSet.Subset (F postfixpoint) postfixpoint \/ postfixpoint = default.
Proof.
  unfold postfixpoint. generalize niter, IdentSet.empty. induction n; intros; cbn.
- auto.
- destruct (IdentSet.subset (F t) t) eqn:SUBSET.
+ left. apply IdentSet.subset_2; auto.
+ apply IHn. 
Qed.

Hypothesis F_stable:
  forall x, IdentSet.Subset x default -> IdentSet.Subset (F x) default.

Lemma postfixpoint_upper_bound:
  IdentSet.Subset postfixpoint default.
Proof.
  assert (REC: forall n x, IdentSet.Subset x default -> IdentSet.Subset (iter n x) default).
  { induction n; intros; cbn.
  - fsetdec.
  - destruct (IdentSet.subset (F x) x); auto.
  }
  apply REC. fsetdec.
Qed.

End FIXPOINT.

(** *** L'analyse de vivacité *)

(** [L] est l'ensemble des variables vivantes "après" la commande [c].
    Le résultat de [live c L] est l'ensemble des variables vivantes "avant" [c]. *)

Fixpoint live (c: com) (L: IdentSet.t) : IdentSet.t :=
  match c with
  | SKIP => L
  | ASSIGN x a =>
      if IdentSet.mem x L
      then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
      else L
  | SEQ c1 c2 =>
      live c1 (live c2 L)
  | IFTHENELSE b c1 c2 =>
      IdentSet.union (fv_bexp b) (IdentSet.union (live c1 L) (live c2 L))
  | WHILE b c =>
      let L' := IdentSet.union (fv_bexp b) L in
      let default := IdentSet.union (fv_com (WHILE b c)) L in
      postfixpoint (fun x => IdentSet.union L' (live c x)) default
  end.

(** Une borne supérieure pour les variables vivantes "avant" est les
    variables vivantes "après" plus toutes les variables utilisées
    dans la commande [c]. *)

Lemma live_upper_bound:
  forall c L,
  IdentSet.Subset (live c L) (IdentSet.union (fv_com c) L).
Proof.
  induction c; intros; simpl.
- fsetdec.
- destruct (IdentSet.mem x L) eqn:MEM; fsetdec. 
- specialize (IHc1 (live c2 L)). specialize (IHc2 L). fsetdec.
- specialize (IHc1 L). specialize (IHc2 L). fsetdec.
- apply postfixpoint_upper_bound. intros x. specialize (IHc x). fsetdec.
Qed.

(** Les variables vivantes à l'entrée d'une boucle vérifient 
    les trois conditions suivantes. *)

Lemma live_while_charact:
  forall b c L,
  let L' := live (WHILE b c) L in
  IdentSet.Subset (fv_bexp b) L'
  /\ IdentSet.Subset L L'
  /\ IdentSet.Subset (live c L') L'.
Proof.
  intros.
  generalize (postfixpoint_charact
    (fun x : IdentSet.t => IdentSet.union (IdentSet.union (fv_bexp b) L) (live c x))
          (IdentSet.union (IdentSet.union (fv_bexp b) (fv_com c)) L)).
  simpl in L'. fold L'. intros [A|A].
- split. fsetdec. split; fsetdec. 
- rewrite A. split. fsetdec. split. fsetdec. 
  eapply ISProp.subset_trans. apply live_upper_bound. fsetdec.
Qed.

(** ** 3.2.  Une optimisation: l'élimination de code mort *)

(** *** La transformation de programme *)

(** L'élimination de code mort, aussi appelée DCE (Dead Code Elimination),
    remplace les affectations [x := a] à des variables mortes en
    instructions [SKIP]. *)

Fixpoint dce (c: com) (L: IdentSet.t): com :=
  match c with
  | SKIP => SKIP
  | ASSIGN x a => if IdentSet.mem x L then ASSIGN x a else SKIP
  | SEQ c1 c2 => SEQ (dce c1 (live c2 L)) (dce c2 L)
  | IFTHENELSE b c1 c2 => IFTHENELSE b (dce c1 L) (dce c2 L)
  | WHILE b c => WHILE b (dce c (live (WHILE b c) L))
  end.

(** Exemples d'optimisation. *)

Print Euclidean_division.

Eval compute in (dce Euclidean_division (IdentSet.singleton "r")).

(** Effet de la transformation:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b <= r do                while b <= r do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

Eval compute in (dce Euclidean_division (IdentSet.singleton "q")).

(** Le programme est inchangé. *)

(** *** Préservation de la sémantique *)

(** Deux états mémoires concordent sur un ensemble [L] de variables vivantes
    s'ils associent les mêmes valeurs à chaque variable vivante. *)

Definition agree (L: IdentSet.t) (s1 s2: store) : Prop :=
  forall x, IdentSet.In x L -> s1 x = s2 x.

(** Cette définition est monotone par-rapport à l'ensemble [L]. *)

Lemma agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> IdentSet.Subset L L' -> agree L s1 s2.
Proof.
  unfold IdentSet.Subset, agree; intros. auto.
Qed.

(** Si deux états mémoire concordent sur les variables libres d'une
    expression, cette expression s'évalue à la même valeur dans les
    deux états. *)

Lemma aeval_agree:
  forall a s1 s2, agree (fv_aexp a) s1 s2 -> aeval a s1 = aeval a s2.
Proof.
  induction a; cbn; intros.
- auto.
- apply H. fsetdec. 
- f_equal; [apply IHa1 | apply IHa2]; eapply agree_mon; eauto; fsetdec.
- f_equal; [apply IHa1 | apply IHa2]; eapply agree_mon; eauto; fsetdec.
Qed.

Lemma beval_agree:
  forall b s1 s2, agree (fv_bexp b) s1 s2 -> beval b s1 = beval b s2.
Proof.
  induction b; cbn; intros.
- auto.
- auto.
- f_equal; eapply aeval_agree; eapply agree_mon; eauto; fsetdec.
- f_equal; eapply aeval_agree; eapply agree_mon; eauto; fsetdec.
- f_equal; apply IHb; auto.
- f_equal; [apply IHb1 | apply IHb2]; eapply agree_mon; eauto; fsetdec.
Qed.

(** La relation [agree] est préservée par affectation parallèle 
    à une variable vivante (la même valeur est affectée à la variable
    dans les deux états). *)

Lemma agree_update_live:
  forall s1 s2 L x v,
  agree (IdentSet.remove x L) s1 s2 ->
  agree L (update x v s1) (update x v s2).
Proof.
  unfold agree, update; intros. destruct (string_dec x x0).
- auto.
- apply H. fsetdec.
Qed.

(** La relation [agree] est préservée par affectation d'un seul côté
    à une variable morte. *)

Lemma agree_update_dead:
  forall s1 s2 L x v,
  agree L s1 s2 -> ~IdentSet.In x L ->
  agree L (update x v s1) s2.
Proof.
  unfold agree, update; intros. destruct (string_dec x x0).
- subst x0. contradiction.
- apply H. fsetdec.
Qed.

(** Nous démontrons maintenant que l'élimination de code mort préserve
    la sémantique des programmes qui terminent.  Nous utilisons la
    sémantique naturelle d'IMP pour montrer le diagramme suivant:
<<
               agree (live c L) s s1
     c / s ----------------------------- dce C L / s1
       |                                         |
       |                                         |
       |                                         |
       v                                         v
      s' -------------------------------------- s1'
                    agree L s' s1'
>>
  La démonstration est une récurrence sur la dérivation de l'exécution de [c].
*)

Theorem dce_correct_terminating:
  forall s c s', cexec s c s' ->
  forall L s1,
  agree (live c L) s s1 ->
  exists s1', cexec s1 (dce c L) s1' /\ agree L s' s1'.
Proof.
  induction 1; intros L s1 AG.
- (* SKIP *)
  exists s1; split. constructor. auto.
- (* ASSIGN *)
  cbn in *. destruct (IdentSet.mem x L) eqn:is_live.
  + (* x est vivante après *)
    assert (EVAL: aeval a s = aeval a s1) by (eapply aeval_agree; eapply agree_mon; eauto; fsetdec).
    econstructor; split.
    apply cexec_assign.
    rewrite EVAL. apply agree_update_live. eapply agree_mon; eauto. fsetdec.
  + (* x est morte après *)
    econstructor; split.
    apply cexec_skip.
    apply agree_update_dead. auto.
    red; intros. assert (IdentSet.mem x L = true) by (apply IdentSet.mem_1; auto). congruence.
- (* SEQ *)
  cbn in *.
  destruct (IHcexec1 _ _ AG) as (s1' & EXEC1 & AG1).
  destruct (IHcexec2 _ _ AG1) as (s2' & EXEC2 & AG2).
  exists s2'; split.
  apply cexec_seq with s1'; auto.
  auto.
- (* IFTHENELSE *)
  cbn in *.
  assert (EVAL: beval b s = beval b s1) by (eapply beval_agree; eapply agree_mon; eauto; fsetdec).
  destruct (IHcexec L s1) as (s1' & EXEC' & AG').
  eapply agree_mon; eauto. destruct (beval b s); fsetdec.
  exists s1'; split.
  apply cexec_ifthenelse. rewrite <- EVAL. destruct (beval b s); auto.
  auto.
- (* WHILE done *)
  change (dce (WHILE b c) L) with (WHILE b (dce c (live (WHILE b c) L))).
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval b s1) by (eapply beval_agree; eapply agree_mon; eauto; fsetdec).
  exists s1; split.
  apply cexec_while_done. congruence.
  eapply agree_mon; eauto.
- (* WHILE loop *)
  change (dce (WHILE b c) L) with (WHILE b (dce c (live (WHILE b c) L))).
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval b s1) by (eapply beval_agree; eapply agree_mon; eauto; fsetdec).
  destruct (IHcexec1 (live (WHILE b c) L) s1) as (s1' & EXEC1 & AG1).
  eapply agree_mon; eauto.
  destruct (IHcexec2 L s1') as (s2' & EXEC2 & AG2).
  auto.
  exists s2'; split.
  apply cexec_while_loop with s1'; auto. congruence.
  auto.
Qed.

(** **** Exercice (3 étoiles) *)

(** On peut montrer la préservation sémantique pour tous les
    programmes, qu'ils terminent ou non, avec un diagramme de
    simulation utilisant la sémantique à réductions d'IMP.
    Complétez la démonstration du diagramme ci-dessous. *)

Fixpoint measure (c: com) : nat :=
  match c with
  | ASSIGN x a => 1
  | SEQ c1 c2 => measure c1
  | _ => 0
  end.

Theorem dce_simulation:
  forall c s c' s',
  red (c, s) (c', s') ->
  forall L s1,
  agree (live c L) s s1 ->
  (exists s1', red (dce c L, s1) (dce c' L, s1') /\ agree (live c' L) s' s1')
  \/
  ((measure c' < measure c)%nat /\ dce c L = dce c' L /\ agree (live c' L) s' s1).
Proof.
  intros until s'; intros STEP. dependent induction STEP; intros.
  (* A COMPLETER *)
Abort.


(** ** 3.3. L'allocation de registres *)

(** Dans un "vrai" compilateur, la phase d'allocation de registres
    consiste à placer les variables du programme les plus utilisées
    dans des registres du processeur (disponibles en petit nombre), les
    autres variables étant stockées dans la mémoire, dans des
    emplacements de pile. *)

(** Pour étudier l'allocation de registres au niveau du langage IMP,
    nous allons la voir comme un renommage des variables du programme
    IMP qui vise à réduire le nombre de variables différentes
    utilisées.  En effet, le renommage n'est pas nécessairement
    injectif: deux variables qui ne sont jamais utilisées en même temps
    peuvent être fusionnées. *)

(** Calculer un bon renommage est un problème algorithmiquement
    difficile, équivalent au coloriage d'un graphe.  Nous allons
    supposer qu'une heuristique extérieure nous donne un renommage,
    appelé [f] ci-dessous, et donner des conditions suffisantes et
    facilement vérifiables pour que le [f] soit correct et préserve la
    sémantique. *)

Section RENAMING.

Variable f: ident -> ident.   (**r le renommage proposé *)

(** *** Renommage des variables dans une expression *)

Fixpoint rename_aexp (a: aexp) : aexp :=
  match a with
  | CONST n => CONST n
  | VAR x => VAR (f x)
  | PLUS a1 a2 => PLUS (rename_aexp a1) (rename_aexp a2)
  | MINUS a1 a2 => MINUS (rename_aexp a1) (rename_aexp a2)
  end.

Fixpoint rename_bexp (b: bexp) : bexp :=
  match b with
  | TRUE => TRUE
  | FALSE => FALSE
  | EQUAL a1 a2 => EQUAL (rename_aexp a1) (rename_aexp a2)
  | LESSEQUAL a1 a2 => LESSEQUAL (rename_aexp a1) (rename_aexp a2)
  | NOT b1 => NOT (rename_bexp b1)
  | AND b1 b2 => AND (rename_bexp b1) (rename_bexp b2)
  end.

(** *** Reconnaissance des expressions qui sont des variables *)

Definition expr_is_var (a: aexp): option ident :=
  match a with VAR x => Some x | _ => None end.

Lemma expr_is_var_correct:
  forall a x, expr_is_var a = Some x -> a = VAR x.
Proof.
  unfold expr_is_var; intros. destruct a; congruence.
Qed.

(** *** Transformation des commandes *)

(** La transformation renomme les variables comme prescrit par [f].
    De plus, elle élimine le code mort comme précédemment, ainsi que
    les affectations [x := y] si les variables [x] et [y] sont renommées
    en la même variable [z]. *)

Fixpoint regalloc (c: com) (L: IdentSet.t) : com :=
  match c with
  | SKIP => SKIP
  | ASSIGN x a =>
      if IdentSet.mem x L then
        match expr_is_var a with
        | None => ASSIGN (f x) (rename_aexp a)
        | Some y => if string_dec (f x) (f y) then SKIP else ASSIGN (f x) (rename_aexp a)
        end
      else SKIP
  | SEQ c1 c2 =>
      SEQ (regalloc c1 (live c2 L)) (regalloc c2 L)
  | IFTHENELSE b c1 c2 =>
      IFTHENELSE (rename_bexp b) (regalloc c1 L) (regalloc c2 L)
  | WHILE b c =>
      WHILE (rename_bexp b) (regalloc c (live (WHILE b c) L))
  end.

(** *** Relation entre les états mémoire *)

(** Nous adaptons la relation [agree] entre deux états mémoire,
    précédemment utilisée pour raisonner sur la transformation [dce].
    Maintenant, deux états mémoires [s1] et [s2] sont reliés vis-à-vis
    des variables vivantes [L] si pour toute variable [x] vivante,
    les valeurs de [x] dans [s1] et de [f x] dans [s2] coincident. *)

Definition agree' (L: IdentSet.t) (s1 s2: store) : Prop :=
  forall x, IdentSet.In x L -> s1 x = s2 (f x).

(** Cette définition est monotone par-rapport à l'ensemble [L]. *)

Lemma agree'_mon:
  forall L L' s1 s2,
  agree' L' s1 s2 -> IdentSet.Subset L L' -> agree' L s1 s2.
Proof.
  unfold IdentSet.Subset, agree'; intros. auto.
Qed.

(** Si deux états mémoire sont reliés sur les variables libres d'une
    expression, cette expression et son renommage s'évaluent à la même
    valeur dans les deux états. *)

Lemma aeval_agree':
  forall a s1 s2, agree' (fv_aexp a) s1 s2 -> aeval a s1 = aeval (rename_aexp a) s2.
Proof.
  induction a; cbn; intros.
- auto.
- apply H. fsetdec. 
- f_equal; [apply IHa1 | apply IHa2]; eapply agree'_mon; eauto; fsetdec.
- f_equal; [apply IHa1 | apply IHa2]; eapply agree'_mon; eauto; fsetdec.
Qed.

Lemma beval_agree':
  forall b s1 s2, agree' (fv_bexp b) s1 s2 -> beval b s1 = beval (rename_bexp b) s2.
Proof.
  induction b; cbn; intros.
- auto.
- auto.
- f_equal; eapply aeval_agree'; eapply agree'_mon; eauto; fsetdec.
- f_equal; eapply aeval_agree'; eapply agree'_mon; eauto; fsetdec.
- f_equal; apply IHb; auto.
- f_equal; [apply IHb1 | apply IHb2]; eapply agree'_mon; eauto; fsetdec.
Qed.

(** La relation [agree'] est préservée par affectation unilatérale
    à une variable morte. *)

Lemma agree'_update_dead:
  forall s1 s2 L x v,
  agree' L s1 s2 -> ~IdentSet.In x L ->
  agree' L (update x v s1) s2.
Proof.
  unfold agree', update; intros. destruct (string_dec x x0).
- subst x0. contradiction.
- apply H. fsetdec.
Qed.

(** La relation [agree'] est préservée par affectation de la même
    valeur à une variable vivante [x] et à son renommage [f x], pourvu
    qu'aucune des autres variables vivantes [z] ne soit renommée à [f x].
    C'est une propriété de non-interférence que le renommage [f] doit
    satisfaire. *)

Lemma agree'_update_live:
  forall s1 s2 L x v,
  agree' (IdentSet.remove x L) s1 s2 ->
  (forall z, IdentSet.In z L -> z <> x -> f z <> f x) ->
  agree' L (update x v s1) (update (f x) v s2).
Proof.
  unfold agree', update; intros.
  destruct (string_dec x x0); destruct (string_dec (f x) (f x0)).
- auto.
- congruence.
- exfalso. apply (H0 x0); auto.
- apply H. fsetdec.
Qed.

(** Un cas particulier du lemme [agree'_update_live], lorsque la
    valeur affectée à [x] et [f x] est la valeur d'une autre variable [y].
    Dans ce cas, comme observé par Chaitin, l'hypothèse de
    non-interférence peut être affaiblie. *)

Lemma agree'_update_move:
  forall s1 s2 L x y,
  agree' (IdentSet.union (IdentSet.remove x L) (IdentSet.singleton y)) s1 s2 ->
  (forall z, IdentSet.In z L -> z <> x -> z <> y -> f z <> f x) ->
  agree' L (update x (s1 y) s1) (update (f x) (s2 (f y)) s2).
Proof.
  unfold agree', update; intros.
  destruct (string_dec x x0); destruct (string_dec (f x) (f x0)).
- apply H. fsetdec.
- congruence.
- destruct (string_dec x0 y).
  + subst x0. apply H. fsetdec.
  + exfalso. apply (H0 x0); auto.
- apply H. fsetdec.
Qed.

(** Un cas particulier du lemma [agree'_update_move] dans le cas où
    [f x = f y], c'est-à-dire que les variables [x] et [y] se retrouvent
    placées dans la même variable.  Dans ce cas, l'affectation a été
    transformée en [SKIP]. *)

Lemma agree'_update_coalesced_move:
  forall s1 s2 L x y,
  agree' (IdentSet.union (IdentSet.remove x L) (IdentSet.singleton y)) s1 s2 ->
  (forall z, IdentSet.In z L -> z <> x -> z <> y -> f z <> f x) ->
  f x = f y ->
  agree' L (update x (s1 y) s1) s2.
Proof.
  unfold agree', update; intros.
  destruct (string_dec x x0); destruct (string_dec (f x) (f x0)).
- rewrite <- e0, H1. apply H. fsetdec.
- congruence.
- destruct (string_dec x0 y).
  + subst x0. apply H. fsetdec.
  + exfalso. apply (H0 x0); auto.
- apply H. fsetdec.
Qed.

(** *** Préservation sémantique *)

(** En regroupant les différentes hypothèses de non-interférence ci-dessus,
    on obtient une condition de correction pour un renommage [f].
    Si cette condition s'évalue à vrai, le renommage est une allocation
    de registres correcte. *)

Fixpoint correct_allocation (c: com) (L: IdentSet.t) : bool :=
  match c with
  | SKIP =>
      true
  | ASSIGN x a =>
      if IdentSet.mem x L then
        match expr_is_var a with
        | None => 
            IdentSet.for_all (fun z => String.eqb z x || negb (String.eqb (f z) (f x))) L
        | Some y =>
            IdentSet.for_all (fun z => String.eqb z x || String.eqb z y
                                    || negb (String.eqb (f z) (f x))) L
        end
      else true
  | SEQ c1 c2 => 
      correct_allocation c1 (live c2 L) && correct_allocation c2 L
  | IFTHENELSE b c1 c2 =>
      correct_allocation c1 L && correct_allocation c2 L
  | WHILE b c =>
      correct_allocation c (live (WHILE b c) L)
  end.

(** Sous l'hypothèse que le renommage [f] satisfait [correct_allocation],
    on démontre la préservation sémantique de l'allocation de registres
    avec le même diagramme de simulation en sémantique naturelle
    que pour l'élimination de code mort.  *)

Theorem regalloc_correct_terminating:
  forall s c s', cexec s c s' ->
  forall L s1,
  agree' (live c L) s s1 ->
  correct_allocation c L = true ->
  exists s1', cexec s1 (regalloc c L) s1' /\ agree' L s' s1'.
Proof.
  induction 1; intros L s1 AG CORR.
- (* SKIP *)
  exists s1; split. constructor. auto.
- (* ASSIGN *)
  cbn in *. destruct (IdentSet.mem x L) eqn:is_live.
  + (* x est vivante après *)
    destruct (expr_is_var a) as [y|] eqn:is_var.
    * apply expr_is_var_correct in is_var. subst a.
      assert (NONINTF: forall z, IdentSet.In z L -> z <> x -> z <> y -> f z <> f x).
      { apply IdentSet.for_all_2 in CORR. 
      - intros. apply CORR in H. 
        destruct (String.eqb_spec z x). congruence.
        destruct (String.eqb_spec z y). congruence.
        destruct (String.eqb_spec (f z) (f x)). discriminate. auto.
      - hnf. intros; congruence.
      }
      destruct (string_dec (f x) (f y)).
      ** (* affectation [x := y] supprimée *)
         econstructor; split.
         apply cexec_skip.
         apply agree'_update_coalesced_move; auto.
      ** (* affectation [x := y] conservée *)
         econstructor; split.
         apply cexec_assign.
         apply agree'_update_move; auto.
    * (* affectation [x := a], cas général *)
      assert (EVAL: aeval a s = aeval (rename_aexp a) s1)
      by (eapply aeval_agree'; eapply agree'_mon; eauto; fsetdec).
      assert (NONINTF: forall z, IdentSet.In z L -> z <> x -> f z <> f x).
      { apply IdentSet.for_all_2 in CORR. 
      - intros. apply CORR in H. 
        destruct (String.eqb_spec z x). congruence.
        destruct (String.eqb_spec (f z) (f x)). discriminate. auto.
      - hnf. intros; congruence.
      }
      econstructor; split.
      apply cexec_assign.
      rewrite <- EVAL. apply agree'_update_live; auto. eapply agree'_mon; eauto. fsetdec.
  + (* x est morte après *)
    econstructor; split.
    apply cexec_skip.
    apply agree'_update_dead. auto.
    red; intros. assert (IdentSet.mem x L = true) by (apply IdentSet.mem_1; auto). congruence.
- (* SEQ *)
  cbn in *. apply andb_prop in CORR; destruct CORR as [CORR1 CORR2].
  destruct (IHcexec1 _ _ AG CORR1) as (s1' & EXEC1 & AG1).
  destruct (IHcexec2 _ _ AG1 CORR2) as (s2' & EXEC2 & AG2).
  exists s2'; split.
  apply cexec_seq with s1'; auto.
  auto.
- (* IFTHENELSE *)
  cbn in *. apply andb_prop in CORR; destruct CORR as [CORR1 CORR2].
  assert (EVAL: beval b s = beval (rename_bexp b) s1)
  by (eapply beval_agree'; eapply agree'_mon; eauto; fsetdec).
  destruct (IHcexec L s1) as (s1' & EXEC' & AG').
  eapply agree_mon; eauto. destruct (beval b s); fsetdec. destruct (beval b s); auto.
  exists s1'; split.
  apply cexec_ifthenelse. rewrite <- EVAL. destruct (beval b s); auto.
  auto.
- (* WHILE done *)
Local Opaque live.
  cbn in *.
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval (rename_bexp b) s1)
  by (eapply beval_agree'; eapply agree'_mon; eauto; fsetdec).
  exists s1; split.
  apply cexec_while_done. congruence.
  eapply agree_mon; eauto.
- (* WHILE loop *)
  cbn in *.
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval (rename_bexp b) s1)
  by (eapply beval_agree'; eapply agree'_mon; eauto; fsetdec).
  destruct (IHcexec1 (live (WHILE b c) L) s1) as (s1' & EXEC1 & AG1).
  eapply agree_mon; eauto. auto.
  destruct (IHcexec2 L s1') as (s2' & EXEC2 & AG2).
  auto. auto.
  exists s2'; split.
  apply cexec_while_loop with s1'; auto. congruence.
  auto.
Local Transparent live.
Qed.

End RENAMING.

(** *** Exemples *)

(** Si le renommage est la fonction identité, l'allocation de registres
    se comporte exactement comme l'élimination de code mort. *)

Definition trivial_alloc := fun (x: ident) => x.

Eval compute in (correct_allocation trivial_alloc Euclidean_division (IdentSet.singleton "r")).

(** Résultat [true]. *)

Eval compute in (regalloc trivial_alloc Euclidean_division (IdentSet.singleton "r")).

(** Result is:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b <= r do                while b <= r do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

(** Voici un renommage non trivial qui place les variables "r" et "a" dans
    le même registre "a". *)

Definition my_alloc := fun (x: ident) => if string_dec x "r" then "a" else x.

Eval compute in (correct_allocation my_alloc Euclidean_division (IdentSet.singleton "r")).

(** Résultat [true]. *)

Eval compute in (regalloc my_alloc Euclidean_division (IdentSet.singleton "r")).

(** Voici le résultat.  On voit que l'affectation [r := a] a été supprimée.
<<
   r := a;                 ===>   skip;
   q := 0;                        skip;
   while b <= r do                while b <= a do
     r := r - b;                    a := a - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

(** En revanche, si nous essayons de placer les variables [r] et [b]
   au même endroit, la fonction de validation [correct_allocation]
   rejette cette allocation. *)

Definition wrong_alloc := fun (x: ident) => if string_dec x "r" then "b" else x.

Eval compute in (correct_allocation my_alloc Euclidean_division (IdentSet.singleton "r")).

(** Résultat [faux]. *)

(** ** 3.4. Pour aller plus loin: les points fixes *)

(** La bibliothèque [Fixpoints] montre comment calculer des points
    fixes exacts en suivant l'approche du théorème de
    Knaster-Tarski. *)

From CDF Require Import Fixpoints.

(** Dans cette section, nous allons appliquer cette approche à l'analyse des
    variables libres. *)

Section FIXPOINT_FINITE_SETS.

(** Première difficulté: l'ordre d'inclusion entre ensembles finis de
    variables n'est pas bien fondé!  Par exemple, on a la suite
    infinie croissante
<<
  {}, {"0"}, {"0","1"}, {"0","1","2"}, {"0","1","2","3"}, ...
>>

    Il faut donc nous restreindre aux sous-ensembles d'un univers [U]
    fini de variables, typiquement toutes les variables qui sont
    mentionnées dans le programme à analyser.
*)

Variable U: IdentSet.t.
Definition finset := { x: IdentSet.t | IdentSet.Subset x U }.

(** Nous munissons le type [finset] des opérations et des propriétés
    attendues par la bibliothèque [Fixpoints]. *)

Program Definition finset_eq (x y: finset) := IdentSet.Equal x y.

Program Definition finset_eq_dec (x y: finset) : {finset_eq x y} + {~finset_eq x y} :=
  match IdentSet.equal x y with true => left _ | false => right _ end.
Next Obligation.
  apply IdentSet.equal_2; auto.
Qed.
Next Obligation.
  red; intros. apply IdentSet.equal_1 in H. congruence.
Qed.

Program Definition finset_le (x y: finset) := IdentSet.Subset x y.

Lemma finset_le_trans:
  forall x y z, finset_le x y -> finset_le y z -> finset_le x z.
Proof.
  intros x y z; apply ISProp.subset_trans.
Qed.
Lemma finset_eq_le: forall x y, finset_eq x y -> finset_le y x.
Proof.
  intros. apply ISProp.subset_equal. apply ISProp.equal_sym. apply H.
Qed.

Program Definition finset_bot : finset := IdentSet.empty.
Next Obligation.
  fsetdec.
Qed.

Lemma finset_bot_smallest: forall x, finset_le finset_bot x.
Proof.
  intros; red; fsetdec.
Qed.

(** Il faut démontrer que l'ordre strict induit par inclusion est bien
    fondé.  Pour cela nous raisonnons sur les cardinaux (nombre
    d'éléments) des ensembles de variables, qui ne peuvent pas
    dépasser le cardinal de l'univers [U]. *)

Program Definition finset_cardinal (x: finset) := IdentSet.cardinal x.

Lemma finset_cardinal_max:
  forall x, (finset_cardinal x <= IdentSet.cardinal U)%nat.
Proof.
  intros. apply ISProp.subset_cardinal. apply proj2_sig.
Qed.

Lemma finset_cardinal_le:
  forall x y, finset_le x y -> (finset_cardinal x <= finset_cardinal y)%nat.
Proof.
  intros. apply ISProp.subset_cardinal. apply H.
Qed.

Lemma finset_cardinal_lt: forall x y,
  finset_le x y -> ~finset_eq x y -> (finset_cardinal x < finset_cardinal y)%nat.
Proof.
  intros.
  destruct (IdentSet.choose (IdentSet.diff (proj1_sig y) (proj1_sig x))) as [elt|] eqn:CHOOSE.
- apply IdentSet.choose_1 in CHOOSE.
  apply ISProp.subset_cardinal_lt with elt. auto. fsetdec. fsetdec.
- apply IdentSet.choose_2 in CHOOSE.
  assert (finset_le y x).
  { intros e IN. 
    destruct (ISProp.In_dec e (proj1_sig x)); auto.
    elim (CHOOSE e). apply IdentSet.diff_3; auto. }
  elim H0. apply ISProp.subset_antisym; auto.
Qed.
 
Lemma finset_gt_wf:
  well_founded (fun x y => finset_le y x /\ ~finset_eq y x).
Proof.
  set (M := fun x => (IdentSet.cardinal U - finset_cardinal x)%nat).
  apply wf_incl with (ltof _ M).
- red; intros x y [L E]; red. unfold M.
  generalize (finset_cardinal_max x), (finset_cardinal_max y),
             (finset_cardinal_lt y x L E); intros.
  lia.
- apply well_founded_ltof.
Qed.

(** Nous pouvons maintenant instancier le calcul de point fixe 
    fourni par la bibliothèque [Fixpoints]. *)

Definition monotone (F: finset -> finset) : Prop :=
  forall x y, finset_le x y -> finset_le (F x) (F y).

Definition finset_fixpoint (F: finset -> finset) (M: monotone F) : finset :=
  fixpoint finset finset_eq finset_eq_dec finset_le finset_gt_wf
           finset_bot finset_bot_smallest F M.

Lemma finset_fixpoint_eq:
  forall F M, finset_eq (finset_fixpoint F M) (F (finset_fixpoint F M)).
Proof.
  intros. unfold finset_fixpoint. apply fixpoint_eq.
Qed.

Lemma finset_fixpoint_smallest:
  forall F M z, finset_le (F z) z -> finset_le (finset_fixpoint F M) z.
Proof.
  intros. unfold finset_fixpoint. apply fixpoint_smallest; eauto using finset_le_trans.
Qed.

Lemma finset_fixpoint_mon:
  forall F1 M1 F2 M2,
  (forall x, finset_le (F1 x) (F2 x)) ->
  finset_le (finset_fixpoint F1 M1) (finset_fixpoint F2 M2).
Proof.
  intros. unfold finset_fixpoint. apply fixpoint_mon; eauto using finset_le_trans, finset_eq_le.
Qed.

(** Essayons de redéfinir l'analyse de vivacité en utilisant 
    les ensembles finis [finset] et le calcul de point fixe [finset_fixpoint].
*)
 
Fail Fixpoint live' (c: com) (L: finset) : finset :=
  match c with
  | SKIP => L
  | ASSIGN x a =>
      if IdentSet.mem x L
      then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
      else L
  | SEQ c1 c2 =>
      live' c1 (live' c2 L)
  | IFTHENELSE b c1 c2 =>
      IdentSet.union (fv_bexp b) (IdentSet.union (live' c1 L) (live' c2 L))
  | WHILE b c =>
      let L' := IdentSet.union (fv_bexp b) L in
      finset_fixpoint (fun x => IdentSet.union L' (live' c x)) _
  end.

(** Premier problème: lorsqu'on fait l'union de [L] avec [fv_aexp a] ou
    [fv_bexp b], rien ne garantit qu'on reste dans l'univers [U] des
    variables du programme.  Il faut donc ajouter une hypothèse 
    [IdentSet.Subset (fv_com c) U] pour garantir que le programme [c]
    en cours d'analyse est bien "contenu" dans l'univers [U].

    Second problème: afin d'utiliser [finset_fixpoint] dans le cas
    [WHILE], il faut lui passer une preuve que sa fonction argument
    est croissante.  Pour ce faire, il faut savoir que [live' c] est
    une fonction croissante de [finset] dans [finset], alors même que
    nous sommes en train de la définir!  Il faut donc définir [live']
    et montrer qu'elle est croissante simultanément.
*)

Program Fixpoint live' (c: com) (CONT: IdentSet.Subset (fv_com c) U)
                 : { f: finset -> finset | monotone f } :=
  match c with
  | SKIP => fun L => L
  | ASSIGN x a =>
      fun L =>
        if IdentSet.mem x L
        then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
        else L
  | SEQ c1 c2 =>
      fun L => live' c1 _ (live' c2 _ L)
  | IFTHENELSE b c1 c2 =>
      fun L => IdentSet.union (fv_bexp b)
                              (IdentSet.union (live' c1 _ L) (live' c2 _ L))
  | WHILE b c =>
      fun L =>
        let L' := IdentSet.union (fv_bexp b) L in
        finset_fixpoint (fun x => IdentSet.union L' (live' c _ x)) _
  end.
Next Obligation.
  red; auto.
Defined.
Next Obligation.
  cbn in CONT. generalize (proj2_sig L). fsetdec.
Defined.
Next Obligation.
  red; intros. rename x0 into L1. rename y into L2. unfold finset_le in *.
  destruct (IdentSet.mem x (proj1_sig L1)) eqn:M1; cbn.
- replace (IdentSet.mem x (proj1_sig L2)) with true. 
  cbn. fsetdec.
  symmetry. apply IdentSet.mem_1. apply H. apply IdentSet.mem_2; auto.
- destruct (IdentSet.mem x (proj1_sig L2)) eqn:M2; cbn; auto.
  apply IdentSet.mem_2 in M2. apply ISFact.not_mem_iff in M1.
  red; intros z IN. apply IdentSet.union_2. apply IdentSet.remove_2. congruence. auto.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  red; intros. auto.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT. generalize (proj2_sig (x L)), (proj2_sig (x0 L)); fsetdec.
Defined.
Next Obligation.
  red; intros; unfold finset_le; cbn.
  destruct (live' c1) as [f1 M1], (live' c2) as [f2 M2]. cbn.
  apply ISProp.union_subset_5.
  apply ISProp.FM.union_s_m. apply M1; auto. apply M2; auto.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT. generalize (proj2_sig (x0 x)) (proj2_sig L). fsetdec.
Defined.
Next Obligation.
  cbn in CONT. red; intros; unfold finset_le; cbn.
  destruct (live' c) as [f M]; cbn.
  apply ISProp.union_subset_5. apply M; auto.
Defined.
Next Obligation.
  cbn in CONT. red; intros. apply finset_fixpoint_mon.
  intros z; unfold finset_le; cbn.
  destruct (live' c) as [f M]; cbn.
  apply ISProp.union_subset_4. apply ISProp.union_subset_5. auto.
Defined.

(** Finalement, nous obtenons la fonction d'analyse voulue, mais non
    sans peine! *)

Definition live'' (c: com) (CONT: IdentSet.Subset (fv_com c) U) (L: finset) : finset :=
  proj1_sig (live' c CONT) L.

End FIXPOINT_FINITE_SETS.
