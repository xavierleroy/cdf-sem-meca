From Coq Require Import Bool String List Program.Equality.
From CDF Require Import Sequences.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** * 7.  Le langage fonctionnel typé FUN *)

(** ** 7.1.  Syntaxe et sémantique *)

(** Le langage se compose du lambda-calcul (variables, abstractions de fonctions,
    applications de fonctions) étendu avec les booléens: 
    constantes [Const true] et [Const false], et conditionnelle [Cond a ifso ifnot]
    (c.à.d. [if a then ifso else ifnot]).  *)
 
Inductive term: Type :=
  | Var (x: string)
  | Abs (x: string) (a: term)
  | App (a1: term) (a2: term)
  | Const (b: bool)
  | Cond (a: term) (ifso: term) (ifnot: term).

(** Les valeurs sont les abstractions de fonctions et les constantes booléennes. *)

Inductive isvalue: term -> Prop :=
  | V_Abs: forall x a,
      isvalue (Abs x a)
  | V_Const: forall b,
      isvalue (Const b).

(** [subst a x c] est la substitution de la variable [x] par le terme [c] dans le terme [a],
    aussi notée [a [x ← c]] dans le cours. *)

(** Cette substitution est incorrecte en général, car elle peut capturer des variables qui
    sont libres dans [c].  On ne peut l'utiliser que si [c] est un terme clos, sans variables
    libres, ce qui correspond à la réduction de programmes complets, sans variables libres.
    Le système de types de la section 7.2 assurera que c'est bien le cas. *)

Fixpoint subst (a: term) (x: string) (c: term) : term :=
  match a with
  | Var y => if string_dec x y then c else Var y
  | Abs y a => if string_dec x y then Abs y a else Abs y (subst a x c)
  | App a1 a2 => App (subst a1 x c) (subst a2 x c)
  | Const b => Const b
  | Cond a ifso ifnot => Cond (subst a x c) (subst ifso x c) (subst ifnot x c)
  end.

(** La sémantique à réductions: [red a a'] signifie que [a] se réduit en une étape vers [a'].
    On choisit une sémantique en appel par valeur, avec évaluation des applications de gauche à droite. *)

Inductive red: term -> term -> Prop :=
  (** beta réduction en appel par valeur *)
  | red_beta: forall x a v,
      isvalue v ->
      red (App (Abs x a) v) (subst a x v)
  (** réduction de la conditionnelle *)
  | red_cond: forall b ifso ifnot,
      red (Cond (Const b) ifso ifnot) (if b then ifso else ifnot)
  (** réduction dans un sous-terme *)
  | red_app_1: forall a1 a2 a1',
      red a1 a1' ->
      red (App a1 a2) (App a1' a2)
  | red_app_2: forall v a2 a2',
      isvalue v -> red a2 a2' ->
      red (App v a2) (App v a2')
  | red_cond_1: forall a a' ifso ifnot,
      red a a' ->
      red (Cond a ifso ifnot) (Cond a' ifso ifnot).

(** *** Exercice (1 étoile). *)
(** Modifier [red] pour obtenir une sémantique en appel par nom.
    Quel est l'impact de ce changement sur les résultats qui suivent? *)

(** *** Exercice (2 à 3 étoiles). *)
(** Enrichir la syntaxe et la sémantique de FUN pour y ajouter une ou plusieurs des extensions
    vues en cours: entiers de Peano, produits, sommes, points fixes. *)

(** Une autre présentation de la sémantique à réductions, dans le style popularisé par Wright et Felleisen.
    On définit d'abord les réductions en tête de terme. *)

Inductive head_red: term -> term -> Prop :=
  | head_red_beta: forall x a v,
      isvalue v ->
      head_red (App (Abs x a) v) (subst a x v)
  | head_red_cond: forall b ifso ifnot,
      head_red (Cond (Const b) ifso ifnot) (if b then ifso else ifnot).

(** On se donne ensuite un ensemble de contextes de réduction.  Les contextes sont
    représentés par des fonctions [C: term -> term], et le prédicat inductif [iscontext C]
    définit lesquelles de ces fonctions sont des contextes de réduction bien formés. *)

Inductive iscontext: (term -> term) -> Prop :=
  | iscontext_hole:                      (**r réduction au sommet *)
      iscontext (fun a => a)
  | iscontext_app_1: forall a C,         (**r réduction à gauche *)
      iscontext C -> iscontext (fun x => App (C x) a)
  | iscontext_app_2: forall v C,         (**r à droite d'une application *)
      isvalue v -> iscontext C -> iscontext (fun x => App v (C x))
  | iscontext_cond: forall C ifso ifnot, (**r à gauche d'une conditionnelle *)
      iscontext C -> iscontext (fun x => Cond (C x) ifso ifnot).

(** La relation de réduction sous contexte. *)

Inductive ctx_red: term -> term -> Prop :=
  | ctx_red_intro: forall a a' C,
      head_red a a' -> iscontext C ->
      ctx_red (C a) (C a').

(** Equivalence avec la réduction précédente. *)

Lemma ctx_red_to_red: 
  forall a a', ctx_red a a' -> red a a'.
Proof.
  assert (REC: forall a a', head_red a a' ->
               forall C, iscontext C ->
               red (C a) (C a')).
  { intros a a' HR; induction 1.
  - inversion HR; subst; constructor; auto.
  - apply red_app_1; auto.
  - apply red_app_2; auto.
  - apply red_cond_1; auto. }
  destruct 1. apply REC; auto.
Qed.

Lemma red_to_ctx_red:
  forall a a', red a a' -> ctx_red a a'.
Proof.
  induction 1.
- apply ctx_red_intro with (C := fun x => x).
  apply head_red_beta; auto.
  constructor.
- apply ctx_red_intro with (C := fun x => x).
  apply head_red_cond; auto.
  constructor.
- destruct IHred. apply ctx_red_intro with (C := fun x => App (C x) a2); auto using iscontext.
- destruct IHred. apply ctx_red_intro with (C := fun x => App v (C x)); auto using iscontext.
- destruct IHred. apply ctx_red_intro with (C := fun x => Cond (C x) ifso ifnot); auto using iscontext.
Qed.

(** La sémantique naturelle. *)

Inductive eval: term -> term -> Prop :=
  | eval_abs: forall x a,
      eval (Abs x a) (Abs x a)
  | eval_app: forall a1 a2 x a v2 v,
      eval a1 (Abs x a) -> eval a2 v2 -> eval (subst a x v2) v ->
      eval (App a1 a2) v
  | eval_const: forall b,
      eval (Const b) (Const b)
  | eval_cond: forall a ifso ifnot b v,
      eval a (Const b) -> eval (if b then ifso else ifnot) v ->
      eval (Cond a ifso ifnot) v.

Lemma eval_isvalue:
  forall a v, eval a v -> isvalue v.
Proof.
  induction 1; auto using isvalue.
Qed.

Lemma isvalue_eval:
  forall v, isvalue v -> eval v v.
Proof.
  destruct 1; eauto using eval.
Qed.

(** Equivalence entre sémantique naturelle [eval a v] et sémantique à réductions
    (il existe une suite de réductions depuis [a] vers la valeur [v]). *)

Lemma eval_reds:
  forall a v, eval a v -> star red a v.
Proof.
  induction 1.
- apply star_refl.
- apply star_trans with (App (Abs x a) a2).
  revert IHeval1. generalize a1, (Abs x a). induction 1; eauto using star, red_app_1.
  apply star_trans with (App (Abs x a) v2).
  revert IHeval2. generalize a2, v2. induction 1; eauto using star, red_app_2, isvalue.
  eapply star_step. apply red_beta. eapply eval_isvalue; eauto.
  apply IHeval3.
- apply star_refl.
- apply star_trans with (Cond (Const b) ifso ifnot).
  revert IHeval1. generalize a, (Const b). induction 1; eauto using star, red_cond_1.
  eapply star_step. apply red_cond. 
  apply IHeval2.
Qed. 

Lemma red_eval_eval:
  forall a1 a2, red a1 a2 -> forall v, eval a2 v -> eval a1 v.
Proof.
  induction 1; intros v' E.
- eauto using eval, isvalue_eval.
- eauto using eval.
- inversion E; subst; eauto using eval.
- inversion E; subst; eauto using eval, isvalue_eval.
- inversion E; subst; eauto using eval.
Qed.

Lemma reds_eval:
  forall a v, star red a v -> isvalue v -> eval a v.
Proof.
  induction 1; intros.
- apply isvalue_eval; auto.
- apply red_eval_eval with b; auto.
Qed. 

(** ** 7.2.  Typage simple *)

(** L'algèbre des types. *)

Inductive type: Type :=
  | Bool                          (**r type des booléens *)
  | Fun (t1: type) (t2: type).    (**r type des fonctions de [t1] dans [t2] *)

Notation " t1 --> t2 " := (Fun t1 t2) (right associativity, at level 55).

(** Les contextes de typage, associant un type à chaque variable. *)

Definition context := list (string * type).

Fixpoint lookup {A: Type} (x: string) (l: list (string * A)) : option A :=
  match l with
  | nil => None
  | (y, a) :: l => if string_dec x y then Some a else lookup x l
  end.

(** Les règles de typage. *)

Reserved Notation "E '⊢' a '∈' t" (at level 40).

Inductive has_type : context -> term -> type -> Prop :=
  | T_Var: forall E x t,
      lookup x E = Some t ->
      E ⊢ Var x ∈ t
  | T_Abs : forall E x a t t',
      ((x, t) :: E) ⊢ a ∈ t' ->
      E ⊢ Abs x a ∈ Fun t t'
  | T_App : forall E a1 a2 t t',
      E ⊢ a1 ∈ Fun t t' -> E ⊢ a2 ∈ t ->
      E ⊢ App a1 a2 ∈ t'
  | T_Const : forall E b,
      E ⊢ Const b ∈ Bool
  | T_Cond : forall E a ifso ifnot t,
      E ⊢ a ∈ Bool -> E ⊢ ifso ∈ t -> E ⊢ ifnot ∈ t ->
      E ⊢ Cond a ifso ifnot ∈ t

where "E '⊢' a '∈' t" := (has_type E a t).

(** Les principales propriétés du jugement de typage.  Tout d'abord, l'affaiblissement. *)

Lemma weakening:
  forall E a t, 
  E ⊢ a ∈ t ->
  forall E',
  (forall x tx, lookup x E = Some tx -> lookup x E' = Some tx) ->
  E' ⊢ a ∈ t.
Proof.
  induction 1; intros E' W; eauto using has_type.
- (* Abs *)
  apply T_Abs. apply IHhas_type.
  cbn; intros. destruct (string_dec x0 x); auto.
Qed.

(** L'affaiblissement est énoncé de manière inhabituelle.  D'ordinaire, on l'exprime
    avec une concaténation syntaxique de contexte: si [E ⊢ a ∈ t] alors [E' ++ E ⊢ a ∈ t].
    Mais cet énoncé est faux si [E'] peut lier des variables déjà liées dans [E].
    Sur papier on a des contraintes implicites qu'un contexte ne lie jamais deux fois
    la même variable, contraintes qui peuvent toujours être satisfaites par renommage.
    Dans notre développement Coq, nous n'avons pas de renommage, ni de contraintes de linéarité
    sur les contextes.  A la place, nous utilisons deux contextes [E] et [E'] et les relions
    par l'hypothèse "toutes les variables qui ont un type dans [E] ont le même type dans [E']". *)

(** Le lemme de stabilité du typage par substitution utilise la même astuce pour relier
-   le contexte [E] dans lequel le terme [a] est typé avant substitution;
-   le contexte [E'] dans lequel le terme [subst a x c] est typé après substitution.

    De plus, le lemme exige que [c] soit typé dans l'environnement vide, ce qui garantit
    qu'il est clos. *)

Lemma substitution_preserves_typing:
  forall E a t, 
  E ⊢ a ∈ t ->
  forall x c t' E',
  nil ⊢ c ∈ t' ->
  lookup x E = Some t' ->
  (forall y ty, y <> x -> lookup y E = Some ty -> lookup y E' = Some ty) ->
  E' ⊢ subst a x c ∈ t.
Proof.
  induction 1; intros until E'; intros TYC TYX TYE; cbn.
- (* Var *)
  destruct (string_dec x0 x).
  + (* Var x *)
    replace t with t' by congruence. 
    apply weakening with (E := nil); auto.
    cbn; intros; discriminate.
  + (* Var y, y <> x *)
    apply T_Var. apply TYE; auto.
- (* Abs *)
  destruct (string_dec x0 x).
  + (* Abs x a *)
    subst x0.
    apply T_Abs. apply weakening with (E := (x, t) :: E); auto.
    cbn; intros. destruct (string_dec x0 x); auto.
  + (* Abs y a, y <> x *)
    apply T_Abs. eapply IHhas_type; eauto.
    cbn. destruct (string_dec x0 x); congruence.
    cbn; intros. destruct (string_dec y x); auto.
- (* App *)
  apply T_App with t; eauto.
- (* Const *)
  apply T_Const.
- (* Cond *)
  apply T_Cond; eauto.
Qed.

(** Enfin, voici comment le type des valeurs closes détermine leur forme. *)

Lemma canonical_forms:
  forall v t,
  nil ⊢ v ∈ t -> isvalue v ->
  match t with
  | Bool => exists b, v = Const b
  | Fun t1 t2 => exists x a, v = Abs x a
  end.
Proof.
  intros v t TY VAL. inversion VAL; subst; inversion TY; subst.
- (* Fun type *)
  exists x, a; auto.
- (* Bool type *)
  exists b; auto.
Qed.

(** On peut alors montrer les deux propriétés essentielles qui relient typage et réductions:
    préservation et progrès. *)

Theorem reduction_preserves_typing:
  forall a a',
  red a a' ->
  forall t,
  nil ⊢ a ∈ t -> nil ⊢ a' ∈ t.
Proof.
  induction 1; intros t TY.
- (* red_beta *) 
  inversion TY; subst. inversion H3; subst.
  eapply substitution_preserves_typing; eauto.
  cbn. destruct (string_dec x x); congruence.
  cbn; intros. destruct (string_dec y x); congruence.
- (* red_cond *)
  inversion TY; subst.
  destruct b; auto.
- (* red_app_1 *)
  inversion TY; subst. apply T_App with t0; eauto. 
- (* red_app_2 *)
  inversion TY; subst. apply T_App with t0; eauto. 
- (* red_cond_1 *)
  inversion TY; subst. apply T_Cond; eauto.
Qed.

Theorem progress:
  forall a t,
  nil ⊢ a ∈ t -> isvalue a \/ exists a', red a a'.
Proof.
  intros a t TY; dependent induction TY.
- (* Abs x a *)
  left; apply V_Abs.
- (* App a1 a2 *)
  destruct IHTY1 as [ISVAL1 | (a1' & RED1)]; auto.
  + destruct IHTY2 as [ISVAL2 | (a2' & RED2)]; auto.
    * (* a1 et a2 sont des valeurs *)
      destruct (canonical_forms a1 (Fun t t')) as (x & a & E); auto.
      subst a1. right; exists (subst a x a2). apply red_beta; auto.
    * (* a1 est une valeur, a2 se réduit *)
      right; exists (App a1 a2'). apply red_app_2; auto.
  + (* a1 se réduit *)
    right; exists (App a1' a2). apply red_app_1; auto.
- (* Const b *)
  left; apply V_Const.
- (* Cond a ifso ifnot *)
  destruct IHTY1 as [ISVAL1 | (a' & RED1)]; auto.
  + (* a est une valeur *)
    destruct (canonical_forms a Bool) as (b & E); auto.
    subst a. right; exists (if b then ifso else ifnot). apply red_cond.
  + (* a se réduit *)
    right; exists (Cond a' ifso ifnot). apply red_cond_1; auto.
Qed.

(** Il s'ensuit qu'un terme bien typé ne peut pas "planter" ("does not go wrong"). *)

Definition goes_wrong (a: term) : Prop :=
  exists a', star red a a' /\ irred red a' /\ ~isvalue a'.

Theorem well_typed_programs_do_not_go_wrong:
  forall a t,
  nil ⊢ a ∈ t -> ~ goes_wrong a.
Proof.
  intros a t TY (a' & REDS & IRRED & NOTVAL).
  assert (TY': nil ⊢ a' ∈ t).
  { clear IRRED NOTVAL. revert a a' REDS TY. induction 1; eauto using reduction_preserves_typing. }
  destruct (progress a' t TY') as [ISVAL | (a'' & RED)].
  - apply NOTVAL. auto.
  - apply IRRED with a''. auto.
Qed.

(** Une présentation davantage positive du même résultat.  On définit coinductivement
    le prédicat [safe a], signifiant "a s'exécute sans planter".  Il recouvre à la fois
    le cas où la réduction de [a] termine sans erreur sur une valeur, et le cas où la réduction de [a] diverge. *)

CoInductive safe: term -> Prop :=
  | safe_value: forall v,
      isvalue v ->
      safe v
  | safe_red: forall a a',
      red a a' -> safe a' ->
      safe a.

Theorem well_typed_programs_are_safe:
  forall a t,
  nil ⊢ a ∈ t -> safe a.
Proof.
  cofix CIH; intros.
  destruct (progress a t H) as [ISVAL | (a' & RED)].
- apply safe_value; auto.
- apply safe_red with a'; auto.
  apply CIH with t. apply reduction_preserves_typing with a; auto.
Qed.

(** *** Exercice (2 à 3 étoiles). *)
(** Enrichir le système de type pour y ajouter une ou plusieurs des extensions
    vues en cours: entiers de Peano, produits, sommes, points fixes.
    Adapter la démonstration de sûreté du typage. *)

(** *** Exercice (3 étoiles). *)
(** Dans la définition de l'algèbre de types, remplacer [Inductive type ...] par [CoInductive type ...].
    Cela permet d'avoir des expressions de types infinies, comme p.ex. [Bool --> Bool --> ... --> Bool --> ...].
-   Vérifier que la sûreté du typage est inchangée.
-   Montrer que l'on peut typer le combinateur de point fixe [Y] donné dans le cours avec le type
    [(t --> t) --> t] pour tout type [t]. *)
Remark type_Y: forall t,
  let D := Abs "x" (App (Var "f") (App (Var "x") (Var "x"))) in
  let Y := Abs "f" (App D D) in
  nil ⊢ Y ∈ ((t --> t) --> t).
Proof.
  intros t D Y.
  (* A COMPLETER *)
Abort.

(** ** 7.3.  Sous-typage *)

Module Subtyping.

(** On enrichit l'algèbre des types avec un type [Top] de toutes les valeurs. *)

Inductive type: Type :=
  | Top                           (**r type universel *)
  | Bool                          (**r type des booléens *)
  | Fun (t1: type) (t2: type).    (**r type des fonctions de [t1] dans [t2] *)

Reserved Notation "t '<:' s" (at level 40).

Inductive subtype: type -> type -> Prop :=
  | subtype_top: forall t,
      t <: Top
  | subtype_bool:
      Bool <: Bool
  | subtype_fun: forall s1 t1 s2 t2,
      s2 <: s1 -> t1 <: t2 ->
      Fun s1 t1 <: Fun s2 t2

where "t '<:' s" := (subtype t s).

Lemma subtype_refl:
  forall t, t <: t.
Proof.
  induction t; auto using subtype.
Qed.

Lemma subtype_trans:
  forall t1 t2 t3, t1 <: t2 -> t2 <: t3 -> t1 <: t3.
Proof.
  intros t1 t2; revert t2 t1.
  induction t2; intros t1 t3 S1 S2; inversion S1; inversion S2; subst; eauto using subtype.
Qed.

Definition context := list (string * type).

Inductive has_type : context -> term -> type -> Prop :=
  | T_Var: forall E x t,
      lookup x E = Some t ->
      E ⊢ Var x ∈ t
  | T_Abs : forall E x a t t',
      ((x, t) :: E) ⊢ a ∈ t' ->
      E ⊢ Abs x a ∈ Fun t t'
  | T_App : forall E a1 a2 t t',
      E ⊢ a1 ∈ Fun t t' -> E ⊢ a2 ∈ t ->
      E ⊢ App a1 a2 ∈ t'
  | T_Const : forall E b,
      E ⊢ Const b ∈ Bool
  | T_Cond : forall E a ifso ifnot t,
      E ⊢ a ∈ Bool -> E ⊢ ifso ∈ t -> E ⊢ ifnot ∈ t ->
      E ⊢ Cond a ifso ifnot ∈ t
  | T_Sub: forall E a s t,       (**r <-- nouveau! *)
      E ⊢ a ∈ s -> s <: t ->
      E ⊢ a ∈ t

where "E '⊢' a '∈' t" := (has_type E a t).

(** *** Exercice (4 étoiles). *)
(** Montrer la sûreté de ce système de types avec sous-typage.
    On peut réutiliser de grandes parties de la démonstration de la section 7.2. *)

Lemma weakening:
  forall E a t, 
  E ⊢ a ∈ t ->
  forall E',
  (forall x tx, lookup x E = Some tx -> lookup x E' = Some tx) ->
  E' ⊢ a ∈ t.
Proof.
  induction 1; intros E' W; eauto using has_type.
- (* Abs *)
  apply T_Abs. apply IHhas_type.
  cbn; intros. destruct (string_dec x0 x); auto.
Qed.

(** L'affaiblissement est énoncé de manière inhabituelle.  D'ordinaire, on l'exprime
    avec une concaténation syntaxique de contexte: si [E ⊢ a ∈ t] alors [E' ++ E ⊢ a ∈ t].
    Mais cet énoncé est faux si [E'] peut lier des variables déjà liées dans [E].
    Sur papier on a des contraintes implicites qu'un contexte ne lie jamais deux fois
    la même variable, contraintes qui peuvent toujours être satisfaites par renommage.
    Dans notre développement Coq, nous n'avons pas de renommage, ni de contraintes de linéarité
    sur les contextes.  A la place, nous utilisons deux contextes [E] et [E'] et les relions
    par l'hypothèse "toutes les variables qui ont un type dans [E] ont le même type dans [E']". *)

(** Le lemme de stabilité du typage par substitution utilise la même astuce pour relier
-   le contexte [E] dans lequel le terme [a] est typé avant substitution;
-   le contexte [E'] dans lequel le terme [subst a x c] est typé après substitution.

    De plus, le lemme exige que [c] soit typé dans l'environnement vide, ce qui garantit
    qu'il est clos. *)

Lemma substitution_preserves_typing:
  forall E a t, 
  E ⊢ a ∈ t ->
  forall x c t' E',
  nil ⊢ c ∈ t' ->
  lookup x E = Some t' ->
  (forall y ty, y <> x -> lookup y E = Some ty -> lookup y E' = Some ty) ->
  E' ⊢ subst a x c ∈ t.
Proof.
  induction 1; intros until E'; intros TYC TYX TYE; cbn.
- (* Var *)
  destruct (string_dec x0 x).
  + (* Var x *)
    replace t with t' by congruence. 
    apply weakening with (E := nil); auto.
    cbn; intros; discriminate.
  + (* Var y, y <> x *)
    apply T_Var. apply TYE; auto.
- (* Abs *)
  destruct (string_dec x0 x).
  + (* Abs x a *)
    subst x0.
    apply T_Abs. apply weakening with (E := (x, t) :: E); auto.
    cbn; intros. destruct (string_dec x0 x); auto.
  + (* Abs y a, y <> x *)
    apply T_Abs. eapply IHhas_type; eauto.
    cbn. destruct (string_dec x0 x); congruence.
    cbn; intros. destruct (string_dec y x); auto.
- (* App *)
  apply T_App with t; eauto.
- (* Const *)
  apply T_Const.
- (* Cond *)
  apply T_Cond; eauto.
- (* Sub *)
  apply T_Sub with s; eauto.
Qed.

(** Enfin, voici comment le type des valeurs closes détermine leur forme. *)

Lemma canonical_forms_fun:
  forall v t1 t2, nil ⊢ v ∈ Fun t1 t2 -> isvalue v -> exists x a, v = Abs x a.
Proof.
  intros v t1 t2 TY. dependent induction TY; intros VAL.
- exists x, a; auto.
- inversion VAL.
- inversion VAL.
- inversion H; subst. eapply IHTY; eauto. 
Qed.

Lemma canonical_forms_bool:
  forall v, nil ⊢ v ∈ Bool -> isvalue v -> exists b, v = Const b.
Proof.
  intros v TY. dependent induction TY; intros VAL.
- inversion VAL.
- exists b; auto.
- inversion VAL.
- inversion H; subst. eapply IHTY; eauto.
Qed.

Lemma T_Abs_inv:
  forall E x a t,
  E ⊢ Abs x a ∈ t -> exists t1 t2, ((x, t1) :: E) ⊢ a ∈ t2 /\ Fun t1 t2 <: t.
Proof.
  intros until t; intros TY; dependent induction TY.
- exists t, t'; auto using subtype_refl.
- edestruct IHTY as (t1 & t2 & P & Q); eauto.
  exists t1, t2; split. auto. apply subtype_trans with s; auto.
Qed.

Lemma T_App_inv:
  forall E a1 a2 t,
  E ⊢ App a1 a2 ∈ t -> exists t1 t2, E ⊢ a1 ∈ Fun t1 t2 /\ E ⊢ a2 ∈ t1 /\ t2 <: t.
Proof.
  intros until t; intros TY; dependent induction TY.
- exists t, t'; auto using subtype_refl.
- edestruct IHTY as (t1 & t2 & P & Q & R); eauto.
  exists t1, t2; split. auto. split. auto. apply subtype_trans with s; auto.
Qed.

Lemma T_Cond_inv:
  forall E a ifso ifnot t,
  E ⊢ Cond a ifso ifnot ∈ t -> exists t', E ⊢ a ∈ Bool /\ E ⊢ ifso ∈ t' /\ E ⊢ ifnot ∈ t' /\ t' <: t.
Proof.
  intros until t; intros TY; dependent induction TY.
- exists t; auto using subtype_refl.
- edestruct IHTY as (t' & P & Q & R & S); eauto.
  exists t'; intuition auto. apply subtype_trans with s; auto.
Qed.

(** On peut alors montrer les deux propriétés essentielles qui relient typage et réductions:
    préservation et progrès. *)

Theorem reduction_preserves_typing:
  forall a a',
  red a a' ->
  forall t,
  nil ⊢ a ∈ t -> nil ⊢ a' ∈ t.
Proof.
  induction 1; intros t TY.
- (* red_beta *) 
  destruct (T_App_inv _ _ _ _ TY) as (t1 & t2 & TY1 & TY2 & SUB).
  destruct (T_Abs_inv _ _ _ _ TY1) as (t3 & t4 & TY3 & SUB').
  inversion SUB'; subst.
  apply T_Sub with t4.
  eapply substitution_preserves_typing with (t' := t3); eauto.
  apply T_Sub with t1; auto.
  cbn. destruct (string_dec x x); congruence.
  cbn; intros. destruct (string_dec y x); congruence.
  apply subtype_trans with t2; auto.
- (* red_cond *)
  destruct (T_Cond_inv _ _ _ _ _ TY) as (t' & TY1 & TY2 & TY3 & SUB).
  apply T_Sub with t'.
  destruct b; auto.
  auto.
- (* red_app_1 *)
  destruct (T_App_inv _ _ _ _ TY) as (t1 & t2 & TY1 & TY2 & SUB).
  apply T_Sub with t2; auto.
  apply T_App with t1; auto.
- (* red_app_2 *)
  destruct (T_App_inv _ _ _ _ TY) as (t1 & t2 & TY1 & TY2 & SUB).
  apply T_Sub with t2; auto.
  apply T_App with t1; auto.
- (* red_cond_1 *)
  destruct (T_Cond_inv _ _ _ _ _ TY) as (t' & TY1 & TY2 & TY3 & SUB).
  apply T_Sub with t'; auto.
  apply T_Cond; eauto.
Qed.

Theorem progress:
  forall a t,
  nil ⊢ a ∈ t -> isvalue a \/ exists a', red a a'.
Proof.
  intros a t TY; dependent induction TY.
- (* Abs x a *)
  left; apply V_Abs.
- (* App a1 a2 *)
  destruct IHTY1 as [ISVAL1 | (a1' & RED1)]; auto.
  + destruct IHTY2 as [ISVAL2 | (a2' & RED2)]; auto.
    * (* a1 et a2 sont des valeurs *)
      destruct (canonical_forms_fun a1 t t') as (x & a & E); auto.
      subst a1. right; exists (subst a x a2). apply red_beta; auto.
    * (* a1 est une valeur, a2 se réduit *)
      right; exists (App a1 a2'). apply red_app_2; auto.
  + (* a1 se réduit *)
    right; exists (App a1' a2). apply red_app_1; auto.
- (* Const b *)
  left; apply V_Const.
- (* Cond a ifso ifnot *)
  destruct IHTY1 as [ISVAL1 | (a' & RED1)]; auto.
  + (* a est une valeur *)
    destruct (canonical_forms_bool a) as (b & E); auto.
    subst a. right; exists (if b then ifso else ifnot). apply red_cond.
  + (* a se réduit *)
    right; exists (Cond a' ifso ifnot). apply red_cond_1; auto.
- (* subtyping *)
  apply IHTY; auto.
Qed.

End Subtyping.

(** ** 7.4.  Termes intrinsiquement typés *)

From Coq Require Import FunctionalExtensionality.

Module Intrinsic.

Definition context := list type.

Inductive var: context -> type -> Type :=
  | V1: forall {E: context} {t: type}, var (t :: E) t
  | VS: forall {E: context} {t t': type}, var E t' -> var (t :: E) t'.

Inductive term: context -> type -> Type :=
  | Var: forall {E: context} {t: type},
         var E t ->
         term E t
  | Abs: forall {E: context} {t t': type},
         term (t :: E) t' ->
         term E (Fun t t')
  | App: forall {E: context} {t t': type},
         term E (Fun t t') -> term E t ->
         term E t'
  | Const: forall {E: context} (b: bool),
         term E Bool
  | Cond: forall {E: context} {t: type},
         term E Bool -> term E t -> term E t ->
         term E t.

(** Exemples de termes. *)

Definition V2 {E: context} {t1 t2: type}: var (t1 :: t2 :: E) t2 := VS V1.
Definition V3 {E: context} {t1 t2 t3: type}: var (t1 :: t2 :: t3 :: E) t3 := VS V2.

(** [fun b => if b then false else true] *)
Definition t_negation : term nil (Bool --> Bool) :=
  Abs (Cond (Var V1) (Const false) (Const true)).

(** [fun f => fun g => fun x => g (f x)] *)
Definition t_compose (t1 t2 t3: type) : term nil ((t1 --> t2) --> (t2 --> t3) --> (t1 --> t3)) :=
  Abs (Abs (Abs (App (Var V2) (App (Var V3) (Var V1))))).

(** Un terme mal typé et donc impossible à exprimer. *)
Fail Definition t_error : term nil Bool :=
  Cond (Abs (Var V1)) (Const false) (Const true).

(** Sémantique dénotationnelle *)

Fixpoint dtype (t: type) : Type :=
  match t with
  | Bool => bool
  | Fun t1 t2 => dtype t1 -> dtype t2
  end.

Fixpoint dcontext (E: context) : Type :=
  match E with
  | nil => unit
  | t :: E => dtype t * dcontext E
  end.

Fixpoint dvar {E: context} {t: type} (v: var E t): dcontext E -> dtype t :=
  match v in var E t return dcontext E -> dtype t with
  | V1 => (fun e => fst e)
  | VS v => (fun e => dvar v (snd e))
  end.

Fixpoint dterm {E: context} {t: type} (a: term E t) : dcontext E -> dtype t :=
  match a in term E t return dcontext E -> dtype t with
  | Var v => dvar v
  | Abs a => (fun e => (fun v => dterm a (v, e)))
  | App a1 a2 => (fun e => dterm a1 e (dterm a2 e))
  | Const b => (fun e => b)
  | Cond a ifso ifnot => (fun e => if dterm a e then dterm ifso e else dterm ifnot e)
  end.

Lemma dbeta: forall (E: context) (t t': type) (a1: term (t :: E) t') (a2: term E t),
  forall e, dterm (App (Abs a1) a2) e = dterm a1 (dterm a2 e, e).
Proof.
  reflexivity.
Qed.

Lemma dconst: forall (E: context) (t: type) (b: bool) (ifso ifnot: term E t),
  forall e, dterm (Cond (Const b) ifso ifnot) e = dterm (if b then ifso else ifnot) e.
Proof.
  intros. destruct b; reflexivity.
Qed.

(** Substitution *)

Fixpoint unlift_env (E': context) (t': type) (E: context) : dcontext (E' ++ t' :: E) -> dcontext (E' ++ E) :=
  match E' with
  | nil => fun e => snd e
  | t :: E' => fun e => (fst e, unlift_env E' t' E (snd e))
  end.

Definition lift_var  (E': context) (t': type) {E: context} {t: type} (v: var (E' ++ E) t) :
           { w : var (E' ++ t' :: E) t
           | forall e, dvar w e = dvar v (unlift_env E' t' E e)}.
Proof.
  revert E' t' E t v. induction E' as [ | t0 E' ]; cbn.
- intros. exists (VS v). auto.
- intros. dependent destruction v.
  + exists V1. auto.
  + destruct (IHE' t' _ _ v) as (w & W). exists (VS w). intros; cbn. rewrite W; auto.
Defined.

Definition lift (E': context) (t': type) {E: context} {t: type} (a: term (E' ++ E) t) :
           { b : term (E' ++ t' :: E) t
           | forall e, dterm b e = dterm a (unlift_env E' t' E e) }.
Proof.
  dependent induction a.
- destruct (lift_var E' t' v) as (w & W). exists (Var w). auto.
- destruct (IHa (t::E') _ a) as (b & B); auto.
  exists (Abs b). intros. apply functional_extensionality; intros. cbn. rewrite B. auto.
- destruct (IHa1 E' _ a1) as (b1 & B1); auto.
  destruct (IHa2 E' _ a2) as (b2 & B2); auto.
  exists (App b1 b2). cbn; intros. rewrite B1, B2. auto.
- exists (Const b); auto.
- destruct (IHa1 E' _ a1) as (b1 & B1); auto.
  destruct (IHa2 E' _ a2) as (b2 & B2); auto.
  destruct (IHa3 E' _ a3) as (b3 & B3); auto.
  exists (Cond b1 b2 b3). intros; cbn. rewrite B1, B2, B3; auto.
Defined.

Definition lift1 (t': type) {E: context} {t: type} (a: term E t) :
           { b : term (t' :: E) t
           | forall e, dterm b e = dterm a (snd e) }.
Proof.
  apply lift with (E' := nil).
Defined.

Fixpoint proj_env (E': context) (E: context) : dcontext (E' ++ E) -> dcontext E :=
  match E' with
  | nil => fun e => e
  | t :: E' => fun e => proj_env E' E (snd e)
  end.

Fixpoint unsubst_env (E': context) (t': type) (E: context) : dcontext (E' ++  E) -> dtype t' -> dcontext (E' ++ t' :: E) :=
  match E' with
  | nil => fun e v => (v, e)
  | t :: E' => fun e v => (fst e, unsubst_env E' t' E (snd e) v)
  end.

Definition subst_var (E': context) (t': type) {E: context} {t: type} (v: var (E' ++ t' :: E) t) (b: term E t') :
           { c : term (E' ++ E) t
           | forall e, dterm c e = dvar v (unsubst_env E' t' E e (dterm b (proj_env E' E e))) }.
Proof.
  induction E' as [ | t0 E' ]; simpl.
- dependent destruction v; simpl.
  + exists b; auto.
  + exists (Var v); auto.
- dependent destruction v; simpl.
  + exists (Var V1); auto.
  + destruct (IHE' v) as (c & C). destruct (lift1 t0 c) as (c' & C'). exists c'.
    simpl; intros. rewrite C', C. auto.
Defined.

Definition subst (E': context) (t': type) {E: context} {t: type} (a: term (E' ++ t' :: E) t) (b: term E t') :
           { c : term (E' ++ E) t
           | forall e, dterm c e = dterm a (unsubst_env E' t' E e (dterm b (proj_env E' E e))) }.
Proof.
  dependent induction a.
- apply subst_var. 
- edestruct (IHa (t :: E') t' E a) as (c & C); eauto.
  exists (Abs c). intros. apply functional_extensionality. intros v; simpl. 
  rewrite C. simpl. eauto.
- edestruct (IHa1 E' t' E a1) as (c1 & C1); eauto.
  edestruct (IHa2 E' t' E a2) as (c2 & C2); eauto.
  exists (App c1 c2). simpl; intros. rewrite C1, C2. eauto.
- exists (Const b). simpl; auto.
- edestruct (IHa1 E' t' E a1) as (c1 & C1); eauto.
  edestruct (IHa2 E' t' E a2) as (c2 & C2); eauto.
  edestruct (IHa3 E' t' E a3) as (c3 & C3); eauto.
  exists (Cond c1 c2 c3). simpl; intros. rewrite C1, C2, C3. eauto.
Defined.

Definition subst1 {t': type} {E: context} {t: type} (a: term (t' :: E) t) (b: term E t') : term E t :=
  proj1_sig (subst nil t' a b).

Lemma dterm_subst1:
  forall {t': type} {E: context} {t: type} (a: term (t' :: E) t) (b: term E t') e,
  dterm (subst1 a b) e = dterm a (dterm b e, e).
Proof.
  intros. unfold subst1. destruct (subst nil t' a b) as (c & C). apply C. 
Qed.

(** Sémantique à réductions *)

Inductive isvalue: forall (E: context) (t: type), term E t -> Prop :=
  | V_Abs: forall E t1 t2 (a: term (t1 :: E) t2),
      isvalue E (Fun t1 t2) (Abs a)
  | V_Const: forall E b,
      isvalue E Bool (Const b).

Inductive red: forall E t, term E t -> term E t -> Prop :=
  | red_beta: forall E t1 t2 (a: term (t1 :: E) t2) (v: term E t1),
      isvalue E t1 v ->
      red E t2 (App (Abs a) v) (subst1 a v)
  | red_cond: forall E t (b: bool) (ifso ifnot: term E t),
      red E t (Cond (Const b) ifso ifnot) (if b then ifso else ifnot)
  | red_app_1: forall E t t' (a1 a1': term E (Fun t t')) (a2: term E t),
      red E (Fun t t') a1 a1' ->
      red E t' (App a1 a2) (App a1' a2)
  | red_app_2: forall E t t' (v: term E (Fun t t')) (a2 a2': term E t),
      isvalue E (Fun t t') v -> red E t a2 a2' ->
      red E t' (App v a2) (App v a2')
  | red_cond_1: forall E t (a a': term E Bool) (ifso ifnot: term E t),
      red E Bool a a' ->
      red E t (Cond a ifso ifnot) (Cond a' ifso ifnot).

Theorem red_denot:
  forall E t a1 a2, red E t a1 a2 -> forall e, dterm a1 e = dterm a2 e.
Proof.
  induction 1; simpl; intros.
- rewrite dterm_subst1; auto.
- destruct b; auto.
- rewrite IHred; auto.
- rewrite IHred; auto.
- rewrite IHred; auto.
Qed.

End Intrinsic.
