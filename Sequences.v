(** Une bibliothèque d'opérateurs sur les relations
    pour définir les suites de transitions et leurs propriétés. *)

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.                 (**r le type des états *)
Variable R: A -> A -> Prop.       (**r la relation de transition entre états *)

(** ** Suites finies de transitions *)

(** Zéro, une ou plusieurs transitions: fermeture réflexive transitive de [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; eauto using star. 
Qed.

(** Une ou plusieurs transitions: fermeture transitive de [R]. *)

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b, R a b -> plus a b.
Proof.
  eauto using star, plus. 
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
  intros. inversion H. eauto using star.  
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
  intros. inversion H. eauto using plus, star_trans.
Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H0. inversion H; eauto using plus, star, star_trans.
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
  eauto using star_plus_trans, plus_one.
Qed.

(** Absence de transition depuis un état. *)

Definition irred (a: A) : Prop := forall b, ~(R a b).

(** ** Suites infinies de transitions *)

(** On peut facilement caractériser le cas où toutes les suites de transitions
  issues d'un état [a] sont infinies: il suffit de dire que toute suite
  finie issue de [a] peut être prolongée par une transition de plus. *)

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

(** Cependent, ce n'est pas le cas que nous voulons caractériser: le cas où
  il existe au moins une suite infinie de transitions issue de [a],
  [a --> a1 --> a2 --> ... -> aN -> ...],
  sans que toutes les suites issues de [a] soient nécessairement infinies.

  Exemple: prenons [A = nat] et [R] telle que [R 0 0] et [R 0 1].  
  [all_seq_inf 0] n'est pas vrai car la suite [0 -->* 1] ne peut pas être
  prolongée.  Et pourtant [R] admet une suite infinie, à savoir
  [0 --> 0 --> ...].  

  On pourrait représenter la suite infinie [a0 --> a1 --> a2 --> ... -> aN -> ...] 
  explicitement, comme une fonction [f: nat -> A] telle que [f i] est le
  [i]-ème état [ai] de la suite. *)

Definition infseq_with_function (a: A) : Prop :=
  exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f (1 + i)).

(** C'est une caractérisation correcte, mais peu pratique en Coq:
  très souvent, la fonction [f] n'est pas calculable et ne peut donc
  être définie en Coq.

  Cependant, nous n'avons pas vraiment besoin de la fonction [f].
  Son ensemble image [X] nous suffit!  Ce qui importe c'est qu'il existe
  un ensemble [X] tel que [a] est dans [X] et tout [b] dans [X] peut
  faire une transition vers un autre élément de [X].  Cela suffit pour
  qu'il existe une suite infinie de transitions depuis [a].
*)

Definition infseq (a: A) : Prop :=
  exists X: A -> Prop,
  X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

(** Cette définition est essentiellement un principe de coinduction.
    Montrons quelques propriétés attendues.  Par exemple: si la relation
    [R] contient un cycle, elle admet une suite infinie. *)

Remark cycle_infseq:
  forall a, R a a -> infseq a.
Proof.
  intros. exists (fun b => b = a); split.
  auto.
  intros. subst a1. exists a; auto.
Qed.

(** Plus généralement: si toutes les suites issues de [a] sont infinies,
  il existe une suite infinie issue de [a]. *)

Lemma infseq_if_all_seq_inf:
  forall a, all_seq_inf a -> infseq a.
Proof.
  intros a0 ALL0. 
  exists all_seq_inf; split; auto.
  intros a1 ALL1. destruct (ALL1 a1) as [a2 R12]. constructor. 
  exists a2; split; auto.
  intros a3 S23. destruct (ALL1 a3) as [a4 R23]. apply star_step with a2; auto.
  exists a4; auto.
Qed.

(** De même, la caractérisation à base de fonctions [infseq_with_function]
    implique [infseq]. *)

Lemma infseq_from_function:
  forall a, infseq_with_function a -> infseq a.
Proof.
  intros a0 (f & F0 & Fn). exists (fun a => exists i, f i = a); split.
- exists 0; auto.
- intros a1 (i1 & F1). subst a1. exists (f (1 + i1)); split; auto. exists (1 + i1); auto.
Qed.  

(** Un lemme d'inversion sur [infseq]: si [infseq a], i.e. il existe une
  suite infinie issue de [a], alors [a] peut faire une transition
  vers un état [b] qui lui aussi vérifie [infseq b]. *)

Lemma infseq_inv:
  forall a, infseq a -> exists b, R a b /\ infseq b.
Proof.
  intros a (X & Xa & XP). destruct (XP a Xa) as (b & Rab & Xb). 
  exists b; split; auto. exists X; auto.
Qed.

(** Une variante très utile du principe de coinduction s'appuie sur
  un ensemble [X] where for every [a] in [X], we can make one *or
  several* transitions to reach a [b] in [X].  *)

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros X H a0 Xa0. 
  exists (fun a => exists b, star a b /\ X b); split.
- exists a0; auto using star_refl.
- intros a1 (a2 & S12 & X2). inversion S12; subst.
  + destruct (H a2 X2) as (a3 & P23 & X3). inversion P23; subst.
    exists b; split; auto. exists a3; auto.
  + exists b; split; auto. exists a2; auto.
Qed.

(** ** Propriétés de déterminisme des relations de transition fonctionnelles *)

(** Une relation de transition est fonctionnelle si tout état peut faire
  une transition vers au plus un autre état. *)

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.

(** Propriétés d'unicité des suites finies de transitions. *)

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
  induction 1; intros.
- auto.
- inversion H1; subst.
+ right. eauto using star. 
+ assert (b = b0) by (eapply R_functional; eauto). subst b0. 
  apply IHstar; auto.
Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof.
  intros. destruct (star_star_inv H H1).
- inversion H3; subst. auto. elim (H0 _ H4).
- inversion H3; subst. auto. elim (H2 _ H4).
Qed.

(** Un état ne peut à la fois diverger et terminer sur un état irréductible. *)

Lemma infseq_inv':
  forall a b, R a b -> infseq a -> infseq b.
Proof.
  intros a b Rab Ia. 
  destruct (infseq_inv Ia) as (b' & Rab' & Xb').
  assert (b' = b) by (eapply R_functional; eauto). 
  subst b'. auto.
Qed.

Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof.
  induction 1; intros.
- auto. 
- apply IHstar. apply infseq_inv' with a; auto.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> infseq a -> False.
Proof.
  intros.
  destruct (@infseq_inv b) as (c & Rbc & _). eapply infseq_star_inv; eauto. 
  apply (H0 c); auto.
Qed.

(** S'il existe une suite infinie de transitions depuis [a], toutes
  les suites de transitions depuis [a] sont infinies. *)

Lemma infseq_all_seq_inf:
  forall a, infseq a -> all_seq_inf a.
Proof.
  intros. unfold all_seq_inf. intros.
  destruct (@infseq_inv b) as (c & Rbc & _). eapply infseq_star_inv; eauto.
  exists c; auto.
Qed.

End SEQUENCES.



