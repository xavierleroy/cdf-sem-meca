(** Calcul de plus petits points fixes, en suivant le théorème de Knaster-Tarski. *)

From Coq Require Import Extraction ExtrOcamlBasic.

Section KNASTER_TARSKI.

(** On se place dans un type [A] muni d'une égalité décidable [eq]
    et d'un ordre partiel [le]. *)

Variable A: Type.

Variable eq: A -> A -> Prop.
Variable eq_dec: forall (x y: A), {eq x y} + {~eq x y}.

Variable le: A -> A -> Prop.
Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.
Hypothesis eq_le: forall x y, eq x y -> le y x.

(** Voici l'ordre strict induit par [le].  Nous supposons qu'il est bien fondé:
    toutes les suites strictement croissantes sont finies. *)

Definition gt (x y: A) := le y x /\ ~eq y x.

Hypothesis gt_wf: well_founded gt.

(** Soit [bot] un élément minimal de [A]. *)

Variable bot: A.
Hypothesis bot_smallest: forall x, le bot x.

Section FIXPOINT.

(** Soit [F] une fonction croissante de [A] dans [A]. *)

Variable F: A -> A.
Hypothesis F_mon: forall x y, le x y -> le (F x) (F y).

Lemma iterate_acc:
  forall (x: A) (acc: Acc gt x) (PRE: le x (F x)) (NEQ: ~eq x (F x)), Acc gt (F x).
Proof.
  intros. apply Acc_inv with x; auto. split; auto.
Defined.

Lemma iterate_le:
  forall (x: A) (PRE: le x (F x)), le (F x) (F (F x)).
Proof.
  intros. apply F_mon. apply PRE.
Qed.

(** Nous itérons [F] en partant d'un pré-point fixe [x], c'est-à-dire un [x]
    tel que [le x (F x)].  La récurrence est structurelle sur une dérivation
    d'accessibilité [Acc gt x] de [x], c'est-à-dire sur la démonstration
    du fait que toutes les suites strictement croissantes issues de [x]
    sont finies.  Ceci garantit la terminaison de l'itération! *)

Fixpoint iterate (x: A) (acc: Acc gt x) (PRE: le x (F x)) {struct acc}: A :=
  let x' := F x in
  match eq_dec x x' with
  | left E => x
  | right NE => iterate x' (iterate_acc x acc PRE NE) (iterate_le x PRE)
  end.

(** Le point fixe s'obtient en itérant à partir de [bot]. *)

Definition fixpoint : A := iterate bot (gt_wf bot) (bot_smallest (F bot)).

(** Il satisfait l'équation de point fixe. *)

Lemma fixpoint_eq: eq fixpoint (F fixpoint).
Proof.
  assert (REC: forall x acc PRE, eq (iterate x acc PRE) (F (iterate x acc PRE))).
  { induction x using (well_founded_induction gt_wf). intros. destruct acc; cbn.
    destruct (eq_dec x (F x)).
    - auto.
    - apply H. split; auto.
  }
  apply REC.
Qed.

(** C'est le plus petit des post-points fixes. *)

Lemma fixpoint_smallest: forall z, le (F z) z -> le fixpoint z.
Proof.
  intros z LEz.
  assert (REC: forall x acc PRE, le x z -> le (iterate x acc PRE) z).
  { induction x using (well_founded_induction gt_wf). intros. destruct acc; cbn.
    destruct (eq_dec x (F x)).
    - auto.
    - apply H. split; auto.
      apply le_trans with (F z). apply F_mon; auto. apply LEz.
  }
  apply REC. apply bot_smallest.
Qed.

End FIXPOINT.

(** Si une fonction [F] est point à point plus petite qu'une fonction [G],
    le point fixe de [F] est plus petit que celui de [G]. *)

Section FIXPOINT_MON.

Variable F: A -> A.
Hypothesis F_mon: forall x y, le x y -> le (F x) (F y).
Variable G: A -> A.
Hypothesis G_mon: forall x y, le x y -> le (G x) (G y).
Hypothesis F_le_G: forall x, le (F x) (G x).

Theorem fixpoint_mon: le (fixpoint F F_mon) (fixpoint G G_mon).
Proof.
  apply fixpoint_smallest. 
  eapply le_trans. apply F_le_G. apply eq_le. apply fixpoint_eq.
Qed.

End FIXPOINT_MON.

End KNASTER_TARSKI.

(** Si on demande à Coq d'extraire le code OCaml correspondant à la définition
  de "fixpoint", on voit que les arguments supplémentaires [acc] et [PRE]
  ont disparu, car ils servent uniquement à montrer la terminaison.
  Le code OCaml est exactement celui que nous aurions écrit à la main! *)

Recursive Extraction fixpoint.

(** Résultat:
<<
(** val iterate : ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iterate eq_dec f x =
  let x' = f x in if eq_dec x x' then x else iterate eq_dec f x'

(** val fixpoint : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 -> 'a1) -> 'a1 **)

let fixpoint eq_dec bot f =
  iterate eq_dec f bot
>>
*)
