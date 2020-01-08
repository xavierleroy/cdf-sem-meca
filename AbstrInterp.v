From Coq Require Import ZArith Psatz Bool String List FMaps Wellfounded Program.Equality.
From CDF Require Import Sequences IMP.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 1. Interface of abstract domains. *)

(** The analyzer operates over abstract values: compile-time approximations
  of sets of integer values.  We specify the type of abstract values
  and the associated operations as a Coq module interface. *)

Module Type VALUE_ABSTRACTION.

(** The type of abstract values. *)
  Variable t: Type.

(** [In n v] holds if the integer [n] belongs to the set represented
    by the abstract value [v]. *)

  Variable In: Z -> t -> Prop.

(** Abstract values are naturally ordered by inclusion. *)
  Definition le (v1 v2: t) : Prop :=
    forall n, In n v1 -> In n v2.

(** [ble] is a boolean function that approximates the [le] relation. *)
  Variable ble: t -> t -> bool.
  Hypothesis ble_1: forall v1 v2, ble v1 v2 = true -> le v1 v2.

(** [const n] returns the abstract value for the singleton set [{n}]. *)
  Variable const: Z -> t.
  Hypothesis const_1: forall n, In n (const n).

(** [bot] represents the empty set of integers. *)
  Variable bot: t.
  Hypothesis bot_1: forall n, ~(In n bot).

(** [top] represents the set of all integers. *)
  Variable top: t.
  Hypothesis top_1: forall n, In n top.

(** [join] computes an upper bound (union). *)
  Variable join: t -> t -> t.
  Hypothesis join_1:
    forall n v1 v2, In n v1 -> In n (join v1 v2).
  Hypothesis join_2:
    forall n v1 v2, In n v2 -> In n (join v1 v2).

(** [meet] computes a lower bound (intersection). *)
  Variable meet: t -> t -> t.
  Hypothesis meet_1:
    forall n v1 v2, In n v1 -> In n v2 -> In n (meet v1 v2).

(** Abstract counterpart of the [+] and [-] operations. *)
  Variable add: t -> t -> t.
  Hypothesis add_1:
    forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1+n2) (add v1 v2).

  Variable sub: t -> t -> t.
  Hypothesis sub_1:
    forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1-n2) (sub v1 v2).

(** A boolean-valued function that approximates the [In] predicate. *)

  Variable test_In: Z -> t -> bool.
  Hypothesis test_In_1:
    forall n v, In n v -> test_In n v = true.

(** Abstract operators for inverse analysis of comparisons.
  Consider a test [a1 = a2] in the program, which we know evaluates to [true].
  Let [v1] be an abstraction of [a1] and [v2] an abstraction of [a2].
  [eq_inv v1 v2] returns a pair of abstract values [v1', v2'].
  [v1'] is a (possibly more precise) abstraction for [a1], taking into
  account the fact that [a1 = a2].  Likewise for [v2'] and [a2]. *)

  Variable eq_inv: t -> t -> t * t.
  Hypothesis eq_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 = n2 ->
    In n1 (fst (eq_inv a1 a2)) /\ In n2 (snd (eq_inv a1 a2)).

  Variable ne_inv: t -> t -> t * t.
  Hypothesis ne_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <> n2 ->
    In n1 (fst (ne_inv a1 a2)) /\ In n2 (snd (ne_inv a1 a2)).

  Variable le_inv: t -> t -> t * t.
  Hypothesis le_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <= n2 ->
    In n1 (fst (le_inv a1 a2)) /\ In n2 (snd (le_inv a1 a2)).

  Variable gt_inv: t -> t -> t * t.
  Hypothesis gt_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 > n2 ->
    In n1 (fst (gt_inv a1 a2)) /\ In n2 (snd (gt_inv a1 a2)).

(** Abstract operators for inverse analysis of expressions.
  Consider an addition expression [a1 + a2].
  Let [v1] be an abstraction of [a1]
      [v2] an abstraction of [a2]
      [v] an abstraction for the result of [a1 + a2], 
      possibly more precise than [add v1 v2].
  Then, [add_inv v1 v2 v] returns a pair of abstract values [v1', v2']
  that are (possibly more precise) abstractions for [a1] and [a2]. *)

  Variable add_inv: t -> t -> t -> t * t.
  Hypothesis add_inv_1:
    forall n1 n2 v1 v2 v,
    In n1 v1 -> In n2 v2 -> In (n1+n2) v ->
    In n1 (fst (add_inv v1 v2 v)) /\ In n2 (snd (add_inv v1 v2 v)).

  Variable sub_inv: t -> t -> t -> t * t.
  Hypothesis sub_inv_1:
    forall n1 n2 v1 v2 v,
    In n1 v1 -> In n2 v2 -> In (n1-n2) v ->
    In n1 (fst (sub_inv v1 v2 v)) /\ In n2 (snd (sub_inv v1 v2 v)).

(** [widen v1 v2] returns a majorant of [v2],
    chosen so that the convergence of fixpoint iteration is accelerated. *)
  Variable widen: t -> t -> t.
  Hypothesis widen_1: forall v1 v2, le v2 (widen v1 v2).

End VALUE_ABSTRACTION.

(** Similarly, we define the interface for abstractions of concrete states. *)

Module Type STATE_ABSTRACTION.

  Declare Module V: VALUE_ABSTRACTION.

  Variable t: Type.

  Variable get: t -> ident -> V.t.
  Variable set: t -> ident -> V.t -> t.

  Definition In (st: store) (s: t) : Prop :=
    forall x, V.In (st x) (get s x).

  Hypothesis set_1:
    forall id n st v s,
    V.In n v -> In st s -> In (update id n st) (set s id v).

  Definition le (s1 s2: t) : Prop :=
    forall st, In st s1 -> In st s2.

  Variable ble: t -> t -> bool.
  Hypothesis ble_1: forall s1 s2, ble s1 s2 = true -> le s1 s2.

  Variable bot: t.
  Hypothesis bot_1: forall s, ~(In s bot).

  Variable top: t.
  Hypothesis top_1: forall s, In s top.

  Variable join: t -> t -> t.
  Hypothesis join_1:
    forall st s1 s2, In st s1 -> In st (join s1 s2).
  Hypothesis join_2:
    forall st s1 s2, In st s2 -> In st (join s1 s2).

  Variable widen: t -> t -> t.
  Hypothesis widen_1: forall v1 v2, le v2 (widen v1 v2).

End STATE_ABSTRACTION.

(** 2. The generic analyzer. *)

Module Analysis (V: VALUE_ABSTRACTION) (S: STATE_ABSTRACTION with Module V := V).

(** Fixpoint iteration with convergence acceleration. *)

Section FIXPOINT.

Variable F: S.t -> S.t.

(** Iterate [F] a bounded number of times, applying the widening operator
  at each iteration.  We stop if a post-fixpoint is encountered,
  or return [S.top] otherwise. *)

Fixpoint iter_up (n: nat) (s: S.t) : S.t :=
  match n with
  | O => S.top
  | S n1 => 
      let s' := F s in
      if S.ble s' s then s else iter_up n1 (S.widen s s')
  end.

(** We then iterate [F] some more times.  If [s] stops to be a post-fixpoint,
  we stop immediately. *)

Fixpoint iter_down (n: nat) (s: S.t) : S.t :=
  match n with
  | O => s
  | S n1 => 
      let s' := F s in
      if S.ble (F s') s' then iter_down n1 s' else s
  end.

Definition num_iter_up := 10%nat.
Definition num_iter_down := 3%nat.

Definition fixpoint (start: S.t) : S.t := 
  iter_down num_iter_down (iter_up num_iter_up start).

Lemma iter_up_post_fixpoint:
  forall n s, S.le (F (iter_up n s)) (iter_up n s).
Proof.
  induction n; simpl; intros.
  red; intros. apply S.top_1.
  remember (S.ble (F s) s). destruct b.
  apply S.ble_1. auto.
  apply IHn.
Qed.

Lemma iter_down_post_fixpoint:
  forall n s, S.le (F s) s -> S.le (F (iter_down n s)) (iter_down n s).
Proof.
  induction n; simpl; intros.
  auto.
  remember (S.ble (F (F s)) (F s)). destruct b.
  apply IHn. apply S.ble_1. auto.
  auto.
Qed.

Lemma fixpoint_ok:
  forall s, S.le (F (fixpoint s)) (fixpoint s).
Proof.
  intro start. unfold fixpoint.
  apply iter_down_post_fixpoint.
  apply iter_up_post_fixpoint.
Qed.

End FIXPOINT.

(** Abstract interpretation of arithmetic expressions. *)

Fixpoint abstr_eval (s: S.t) (a: aexp) : V.t :=
  match a with
  | CONST n => V.const n
  | VAR x => S.get s x
  | PLUS a1 a2 => V.add (abstr_eval s a1) (abstr_eval s a2)
  | MINUS a1 a2 => V.sub (abstr_eval s a1) (abstr_eval s a2)
  end.

(** Inverse analysis of arithmetic expressions.  Assuming that the
  result of [a] matches the abstract value [res], what do we learn
  about the values of variables occurring in [a]?  Whatever we learn
  is used to refine the abstract values of these variables. *)

Fixpoint assume_eval (s: S.t) (a: aexp) (res: V.t) : S.t :=
  match a with
  | CONST n => if V.test_In n res then s else S.bot
  | VAR x => S.set s x (V.meet res (S.get s x))
  | PLUS a1 a2 =>
      let (res1, res2) := V.add_inv (abstr_eval s a1) (abstr_eval s a2) res in
      assume_eval (assume_eval s a1 res1) a2 res2
  | MINUS a1 a2 =>
      let (res1, res2) := V.sub_inv (abstr_eval s a1) (abstr_eval s a2) res in
      assume_eval (assume_eval s a1 res1) a2 res2
  end.

(** Inverse analysis of boolean expressions.  Assuming that the result of [b]
  is equal to the boolean [res], what do we learn about the values
  of variables occurring in [b]? *)

Fixpoint assume_test (s: S.t) (b: bexp) (res: bool) : S.t :=
  match b with
  | TRUE => if res then s else S.bot
  | FALSE => if res then S.bot else s
  | EQUAL a1 a2 =>
      let (res1, res2) :=
        if res
        then V.eq_inv (abstr_eval s a1) (abstr_eval s a2)
        else V.ne_inv (abstr_eval s a1) (abstr_eval s a2) in
      assume_eval (assume_eval s a1 res1) a2 res2
  | LESSEQUAL a1 a2 =>
      let (res1, res2) :=
        if res
        then V.le_inv (abstr_eval s a1) (abstr_eval s a2)
        else V.gt_inv (abstr_eval s a1) (abstr_eval s a2) in
      assume_eval (assume_eval s a1 res1) a2 res2
  | NOT b1 =>
      assume_test s b1 (negb res)
  | AND b1 b2 =>
      if res
      then assume_test (assume_test s b1 true) b2 true
      else S.join (assume_test s b1 false) (assume_test s b2 false)
  end.

(** Abstract interpretation of commands.  We use [assume_test] every time
  a conditional branch is taken / not taken. *)

Fixpoint abstr_interp (s: S.t) (c: com) : S.t :=
  match c with
  | SKIP => s
  | ASSIGN x a => S.set s x (abstr_eval s a)
  | SEQ c1 c2 => abstr_interp (abstr_interp s c1) c2
  | IFTHENELSE b c1 c2 =>
      S.join (abstr_interp (assume_test s b true) c1)
             (abstr_interp (assume_test s b false) c2)
  | WHILE b c =>
      let s' :=
        fixpoint
         (fun x => S.join s (abstr_interp (assume_test x b true) c))
         s in
      assume_test s' b false
  end.

(** Soundness of abstract interpretation of expressions.  No change. *)

Lemma abstr_eval_sound:
  forall st s, S.In st s ->
  forall a, V.In (aeval a st) (abstr_eval s a).
Proof.
  induction a; simpl.
  apply V.const_1.
  apply H.
  apply V.add_1; auto.
  apply V.sub_1; auto.
Qed.

(** Soundness of inverse analysis of expressions. *)

Lemma assume_eval_sound:
  forall st a s res,
  S.In st s -> V.In (aeval a st) res ->
  S.In st (assume_eval s a res).
Proof.
  induction a; simpl; intros.
- (* CONST *)
  rewrite (V.test_In_1 n); auto.
- (* VAR *)
  assert (A: S.In (update x (st x) st) (S.set s x (V.meet res (S.get s x)))).
  { apply S.set_1. apply V.meet_1. auto. apply H. auto. }
  intros y. specialize (A y). unfold update in A. destruct (string_dec x y); congruence.
- (* PLUS *)
  specialize (V.add_inv_1 (aeval a1 st) (aeval a2 st) (abstr_eval s a1) (abstr_eval s a2) res).
  destruct (V.add_inv (abstr_eval s a1) (abstr_eval s a2) res) as [res1 res2].
  simpl; intros. destruct H1; auto using abstr_eval_sound.
- (* MINUS *)
  specialize (V.sub_inv_1 (aeval a1 st) (aeval a2 st) (abstr_eval s a1) (abstr_eval s a2) res).
  destruct (V.sub_inv (abstr_eval s a1) (abstr_eval s a2) res) as [res1 res2].
  simpl; intros. destruct H1; auto using abstr_eval_sound.
Qed.

(** Soundness of inverse analysis of boolean expressions. *)

Lemma assume_test_sound:
  forall st b s res,
  S.In st s -> beval b st = res ->
  S.In st (assume_test s b res).
Proof.
  induction b; simpl; intros.
- (* TRUE *)
  subst res; auto.
- (* FALSE *)
  subst res; auto.
- (* EQUAL *)
  set (r := if res
            then V.eq_inv (abstr_eval s a1) (abstr_eval s a2)
            else V.ne_inv (abstr_eval s a1) (abstr_eval s a2)).
  assert (A: V.In (aeval a1 st) (fst r) /\ V.In (aeval a2 st) (snd r)).
  { unfold r; destruct res.
  - apply V.eq_inv_1; auto using abstr_eval_sound.
    apply Z.eqb_eq; auto.
  - apply V.ne_inv_1; auto using abstr_eval_sound.
    apply Z.eqb_neq; auto.
  }
  destruct A as [A1 A2]. destruct r as [r1 r2]. auto using assume_eval_sound.
- (* LESSEQUAL *)
  set (r := if res
            then V.le_inv (abstr_eval s a1) (abstr_eval s a2)
            else V.gt_inv (abstr_eval s a1) (abstr_eval s a2)).
  assert (A: V.In (aeval a1 st) (fst r) /\ V.In (aeval a2 st) (snd r)).
  { unfold r; destruct res.
  - apply V.le_inv_1; auto using abstr_eval_sound.
    apply Z.leb_le; auto.
  - apply V.gt_inv_1; auto using abstr_eval_sound.
    apply Z.leb_nle in H0. lia.
  }
  destruct A as [A1 A2]. destruct r as [r1 r2]. auto using assume_eval_sound.
- (* NOT *)
  apply IHb; auto. rewrite <- H0. rewrite negb_involutive; auto. 
- (* AND *)
  destruct res.
  + (* AND, true *)
    destruct (andb_prop _ _ H0). 
    auto.
  + (* AND, false *)
    destruct (andb_false_elim _ _ H0).
    apply S.join_1. auto.
    apply S.join_2. auto.
Qed.

(** Soundness of abstract interpretation of commands. *)

Theorem abstr_interp_sound:
  forall c st st' s,
  S.In st s ->
  cexec st c st' ->
  S.In st' (abstr_interp s c).
Proof.
  induction c; intros st st' s MATCH EVAL; simpl.
- (* SKIP *)
  inversion EVAL; subst. auto.
- (* ASSIGN *)
  inversion EVAL; subst. apply S.set_1. apply abstr_eval_sound; auto. auto. 
- (* SEQ *)
  inversion EVAL; subst.
  apply IHc2 with s'. apply IHc1 with st. auto. auto. auto.
- (* IFTHENELSE *)
  inversion EVAL; subst.
  destruct (beval b st) eqn:B.
  + (* true *)
    apply S.join_1. apply IHc1 with st; auto. apply assume_test_sound; auto.
  + (* false *)
    apply S.join_2. apply IHc2 with st; auto. apply assume_test_sound; auto.
- (* WHILE *)
  set (F := fun x => S.join s (abstr_interp (assume_test x b true) c)).
  set (s' := fixpoint F s).
  assert (FIX: S.le (F s') s').
  { apply fixpoint_ok. }
  assert (INNER: forall st1 c1 st2,
                    cexec st1 c1 st2 ->
                    c1 = WHILE b c ->
                    S.In st1 s' ->
                    S.In st2 (assume_test s' b false)).
  { induction 1; intro EQ; inversion EQ; subst; intros.
  + (* WHILE stop *)
    apply assume_test_sound; auto.
  + (* WHILE loop *)
    apply IHcexec2; auto.
    apply FIX. unfold F.
    apply S.join_2. apply IHc with s0. apply assume_test_sound; auto. auto.
  }
  eapply INNER; eauto.
  apply FIX. unfold F. apply S.join_1. auto.
Qed.

End Analysis.

(** Analyse d'intervalles *)

Inductive zinf : Type := Fin (h: Z) | Inf.

Coercion Fin : Z >-> zinf.

Module Zinf.
  Definition In (n: Z) (v: zinf) : Prop :=
    match v with Fin h => n <= h | Inf => True end.

  Lemma In_mono: forall n1 n2 v, n1 <= n2 -> In n2 v -> In n1 v.
  Proof.
    unfold In; destruct v; intros. lia. auto.
  Qed.

  Definition le (v1 v2: zinf) : Prop :=
    forall n, In n v1 -> In n v2.

  Definition ble (v1 v2: zinf) : bool :=
    match v1, v2 with _, Inf => true | Inf, _ => false | Fin h1, Fin h2 => h1 <=? h2 end.

  Lemma ble_1: forall v1 v2, ble v1 v2 = true -> le v1 v2.
  Proof.
    unfold ble, le, In; intros.
    destruct v1, v2; auto.
    apply Z.leb_le in H. lia.
    discriminate.
  Qed.

  Lemma ble_2: forall v1 v2, le v1 v2 -> ble v1 v2 = true.
  Proof.
    unfold ble, le, In; intros.
    destruct v2.
  - destruct v1.
    + apply Z.leb_le. apply H; lia.
    + assert (h + 1 <= h) by auto. lia.
  - destruct v1; auto.
  Qed.

  Definition max (v1 v2: zinf) : zinf :=
    match v1, v2 with Inf, _ => Inf | _, Inf => Inf | Fin h1, Fin h2 => Fin (Z.max h1 h2) end.

  Lemma max_1: forall n v1 v2, In n v1 -> In n (max v1 v2).
  Proof.
    unfold In, max; intros. destruct v1; auto. destruct v2; auto. lia.
  Qed.

  Lemma max_2: forall n v1 v2, In n v2 -> In n (max v1 v2).
  Proof.
    unfold In, max; intros. destruct v1; auto. destruct v2; auto. lia.
  Qed.

  Definition min (v1 v2: zinf) : zinf :=
    match v1, v2 with Inf, _ => v2 | _, Inf => v1 | Fin h1, Fin h2 => Fin (Z.min h1 h2) end.

  Lemma min_1: forall n v1 v2, In n v1 -> In n v2 -> In n (min v1 v2).
  Proof.
    unfold In, min; intros. destruct v1; auto. destruct v2; auto. lia.
  Qed.

  Definition add (v1 v2: zinf) : zinf :=
    match v1, v2 with Inf, _ => Inf | _, Inf => Inf | Fin h1, Fin h2 => Fin (h1 + h2) end.

  Lemma add_1: forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1 + n2) (add v1 v2).
  Proof.
    unfold In, add; intros. destruct v1; auto. destruct v2; auto. lia.
  Qed.

  Definition Inb (n: Z) (v: zinf) : bool :=
    match v with Fin h => n <=? h | Inf => true end.

  Lemma Inb_1:
    forall n v, In n v -> Inb n v = true.
  Proof.
    unfold In, Inb; intros. destruct v; auto. apply Z.leb_le; auto.
  Qed.

  Definition pred (v: zinf) : zinf :=
    match v with Inf => Inf | Fin n => Fin (n - 1) end.

  Lemma pred_1: forall n v, In n v -> In (n - 1) (pred v).
  Proof.
    unfold pred, In; intros; destruct v; auto. lia.
  Qed.

  Definition widen (v1 v2: zinf) : zinf :=
    (* if bound increases strictly from v1 to v2, go to Inf, else keep v2 *)
    if ble v2 v1 then v2 else Inf.

  Lemma widen_1: forall v1 v2, le v2 (widen v1 v2).
  Proof.
    unfold widen; intros. destruct (ble v2 v1) eqn:LE.
    red; auto.
    red; unfold In; auto.
  Qed.
 
End Zinf.

Module Intervals <: VALUE_ABSTRACTION.

(** The type of abstract values. *)
  Record t_ : Type := intv { low: zinf; high: zinf }.
  Definition t := t_.

(** [In n v] holds if the integer [n] belongs to the set represented
    by the abstract value [v]. *)

  Definition In (n: Z) (v: t) : Prop :=
    Zinf.In n (high v) /\ Zinf.In (-n) (low v).

(** Abstract values are naturally ordered by inclusion. *)
  Definition le (v1 v2: t) : Prop :=
    forall n, In n v1 -> In n v2.

(** [const n] returns the abstract value for the singleton set [{n}]. *)
  Definition const (n: Z) : t := {| low := Fin (-n); high := Fin n |}.

  Lemma const_1: forall n, In n (const n).
  Proof.
    unfold const, In, Zinf.In; intros; cbn. lia.
  Qed.

(** [bot] represents the empty set of integers. *)
  Definition bot: t := {| low := Fin 0; high := Fin (-1) |}.

  Lemma bot_1: forall n, ~(In n bot).
  Proof.
    unfold bot, In, Zinf.In; intros; cbn. lia.
  Qed.

  Definition isempty (v: t) : bool :=
    match v with 
    | {| low := Fin l; high := Fin h |} => h <? (-l)
    | _ => false
    end.

  Lemma isempty_1: forall v n, isempty v = true -> In n v -> False.
  Proof.
    unfold isempty, In; intros. destruct v as [[l|] [h|]]; try discriminate.
    apply Z.ltb_lt in H. cbn in H0. lia.
  Qed.

(** [ble] is a boolean function that approximates the [le] relation. *)
  Definition ble (v1 v2: t) : bool :=
    isempty v1 || (Zinf.ble (high v1) (high v2) && Zinf.ble (low v1) (low v2)).

  Lemma ble_1: forall v1 v2, ble v1 v2 = true -> le v1 v2.
  Proof.
    unfold ble, le, In; intros.
    destruct (isempty v1) eqn:E.
    elim (isempty_1 _ _ E H0).
    simpl in H. apply andb_prop in H. destruct H as [B1 B2].
    apply Zinf.ble_1 in B1. apply Zinf.ble_1 in B2.
    intuition.
  Qed.

(*
  Lemma ble_2: forall v1 v2, le v1 v2 -> ble v1 v2 = true.
  Proof.
    unfold ble, isempty, le, In, Zinf.ble; intros.
    destruct v1 as [ [ l1 | ] [ h1 | ]]; cbn in *.
  - destruct (Z.ltb_spec h1 (-l1)); auto.
    apply andb_true_intro; split.
    destruct (high v2) as [ h2 | ]; auto. apply Z.leb_le. apply H. lia.
    destruct (low v2) as [ l2 | ]; auto.
    apply Z.leb_le. replace l1 with (- - l1) by lia. apply H. lia.
  -  
*)


(** [top] represents the set of all integers. *)
  Definition top: t := {| low := Inf; high := Inf |}.

  Lemma top_1: forall n, In n top.
  Proof.
    intros. split; exact I.
  Qed.

(** [join] computes an upper bound (union). *)
  Definition join (v1 v2: t) : t :=
    {| low := Zinf.max (low v1) (low v2);
       high := Zinf.max (high v1) (high v2) |}.

  Lemma join_1:
    forall n v1 v2, In n v1 -> In n (join v1 v2).
  Proof.
    unfold In, join; intros; cbn. split; apply Zinf.max_1; tauto.
  Qed.

  Lemma join_2:
    forall n v1 v2, In n v2 -> In n (join v1 v2).
  Proof.
    unfold In, join; intros; cbn. split; apply Zinf.max_2; tauto.
  Qed.

(** [meet] computes a lower bound (intersection). *)

  Definition meet (v1 v2: t) : t :=
    {| low := Zinf.min (low v1) (low v2);
       high := Zinf.min (high v1) (high v2) |}.

  Lemma meet_1:
    forall n v1 v2, In n v1 -> In n v2 -> In n (meet v1 v2).
  Proof.
    unfold In, meet; intros; cbn. split; apply Zinf.min_1; tauto. 
  Qed.

(** Abstract counterpart of the [+] and [-] operations. *)
  Definition add (v1 v2: t) : t :=
    if isempty v1 || isempty v2 then bot else
    {| low := Zinf.add (low v1) (low v2);
       high := Zinf.add (high v1) (high v2) |}.

  Lemma add_1:
    forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1 + n2) (add v1 v2).
  Proof.
    unfold add; intros.
    destruct (isempty v1) eqn:E1. elim (isempty_1 v1 n1); auto.
    destruct (isempty v2) eqn:E2. elim (isempty_1 v2 n2); auto.
    destruct H; destruct H0; split; cbn.
    apply Zinf.add_1; auto.
    replace (- (n1 + n2)) with ((-n1) + (-n2)) by lia. apply Zinf.add_1; auto.
  Qed.

  Definition opp (v: t) : t := {| low := high v; high := low v |}.

  Lemma opp_1:
    forall n v, In n v -> In (-n) (opp v).
  Proof.
    unfold In, opp; intros; cbn. replace (- - n) with n by lia. tauto.
  Qed.

  Definition sub (v1 v2: t) : t := add v1 (opp v2).

  Lemma sub_1:
    forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1 - n2) (sub v1 v2).
  Proof.
    intros. apply add_1; auto. apply opp_1; auto.
  Qed.

(** A boolean-valued function that approximates the [In] predicate. *)

  Definition test_In (n: Z) (v: t) : bool :=
    Zinf.Inb n (high v) && Zinf.Inb (-n) (low v).

  Lemma test_In_1:
    forall n v, In n v -> test_In n v = true.
  Proof.
    unfold In, test_In; intros.
    apply andb_true_intro; split; apply Zinf.Inb_1; tauto. 
  Qed.

(** Abstract operators for inverse analysis of comparisons.
  Consider a test [a1 = a2] in the program, which we know evaluates to [true].
  Let [v1] be an abstraction of [a1] and [v2] an abstraction of [a2].
  [eq_inv v1 v2] returns a pair of abstract values [v1', v2'].
  [v1'] is a (possibly more precise) abstraction for [a1], taking into
  account the fact that [a1 = a2].  Likewise for [v2'] and [a2]. *)

  Definition eq_inv (v1 v2: t) : t * t := (meet v1 v2, meet v1 v2).

  Lemma eq_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 = n2 ->
    In n1 (fst (eq_inv a1 a2)) /\ In n2 (snd (eq_inv a1 a2)).
  Proof.
    intros; cbn. subst n2. split; apply meet_1; auto.
  Qed.

  Definition ne_inv (v1 v2: t) : t * t := (v1, v2).

  Lemma ne_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <> n2 ->
    In n1 (fst (ne_inv a1 a2)) /\ In n2 (snd (ne_inv a1 a2)).
  Proof.
    intros; cbn; auto.
  Qed.

  Definition le_inv (v1 v2: t) : t * t :=
    (* v1's upper bound is at most v2's upper bound
       v2's lower bound is at least v1's lower bound *)
    ( {| low := low v1; high := Zinf.min (high v1) (high v2) |},
      {| low := Zinf.min (low v1) (low v2); high := high v2 |} ).

  Lemma le_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <= n2 ->
    In n1 (fst (le_inv a1 a2)) /\ In n2 (snd (le_inv a1 a2)).
  Proof.
    unfold In, le_inv; intros; cbn.
    intuition auto; apply Zinf.min_1; auto.
    apply Zinf.In_mono with n2; auto.
    apply Zinf.In_mono with (-n1); auto. lia.
  Qed.

  Definition gt_inv (v1 v2: t) : t * t :=
    (* v1's lower bound is at least v2's lower bound + 1.
       v2's upper bound is at most v1's upper bound - 1. *)
    ( {| low := Zinf.min (low v1) (Zinf.pred (low v2)); high := high v1 |},
      {| low := low v2; high := Zinf.min (high v2) (Zinf.pred (high v1)) |} ).

  Lemma gt_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 > n2 ->
    In n1 (fst (gt_inv a1 a2)) /\ In n2 (snd (gt_inv a1 a2)).
  Proof.
    unfold In, gt_inv; intros; cbn.
    intuition auto; apply Zinf.min_1; auto.
    apply Zinf.In_mono with ((-n2) - 1). lia. apply Zinf.pred_1; auto.
    apply Zinf.In_mono with (n1 - 1). lia. apply Zinf.pred_1; auto.
  Qed.

(** Abstract operators for inverse analysis of expressions.
  Consider an addition expression [a1 + a2].
  Let [v1] be an abstraction of [a1]
      [v2] an abstraction of [a2]
      [v] an abstraction for the result of [a1 + a2], 
      possibly more precise than [add v1 v2].
  Then, [add_inv v1 v2 v] returns a pair of abstract values [v1', v2']
  that are (possibly more precise) abstractions for [a1] and [a2]. *)

  Definition add_inv (v1 v2 vres: t) : t * t :=
    (meet v1 (sub vres v2), meet v2 (sub vres v1)).

  Lemma add_inv_1:
    forall n1 n2 v1 v2 v,
    In n1 v1 -> In n2 v2 -> In (n1+n2) v ->
    In n1 (fst (add_inv v1 v2 v)) /\ In n2 (snd (add_inv v1 v2 v)).
  Proof.
    unfold add_inv; intros; cbn; split; apply meet_1; auto.
  - replace n1 with ((n1 + n2) - n2) by lia. apply sub_1; auto.
  - replace n2 with ((n1 + n2) - n1) by lia. apply sub_1; auto.
  Qed.

  Definition sub_inv (v1 v2 vres: t) : t * t :=
    (meet v1 (add vres v2), meet v2 (sub v1 vres)).

  Lemma sub_inv_1:
    forall n1 n2 v1 v2 v,
    In n1 v1 -> In n2 v2 -> In (n1-n2) v ->
    In n1 (fst (sub_inv v1 v2 v)) /\ In n2 (snd (sub_inv v1 v2 v)).
  Proof.
    unfold sub_inv; intros; cbn; split; apply meet_1; auto.
  - replace n1 with ((n1 - n2) + n2) by lia. apply add_1; auto.
  - replace n2 with (n1 - (n1 - n2)) by lia. apply sub_1; auto.
  Qed.

(** [widen v1 v2] returns a majorant of [v2],
    chosen so that the convergence of fixpoint iteration is accelerated. *)
  Definition widen (v1 v2: t) : t :=
    {| low := Zinf.widen (low v1) (low v2); high := Zinf.widen (high v1) (high v2) |}.

  Lemma widen_1: forall v1 v2, le v2 (widen v1 v2).
  Proof.
    unfold le, widen, In; intros; cbn. 
    split; apply Zinf.widen_1; tauto.
  Qed.

  Remark Zinf_ble_Inf: forall z, Zinf.ble z Inf = true.
  Proof.
    destruct z; auto.
  Qed.

  Definition Zinf_measure (z: zinf) : nat :=
    match z with Inf => 0%nat | Fin _ => 1%nat end.

  Lemma Zinf_ble_measure_1: forall x y,
    Zinf.ble x y = true -> (Zinf_measure y <= Zinf_measure x)%nat.
  Proof.
    destruct x, y; cbn; intros; auto. discriminate.
  Qed.

End Intervals.


(*****

Inductive t : Type :=
    | Top
    | Inf (h: Z)
    | Sup (l: Z)
    | Int (l h: Z).

(** [In n v] holds if the integer [n] belongs to the set represented
    by the abstract value [v]. *)

  Definition In (n: Z) (v: t) : Prop :=
    match v with
    | Top => True
    | Inf h => n <= h
    | Sup l => l <= n
    | Int l h => l <= n <= h
    end.

(** Abstract values are naturally ordered by inclusion. *)
  Definition le (v1 v2: t) : Prop :=
    forall n, In n v1 -> In n v2.

(** [ble] is a boolean function that approximates the [le] relation. *)
  Definition ble (v1 v2: t) : bool :=
    match v1, v2 with
    | _, Top => true
    | Top, _ => false
    | Inf h, Inf h' => h <=? h'
    | Inf h, _ => false
    | Sup l, Sup l' => l' <=? l
    | Sup l, _ => false
    | Int l1 h1, Int l2 h2 => (l2 <=? l1) && (h1 <=? h2)
    | Int l1 h1, Inf h' => h1 <=? h'
    | Int l1 h1, Sup l' => l' <=? l1
    end.

  Lemma ble_1: forall v1 v2, ble v1 v2 = true -> le v1 v2.
  Proof.
    unfold ble, le, In; intros v1 v2 B n I.
    destruct v2; auto; destruct v1; try discriminate;
    try (apply Z.leb_le in B); try lia.
    apply andb_prop in B; destruct B as [B1 B2].
    apply Z.leb_le in B1; apply Z.leb_le in B2. lia.
  Qed.

(** [const n] returns the abstract value for the singleton set [{n}]. *)
  Definition const (n: Z) : t := Int n n.

  Lemma const_1: forall n, In n (const n).
  Proof.
    unfold const, In; intros. lia.
  Qed.

(** [bot] represents the empty set of integers. *)
  Definition bot: t := Int 1 0.

  Lemma bot_1: forall n, ~(In n bot).
  Proof.
    unfold bot, In; intros. lia.
  Qed.

  Definition isempty (v: t) : bool :=
    match v with Int l h => h <? l | _ => false end.

  Lemma isempty_1: forall v n, isempty v = true -> In n v -> False.
  Proof.
    unfold isempty, In; intros. destruct v; try discriminate.
    apply Z.ltb_lt in H. lia.
  Qed.

(** [top] represents the set of all integers. *)
  Definition top: t := Top.

  Lemma top_1: forall n, In n top.
  Proof.
    intros. exact I.
  Qed.

(** [join] computes an upper bound (union). *)
  Definition join (v1 v2: t) : t :=
    match v1, v2 with
    | Int l1 h1, Int l2 h2 => Int (Z.min l1 l2) (Z.max h1 h2)
    | Int l1 h1, Sup l2 => Sup (Z.min l1 l2)
    | Sup l1, Int l2 h2 => Sup (Z.min l1 l2)
    | Sup l1, Sup l2 => Sup (Z.min l1 l2)
    | Int l1 h1, Inf h2 => Inf (Z.max h1 h2)
    | Inf h1, Int l2 h2 => Inf (Z.max h1 h2)
    | Inf h1, Inf h2 => Inf (Z.max h1 h2)
    | _, _ => Top
    end.

  Lemma join_1:
    forall n v1 v2, In n v1 -> In n (join v1 v2).
  Proof.
    unfold In, join; intros; destruct v1, v2; auto; lia.
  Qed.

  Lemma join_2:
    forall n v1 v2, In n v2 -> In n (join v1 v2).
  Proof.
    unfold In, join; intros; destruct v1, v2; auto; lia.
  Qed.

(** [meet] computes a lower bound (intersection). *)
  Definition meet (v1 v2: t) : t :=
    match v1, v2 with
    | Top, _ => v2
    | _, Top => v1
    | Int l1 h1, Int l2 h2 => Int (Z.max l1 l2) (Z.min h1 h2)
    | Int l1 h1, Sup l2 => Int (Z.max l1 l2) h1
    | Sup l1, Int l2 h2 => Int (Z.max l1 l2) h2
    | Sup l1, Sup l2 => Sup (Z.max l1 l2)
    | Int l1 h1, Inf h2 => Int l1 (Z.min h1 h2)
    | Inf h1, Int l2 h2 => Int l2 (Z.min h1 h2)
    | Inf h1, Inf h2 => Inf (Z.min h1 h2)
    | Sup l1, Inf h2 => Int l1 h2
    | Inf h1, Sup l2 => Int l2 h1
    end.

  Lemma meet_1:
    forall n v1 v2, In n v1 -> In n v2 -> In n (meet v1 v2).
  Proof.
    unfold In, meet; intros; destruct v1, v2; cbn in *; auto; lia.
  Qed.

(** Abstract counterpart of the [+] and [-] operations. *)
  Definition add (v1 v2: t) : t :=
    if isempty v1 || isempty v2 then bot else
    match v1, v2 with
    | Int l1 h1, Int l2 h2 => Int (l1 + l2) (h1 + h2)
    | Int l1 h1, Sup l2 => Sup (l1 + l2)
    | Int l1 h1, Inf h2 => Inf (h1 + h2)
    | Sup l1, Int l2 h2 => Sup (l1 + l2)
    | Inf h1, Int l2 h2 => Inf (h1 + h2)
    | _, _ => Top
    end.

  Lemma add_1:
    forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1 + n2) (add v1 v2).
  Proof.
    unfold In, add; intros.
    destruct (isempty v1) eqn:E1. elim (isempty_1 v1 n1); auto.
    destruct (isempty v2) eqn:E2. elim (isempty_1 v2 n2); auto.
    cbn. destruct v1, v2; cbn in *; auto; lia.
  Qed.

  Definition opp (v: t) : t :=
    match v with
    | Int l h => Int (-h) (-l)
    | Sup l => Inf (-l)
    | Inf h => Sup (-h)
    | Top => Top
    end.

  Lemma opp_1:
    forall n v, In n v -> In (-n) (opp v).
  Proof.
    unfold In, opp; intros; destruct v; cbn in *; auto; lia.
  Qed.

  Definition sub (v1 v2: t) : t := add v1 (opp v2).

  Lemma sub_1:
    forall n1 n2 v1 v2, In n1 v1 -> In n2 v2 -> In (n1 - n2) (sub v1 v2).
  Proof.
    intros. apply add_1; auto. apply opp_1; auto.
  Qed.

(** A boolean-valued function that approximates the [In] predicate. *)

  Definition test_In (n: Z) (v: t) : bool :=
    match v with
    | Top => true
    | Inf h => n <=? h
    | Sup l => l <=? n
    | Int l h => (l <=? n) && (n <=? h)
    end.

  Lemma test_In_1:
    forall n v, In n v -> test_In n v = true.
  Proof.
    unfold In, test_In; intros; destruct v.
  - auto.
  - apply Z.leb_le; auto.
  - apply Z.leb_le; auto.
  - apply andb_true_intro; split; apply Z.leb_le; tauto.
  Qed.

(** Abstract operators for inverse analysis of comparisons.
  Consider a test [a1 = a2] in the program, which we know evaluates to [true].
  Let [v1] be an abstraction of [a1] and [v2] an abstraction of [a2].
  [eq_inv v1 v2] returns a pair of abstract values [v1', v2'].
  [v1'] is a (possibly more precise) abstraction for [a1], taking into
  account the fact that [a1 = a2].  Likewise for [v2'] and [a2]. *)

  Definition eq_inv (v1 v2: t) : t * t := (meet v1 v2, meet v1 v2).

  Lemma eq_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 = n2 ->
    In n1 (fst (eq_inv a1 a2)) /\ In n2 (snd (eq_inv a1 a2)).
  Proof.
    intros; cbn. subst n2. split; apply meet_1; auto.
  Qed.

  Definition ne_inv (v1 v2: t) : t * t := (v1, v2).

  Lemma ne_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <> n2 ->
    In n1 (fst (ne_inv a1 a2)) /\ In n2 (snd (ne_inv a1 a2)).
  Proof.
    intros; cbn; auto.
  Qed.

  Definition le_inv (v1 v2: t) : t * t :=
    (* v1's upper bound is at most v2's upper bound
       v2's lower bound is at least v1's lower bound *)
    match v1, v2 with
    | Int l1 h1, Int l2 h2 => (Int l1 (Z.min h1 h2), Int (Z.max l1 l2) h2)
    | Int l1 h1, Sup l2    => (v1, Sup (Z.max l1 l2))
    | Sup l1, Int l2 h2    => (v1, Int (Z.max l1 l2) h2)
    | Sup l1, Sup l2       => (v1, Sup (Z.max l1 l2))
    | Int l1 h1, Inf h2    => (Int l1 (Z.min h1 h2), v2)
    | Inf h1, Int l2 h2    => (Inf (Z.min h1 h2), v2)
    | _, _ => (v1, v2)
    end.

  Lemma le_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <= n2 ->
    In n1 (fst (le_inv a1 a2)) /\ In n2 (snd (le_inv a1 a2)).
  Proof.
    unfold In, le_inv; intros; destruct a1, a2; cbn; auto; lia.
  Qed.

  Definition gt_inv (v1 v2: t) :=
    let (v1', v2') := le_inv (add v2 (const 1)) v1 in (v2', v1').

  Lemma gt_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 > n2 ->
    In n1 (fst (gt_inv a1 a2)) /\ In n2 (snd (gt_inv a1 a2)).
  Proof.
    intros.
    destruct (le_inv_1 (n2 + 1) n1 (add a2 (const 1)) a1) as [A1 A2].
    auto using add_1, const_1.
    auto.
    lia.
    unfold gt_inv. destruct (le_inv (add a2 (const 1)) a1) as [v1' v2'] in *.
    cbn in *.
  

(** Abstract operators for inverse analysis of expressions.
  Consider an addition expression [a1 + a2].
  Let [v1] be an abstraction of [a1]
      [v2] an abstraction of [a2]
      [v] an abstraction for the result of [a1 + a2], 
      possibly more precise than [add v1 v2].
  Then, [add_inv v1 v2 v] returns a pair of abstract values [v1', v2']
  that are (possibly more precise) abstractions for [a1] and [a2]. *)

  Variable add_inv: t -> t -> t -> t * t.
  Hypothesis add_inv_1:
    forall n1 n2 v1 v2 v,
    In n1 v1 -> In n2 v2 -> In (n1+n2) v ->
    In n1 (fst (add_inv v1 v2 v)) /\ In n2 (snd (add_inv v1 v2 v)).

  Variable sub_inv: t -> t -> t -> t * t.
  Hypothesis sub_inv_1:
    forall n1 n2 v1 v2 v,
    In n1 v1 -> In n2 v2 -> In (n1-n2) v ->
    In n1 (fst (sub_inv v1 v2 v)) /\ In n2 (snd (sub_inv v1 v2 v)).

(** [widen v1 v2] returns a majorant of [v2],
    chosen so that the convergence of fixpoint iteration is accelerated. *)
  Variable widen: t -> t -> t.
  Hypothesis widen_1: forall v1 v2, le v2 (widen v1 v2).

End VALUE_ABSTRACTION.

*)


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

Module IdentMap := FMapWeakList.Make(Ident_Decidable).
Module IMFact := FMapFacts.WFacts(IdentMap).
Module IMProp := FMapFacts.WProperties(IdentMap).

Module StateAbstr (VA: VALUE_ABSTRACTION) <: STATE_ABSTRACTION with Module V := VA.

Module V := VA.

Inductive abstr_state : Type :=
  | Bot
  | Top_except (m: IdentMap.t V.t).

Definition t := abstr_state.

Definition get (s: t) (x: ident) : V.t :=
  match s with
  | Bot => V.bot
  | Top_except m =>
      match IdentMap.find x m with
      | None => V.top
      | Some v => v
      end
  end.

Definition In (st: store) (s: t) : Prop :=
  forall x, V.In (st x) (get s x).

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

Definition set (s: t) (x: ident) (v: V.t) : t :=
  match s with
  | Bot => Bot
  | Top_except m => Top_except (IdentMap.add x v m)
  end.

Lemma set_1:
    forall id n st v s,
    V.In n v -> In st s -> In (update id n st) (set s id v).
Proof.
  unfold In, get, set; intros. destruct s.
- elim (bot_1 _ H0).
- rewrite IMFact.add_o. change IdentMap.E.eq_dec with string_dec. unfold update.
  destruct (string_dec id x); auto.
Qed. 

Definition le (s1 s2: t) : Prop :=
  forall st, In st s1 -> In st s2.

Definition ble (s1 s2: t) : bool :=
  match s1, s2 with
  | Bot, _ => true
  | _, Bot => false
  | Top_except m1, Top_except m2 =>
      IMProp.for_all (fun x v => V.ble (get s1 x) v) m2
  end.

Lemma ble_1: forall s1 s2, ble s1 s2 = true -> le s1 s2.
Proof.
  unfold ble, le; intros.
  destruct s1 as [ | m1].
- elim (bot_1 _ H0).
- destruct s2 as [ | m2]. discriminate.
  red; cbn; intros. destruct (IdentMap.find x m2) as [v2|] eqn:F2.
  + apply IdentMap.find_2 in F2. eapply IMProp.for_all_iff in H; eauto.
    apply V.ble_1 in H. apply H. apply H0.
    hnf. intros; subst x0. hnf; intros. subst x0. auto.
  + apply V.top_1.
Qed.

Definition join_aux (ov1 ov2: option V.t) : option V.t :=
  match ov1, ov2 with
  | Some v1, Some v2 => Some (V.join v1 v2)
  | _, _ => None
  end.

Definition join (s1 s2: t) : t :=
  match s1, s2 with
  | Bot, _ => s2
  | _, Bot => s1
  | Top_except m1, Top_except m2 =>
      Top_except (IdentMap.map2 join_aux m1 m2)
  end.

Lemma join_1:
    forall st s1 s2, In st s1 -> In st (join s1 s2).
Proof.
  unfold join; intros. destruct s1 as [ | m1].
- elim (bot_1 _ H).
- destruct s2 as [ | m2]; auto.
  red; unfold get; intros. rewrite IMFact.map2_1bis; auto.
  unfold join_aux. specialize (H x). unfold get in H.
  destruct (IdentMap.find x m1). 
  + destruct (IdentMap.find x m2).
    * apply V.join_1; auto.
    * apply V.top_1.
  + apply V.top_1.
Qed.

Lemma join_2:
    forall st s1 s2, In st s2 -> In st (join s1 s2).
Proof.
  unfold join; intros. destruct s2 as [ | m2].
- elim (bot_1 _ H).
- destruct s1 as [ | m1]; auto.
  red; unfold get; intros. rewrite IMFact.map2_1bis; auto.
  unfold join_aux. specialize (H x). unfold get in H.
  destruct (IdentMap.find x m1). 
  + destruct (IdentMap.find x m2).
    * apply V.join_2; auto.
    * apply V.top_1.
  + apply V.top_1.
Qed.

Definition widen_aux (ov1 ov2: option V.t) : option V.t :=
  match ov1, ov2 with
  | Some v1, Some v2 => Some (V.widen v1 v2)
  | _, _ => ov2
  end.

Definition widen (s1 s2: t) : t :=
  match s1, s2 with
  | Bot, _ => s2
  | _, Bot => s2
  | Top_except m1, Top_except m2 =>
      Top_except (IdentMap.map2 widen_aux m1 m2)
  end.

Lemma widen_1: forall s1 s2, le s2 (widen s1 s2).
Proof.
  unfold le, widen; intros.
  destruct s1 as [ | m1]; auto.
  destruct s2 as [ | m2]. elim (bot_1 _ H).
  red; unfold get; intros. specialize (H x); cbn in H.
  rewrite IMFact.map2_1bis; auto. unfold widen_aux.
  destruct (IdentMap.find x m1); destruct (IdentMap.find x m2).
- apply V.widen_1; auto.
- apply V.top_1.
- auto.
- apply V.top_1.
Qed.

End StateAbstr.


