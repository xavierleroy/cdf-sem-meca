From Coq Require Import Psatz.
From CDF Require Import Sequences.

(** Un diagramme de simulation générique, pour montrer l'équivalence sémantique
    entre deux programmes à partir de leurs sémantiques "à petits pas". *)

Section SIMULATION_DIAGRAM.

(** Le diagramme est paramétré par
    - les sémantiques "à petits pas" des deux programmes:
      type des configurations et relation de transition entre configurations;
    - un invariant qui relie les configurations des deux programmes.
*)

Variable C1: Type.	                (**r le type des configurations du programme source *)
Variable step1: C1 -> C1 -> Prop.   (**r sa relation de transition *)

Variable C2: Type.	                (**r le type des configurations du programme transformé *)
Variable step2: C2 -> C2 -> Prop.   (**r sa relation de transition *)

Variable inv: C1 -> C2 -> Prop.     (**r l'invariant *)

Variable measure: C1 -> nat.        (**r la mesure qui évite le bégaiement infini *)

(** Le diagramme proprement dit est l'hypothèse suivante:
    chaque transition du programme source est simulée par zéro, une ou plusieurs
    transitions du programme transformé, en préservant l'invariant, et
    en décrémentant la mesure dans le cas du bégaiement. *)

Hypothesis simulation:
  forall c1 c1', step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2',
     (plus step2 c2 c2' \/ (star step2 c2 c2' /\ measure c1' < measure c1))
  /\ inv c1' c2'.

(** Tout d'abord nous étendons la simulation aux suites finies de transitions
    dans le programme source.  C'est le lemme crucial pour montrer
    la préservation sémantique dans le cas où le programme source termine. *)

Lemma simulation_star:
  forall c1 c1', star step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2', star step2 c2 c2' /\ inv c1' c2'.
Proof.
  induction 1; intros.
- (* zéro transition *)
  exists c2; split. apply star_refl. auto.
- (* une ou plusieurs transitions *)
  destruct (simulation _ _ H _ H1) as (c2' & P & Q).
  destruct (IHstar _ Q) as (c2'' & U & V).
  exists c2''; split. 
  eapply star_trans; eauto. destruct P. apply plus_star; auto. destruct H2; auto.
  auto.
Qed.

(** Raisonnons maintenant sur un programme source qui effectue
    une infinité de transitions.
    D'abord nous montrons que le programme transformé peut toujours avancer
    dans son exécution tout en préservant la relation [inv].
    La démonstration est par récurrence sur le nombre maximal [N] d'étapes
    de bégaiement que le programme transformé peut faire avant d'effectuer
    au moins une transition. *)

Lemma simulation_infseq_productive:
  forall N c1 c2,
  measure c1 < N ->
  infseq step1 c1 ->
  inv c1 c2 ->
  exists c1', exists c2',
      plus step2 c2 c2'
   /\ infseq step1 c1'
   /\ inv c1' c2'.
Proof.
  induction N; intros c1 c2 MEAS INF1 INV.
- (* N = 0 *)
  lia.
- (* N > 0 *)
  destruct (infseq_inv INF1) as (c1' & STEP1 & INF1').
  destruct (simulation _ _ STEP1 _ INV) as (c2' & P & INV').
  destruct P as [STEPS2 | [STEPS2 MEAS']].
  + (* une ou plusieurs transitions *)
    exists c1'; exists c2'; auto.
  + (* zéro, une ou plusieurs transitions *)
    inversion STEPS2; subst; clear STEPS2.
    * (* zéro transitions *)
      eapply IHN; eauto. lia.
    * (* une ou plusieurs transitions *)
      exists c1'; exists c2'; split. eapply plus_left; eauto. auto.
Qed.

(** En conséquence, le programme transformé effectue une infinité de transitions
    si on le démarre dans une configuration qui correspond à une configuration
    divergente du programme source. *)

Lemma simulation_infseq:
  forall c1 c2,
  infseq step1 c1 ->
  inv c1 c2 ->
  infseq step2 c2.
Proof.
  intros. 
  apply infseq_coinduction_principle with
    (X := fun c2 => exists c1, infseq step1 c1 /\ inv c1 c2).
- clear c1 c2 H H0. intros c2 (c1 & INF & INV).  
  destruct (simulation_infseq_productive (measure c1 + 1) c1 c2) 
  as (c1' & c2' & PLUS2 & INF' & INV').
  lia. auto. auto.
  exists c2'; split. auto. exists c1'; auto. 
- exists c1; auto.
Qed.

End SIMULATION_DIAGRAM.
