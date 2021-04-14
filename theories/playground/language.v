From iris.prelude Require Import options prelude.
From stdpp Require Import gmap.


Class Language := {
  expr: Type;
  step: expr → expr → list expr → Prop;
  val: expr → Prop;
  is_val:> ∀ e, Decision (val e);
  val_no_step: ∀ e, val e → ¬ ∃ e' efs, step e e' efs;
}.


Notation pool := (list (expr * expr)).
Notation delays := (list nat).

(* Language Setup *)
Notation "P '.(tgt)'" := (P.*1) (at level 5).
Notation "P '.(src)'" := (P.*2) (at level 5).


Section language_setup.

  Context `{!Language}.
  Implicit Types (e: expr) (T: list expr) (D: delays) (P: pool).


  Definition no_fork e e' := step e e' [].
  Definition no_forks e e' := rtc no_fork e e'.

  Definition threads T :=
    list_to_set (C := gset nat) (seq 0 (length T)).

  Lemma threads_spec T i:
    i ∈ threads T ↔ ∃ e, T !! i = Some e.
  Proof.
    rewrite elem_of_list_to_set elem_of_seq.
    split.
    - intros [_ Hlt]. eapply lookup_lt_is_Some_2. lia.
    - intros ? % lookup_lt_is_Some_1. lia.
  Qed.

  Lemma threads_update T i e:
    threads T ⊆ threads (<[i:=e]> T).
  Proof.
    intros j [e' Hlook]%threads_spec.
    eapply threads_spec.
    destruct (decide (i = j)).
    - subst; exists e.
      eapply list_lookup_insert, lookup_lt_Some, Hlook.
    - rewrite list_lookup_insert_ne; last done. by exists e'.
  Qed.

  Lemma threads_weaken T T':
    threads T ⊆ threads (T ++ T').
  Proof.
    intros j (e & Hlook)%threads_spec.
    eapply threads_spec. exists e.
    eapply lookup_app_l_Some, Hlook.
  Qed.

  Lemma threads_src_tgt P:
    threads P.(tgt) = threads P.(src).
  Proof.
    by rewrite /threads !fmap_length.
  Qed.



  (* we lift the step relation to thread pools,
    and we define the notion of a fair step.
    A fair step decreases counters in an associated
    delay list.
  *)
  Inductive pool_step : list expr → nat → list expr → Prop :=
    take_pool_step i T_l e e' T_r T_f:
      step e e' T_f →
      i = length T_l →
      pool_step (T_l ++ e :: T_r) i (T_l ++ e' :: T_r ++ T_f).

  Inductive pool_steps : list expr → gset nat → list expr → Prop :=
    | pool_no_steps T: pool_steps T ∅ T
    | pool_do_steps T T' T'' i I J:
      pool_step T i T' →
      pool_steps T' I T'' →
      J ≡ I ∪ {[i]} →
      pool_steps T J T''.


  Lemma pool_step_iff T i T':
    pool_step T i T' ↔
    (∃ e e' T_f, step e e' T_f ∧ T !! i = Some e ∧ T' = <[i := e']> T ++ T_f).
  Proof.
    split.
    - destruct 1 as [i T_l e e' T_r T_f Hstep]; subst.
      exists e, e', T_f. split; first done.
      rewrite list_lookup_middle; last done.
      split; first done.
      replace (length T_l) with (length T_l + 0) by lia.
      rewrite insert_app_r; simpl.
      by rewrite -app_assoc.
    - intros (e & e' & T_f & Hstep & Hlook & ->).
      replace T with (take i T ++ e :: drop (S i) T); last by eapply take_drop_middle.
      assert (i = length (take i T)).
      { rewrite take_length_le; first lia. eapply lookup_lt_Some in Hlook. lia. }
      replace i with (length (take i T) + 0) at 4 by lia.
      rewrite insert_app_r. simpl.
      rewrite -app_assoc; simpl.
      econstructor; auto.
  Qed.

  Lemma pool_steps_single T i T':
    pool_step T i T' →
    pool_steps T {[i]} T'.
  Proof.
    intros Hstep; econstructor; [eauto|constructor|].
    set_solver.
  Qed.

  Lemma pool_step_value_preservation e T i j T':
    pool_step T j T' →
    val e →
    T !! i = Some e →
    T' !! i = Some e.
  Proof.
    rewrite pool_step_iff.
    destruct 1 as (e1 & e2 & T_f & Hstep & Hpre & Hpost).
    intros Hval Hlook. destruct (decide (i = j)); subst.
    - pose proof val_no_step. naive_solver.
    - eapply lookup_app_l_Some.
      rewrite list_lookup_insert_ne; done.
  Qed.

  Lemma pool_steps_value_preservation e T i J T':
    pool_steps T J T' →
    val e →
    T !! i = Some e →
    T' !! i = Some e.
  Proof.
    induction 1; eauto using pool_step_value_preservation.
  Qed.

  Lemma no_forks_pool_steps e e' e'' i T:
    no_fork e e' →
    no_forks e' e'' →
    T !! i = Some e →
    pool_steps T {[i]} (<[i := e'']> T).
  Proof.
    intros Hstep Hsteps.
    revert e T Hstep.
    induction Hsteps as [e'|e' e'' e''' Hstep' Hsteps IH]; intros e T Hstep Hlook.
    - eapply pool_steps_single, pool_step_iff.
      exists e, e', []; split; first done. split; first done.
      by rewrite right_id.
    - econstructor.
      + eapply pool_step_iff. exists e, e', []; split; first done. split; first done.
        rewrite right_id. reflexivity.
      + rewrite -(list_insert_insert T i e''' e'). eapply IH; eauto.
        eapply list_lookup_insert, lookup_lt_Some, Hlook.
      + set_solver.
  Qed.

  Lemma pool_steps_set_morph T T' I J:
    pool_steps T I T' →
    I ≡ J →
    pool_steps T J T'.
  Proof.
    by intros ? ->%leibniz_equiv.
  Qed.

  Lemma pool_steps_trans T T' T'' I I' J:
    pool_steps T I T' →
    pool_steps T' I' T'' →
    I ∪ I' ≡ J →
    pool_steps T J T''.
  Proof.
    induction 1 in J.
    - intros Hsteps Heq; eapply pool_steps_set_morph; first apply Hsteps. set_solver.
    - intros Hsteps Heq. econstructor; eauto. set_solver.
  Qed.


  (* an expression is active in a thread pool,
    if it is not a value *)
    Inductive fair_pool_step : list expr → list nat → nat → list expr → list nat → Prop :=
      take_fair_step i T T' D D':
      pool_step T i T' →
      (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n') →
      fair_pool_step T D i T' D'.

    Lemma fair_pool_step_iff T D i T' D':
      fair_pool_step T D i T' D' ↔
        pool_step T i T' ∧ (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').
    Proof.
      split; destruct 1; eauto 10 using take_fair_step.
    Qed.

    Lemma fair_pool_step_inv T D i T' D':
      fair_pool_step T D i T' D' →
        ∃ e e' T_f, step e e' T_f ∧
        T !! i = Some e ∧
        T' = <[i := e']> T ++ T_f ∧
        (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').
    Proof.
      destruct 1 as [i T T' D D' Pool Hdecr].
      eapply pool_step_iff in Pool as (e & e' & T_f & Hstep & Hlook & Hupd).
      eauto 10.
    Qed.


    Definition active_threads T :=
      list_to_set (C := gset nat) (fmap fst (filter (λ '(i, e), ¬ val e) (imap pair T))).

    Lemma active_threads_spec T i:
      i ∈ active_threads T ↔ ∃ e, T !! i = Some e ∧ ¬ val e.
    Proof.
      rewrite /active_threads elem_of_list_to_set elem_of_list_fmap.
      split.
      - intros [[i' e] [-> Hlook]]; simpl.
        eapply elem_of_list_filter in Hlook as [? Hlook].
        eapply elem_of_lookup_imap in Hlook as (? & ? & Heq & ?).
        injection Heq as ??; subst. eexists; split; eauto.
      - intros [e [Hlook Hval]]. exists (i, e).
        split; first done. eapply elem_of_list_filter.
        split; first done. eapply elem_of_lookup_imap.
        eexists _, _. split; done.
    Qed.

    Definition delays_for T D :=
      ∀ i, i ∈ active_threads T → is_Some (D !! i).


  CoInductive fair_div T D : Prop :=
  | fair_div_step i T' D':
    fair_pool_step T D i T' D' →
    delays_for T D →
    fair_div T' D' →
    fair_div T D.

  Inductive val_or_step : list expr → gset nat → list expr → Prop :=
    | val_or_step_values T O:
      (∀ i, i ∈ O → ∃ e, T !! i = Some e ∧ val e) → val_or_step T O T
    | val_or_step_step I O T T' T'':
        pool_steps T I T' → val_or_step T' (O ∖ I) T'' → val_or_step T O T''.

  CoInductive fair_div_alt T : Prop :=
    fair_div_alt_step T':
    val_or_step T (threads T) T' →
    fair_div_alt T' →
    fair_div_alt T.

  Lemma active_threads_step T i T':
    pool_step T i T' → active_threads T ∖ {[i]} ⊆ active_threads T'.
  Proof.
    intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
    intros j [Hact Hnj]%elem_of_difference.
    eapply active_threads_spec in Hact as (e'' & Hlook' & Hnval).
    assert (i ≠ j) by set_solver.
    eapply active_threads_spec. exists e''; split; last done.
    eapply lookup_app_l_Some. rewrite list_lookup_insert_ne //.
  Qed.

  Lemma threads_mono T i T':
    pool_step T i T' → threads T ⊆ threads T'.
  Proof.
    intros (e & e' & T_f & Hstep & Hlook & ->)%pool_step_iff.
    etrans; last by eapply threads_weaken.
    eapply threads_update.
  Qed.

  Lemma threads_mono' T I T':
    pool_steps T I T' → threads T ⊆ threads T'.
  Proof.
    induction 1; first done.
    etrans; first by eapply threads_mono.
    done.
  Qed.

  Lemma fair_div_delays T D:
    fair_div T D → delays_for T D.
  Proof. by destruct 1. Qed.

  Lemma fair_div_active_threads_steps T D:
    fair_div T D → ∃ T' D' O, active_threads T ⊆ O ∧ fair_div T' D' ∧ pool_steps T O T'.
  Proof.
    enough (∀ O T D, O ⊆ active_threads T → fair_div T D → ∃ T' D' O', O ⊆ O' ∧ fair_div T' D' ∧ pool_steps T O' T') by eauto.
    clear T D; intros O; induction (set_wf O) as [O _ IHO]; intros T D Hsub Hfair.
    destruct (decide (O ≡ ∅)) as [->%leibniz_equiv|[i Hi]%set_choose].
    - exists T, D, ∅. do 2 (split; first done). constructor.
    - assert (delays_for T D) as Hdel by by destruct Hfair.
      assert (is_Some (D !! i)) as [d HD] by eapply Hdel, Hsub, Hi.
      revert T D Hsub Hfair Hdel HD. induction (lt_wf d) as [d _ IHd].
      intros T D Hsub Hfair Hdel HD. destruct Hfair as [j T' D' Hstep _ Hfair].
      eapply fair_pool_step_iff in Hstep as [Hpool Hdecr].
      destruct (decide (j ∈ O)).
      + edestruct (IHO (O ∖ {[j]})) as (T'' & D'' & O' & HO' & Hfair' & Hsteps).
        * by set_solver.
        * etrans; last by apply active_threads_step. set_solver.
        * apply Hfair.
        * exists T'', D'', (O' ∪ {[j]}); split.
         { intros k Hk; destruct (decide (k = j)); set_solver. }
          split; first done.
          econstructor; eauto.
      + assert (j ≠ i) by set_solver.
        edestruct Hdecr as (d' & Heq & HD'); eauto.
        subst d. edestruct (IHd d') as (T'' & D'' & O' & HO' & Hfair' & Hsteps).
        * lia.
        * etrans; last by eapply active_threads_step. set_solver.
        * eauto.
        * by eapply fair_div_delays.
        * done.
        * exists T'', D'', (O' ∪ {[j]}); split.
          { intros k Hk; destruct (decide (k = j)); set_solver. }
          split; first done.
          econstructor; eauto.
  Qed.


  Lemma fair_div_foo T D:
    fair_div T D → fair_div_alt T.
  Proof.
    revert T D; cofix IH; intros T D Hfair.
    eapply fair_div_active_threads_steps in Hfair as (T' & D' & O & Hsub & Hfair' & Hsteps).
    apply (fair_div_alt_step T T'); last eauto.
    econstructor; eauto.
    constructor. intros i [Hi Ho]%elem_of_difference.
    eapply threads_spec in Hi as [e Hlook].
    destruct (decide (val e)).
    - exists e; split; last done. by eapply pool_steps_value_preservation.
    - exfalso. eapply Ho, Hsub, active_threads_spec. eauto 10.
  Qed.


End language_setup.