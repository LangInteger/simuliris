From iris.prelude Require Import options prelude.
From simuliris.playground Require Import fixpoints.
From stdpp Require Import gmap.

Lemma set_strong_ind {K} `{!EqDecision K} `{!Countable K} (P: gset K → Prop):
  (∀ O, (∀ O', O' ⊂ O → P O') → P O) → ∀ O, P O.
Proof.
  intros Step O; induction (set_wf O) as [O _ IH]; eauto.
Qed.

Section fair_termination_preservation.

  Context (expr: Type) (step: expr → expr → list expr → Prop)
          (val: expr → Prop) (is_val: ∀ e, Decision (val e))
          (val_no_step: ∀ e, val e → ¬ ∃ e' efs, step e e' efs).

  Notation pool := (list (expr * expr)).
  Notation delays := (list nat).
  Implicit Types (e: expr) (T: list expr) (D: delays) (P: pool).

  (* Language Setup *)
  Notation "P '.(tgt)'" := (P.*1) (at level 5).
  Notation "P '.(src)'" := (P.*2) (at level 5).

  Definition no_fork e e' := step e e' [].
  Definition no_forks e e' := rtc no_fork e e'.


  (* an expression is active in a thread pool,
     if it is not a value *)
  Definition active_threads T :=
    list_to_set (C := gset nat) (fmap fst (filter (λ '(i, e), ¬ val e) (imap pair T))).

  Definition threads T :=
    list_to_set (C := gset nat) (seq 0 (length T)).


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

  Lemma threads_spec T i:
    i ∈ threads T ↔ ∃ e, T !! i = Some e.
  Proof.
    rewrite /active_threads elem_of_list_to_set elem_of_seq.
    split.
    - intros [_ Hlt]. eapply lookup_lt_is_Some_2. lia.
    - intros ? % lookup_lt_is_Some_1. lia.
  Qed.

  Lemma threads_update T i e:
    threads T ⊆ threads (<[i:=e]> T).
  Proof using val_no_step.
    intros j [e' Hlook]%threads_spec.
    eapply threads_spec.
    destruct (decide (i = j)).
    - subst; exists e.
      eapply list_lookup_insert, lookup_lt_Some, Hlook.
    - rewrite list_lookup_insert_ne; last done. by exists e'.
  Qed.

  Lemma threads_weaken T T':
    threads T ⊆ threads (T ++ T').
  Proof using val_no_step.
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

  Inductive fair_pool_step : list expr → list nat → nat → list expr → list nat → Prop :=
    take_fair_step i T T' D D':
    pool_step T i T' →
    (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n') →
    fair_pool_step T D i T' D'.

  Definition delays_for T D :=
    ∀ i, i ∈ active_threads T → is_Some (D !! i).



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
  Proof using val_no_step.
    intros Hstep; econstructor; [eauto|constructor|].
    set_solver.
  Qed.

  Lemma pool_step_value_preservation e T i j T':
    pool_step T j T' →
    val e →
    T !! i = Some e →
    T' !! i = Some e.
  Proof using val_no_step.
    rewrite pool_step_iff.
    destruct 1 as (e1 & e2 & T_f & Hstep & Hpre & Hpost).
    intros Hval Hlook. destruct (decide (i = j)); subst.
    - naive_solver.
    - eapply lookup_app_l_Some.
      rewrite list_lookup_insert_ne; done.
  Qed.

  Lemma pool_steps_value_preservation e T i J T':
    pool_steps T J T' →
    val e →
    T !! i = Some e →
    T' !! i = Some e.
  Proof using val_no_step.
    induction 1; eauto using pool_step_value_preservation.
  Qed.

  Lemma no_forks_pool_steps e e' e'' i T:
    no_fork e e' →
    no_forks e' e'' →
    T !! i = Some e →
    pool_steps T {[i]} (<[i := e'']> T).
  Proof using val_no_step.
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
  Proof using val_no_step.
    induction 1 in J.
    - intros Hsteps Heq; eapply pool_steps_set_morph; first apply Hsteps. set_solver.
    - intros Hsteps Heq. econstructor; eauto. set_solver.
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

  (* Per-Thread Simulation *)

  Definition sim_expr_inner (outer: relation expr) (inner: relation expr) (e_t e_s: expr) :=
    (* value case *)
    (val e_t ∧ ∃ e_s', no_forks e_s e_s' ∧ val e_s') ∨
    (* target step case *)
    ((∃ e_t' T_t, step e_t e_t' T_t) ∧
     (∀ e_t' T_t, step e_t e_t' T_t →
      (* stuttering *)
      (T_t = [] ∧ inner e_t' e_s) ∨
      (* no stuttering *)
      (∃ e_s' e_s'' T_s,
        no_forks e_s e_s' ∧
        step e_s' e_s'' T_s ∧
        length T_t = length T_s ∧
        ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s'' :: T_s) → outer e_t e_s)
    )).

  Definition sim_expr_body outer := lfp (sim_expr_inner outer).
  Definition sim_expr := gfp sim_expr_body.

  Lemma sim_expr_inner_strong_mono outer outer' inner inner':
    outer ⪯ outer' →
    inner ⪯ inner' →
    sim_expr_inner outer inner ⪯ sim_expr_inner outer' inner'.
  Proof.
    intros Houter Hinner e_t e_s; rewrite /sim_expr_inner.
    intros [Val|[CanStep AllSteps]]; first by eauto.
    right; split; first done.
    intros e_t' T_t Hstep.
    destruct (AllSteps e_t' T_t Hstep) as [Stutter|NoStutter].
    - left; destruct Stutter; split; first done.
      by eapply Hinner.
    - destruct NoStutter as (e_s' & e_s'' & T_s & Hfrk & Hlen & Hstep' & Hall).
      right; exists e_s', e_s'', T_s; repeat split; [by eauto..|].
      intros ???. by eapply Houter, Hall.
  Qed.

  Instance sim_expr_inner_mono outer: Mono (sim_expr_inner outer).
  Proof.
    split; intros sim sim' Hsim. by eapply sim_expr_inner_strong_mono.
  Qed.

  Instance sim_expr_body_mono: Mono sim_expr_body.
  Proof.
    split; intros sim sim' Hsim.
    rewrite /sim_expr_body.
    eapply lfp_mono; first apply _.
    intros inner; by eapply sim_expr_inner_strong_mono.
  Qed.

  Lemma sim_expr_body_unfold sim e_t e_s:
    sim_expr_body sim e_t e_s ↔
    sim_expr_inner sim (sim_expr_body sim) e_t e_s.
  Proof using is_val val_no_step.
    revert e_t e_s; change (sim_expr_body sim ≡ sim_expr_inner sim (sim_expr_body sim)).
    eapply lfp_fixpoint, _.
  Qed.

  Lemma sim_expr_unfold e_t e_s:
    sim_expr e_t e_s ↔
    sim_expr_body sim_expr e_t e_s.
  Proof using is_val.
    revert e_t e_s; change (sim_expr ≡ sim_expr_body sim_expr).
    eapply gfp_fixpoint, _.
  Qed.

  Lemma sim_expr_fixpoint e_t e_s:
    sim_expr e_t e_s ↔
    sim_expr_inner sim_expr sim_expr e_t e_s.
  Proof using is_val val_no_step.
    rewrite sim_expr_unfold sim_expr_body_unfold.
    revert e_t e_s; change (sim_expr_inner sim_expr (sim_expr_body sim_expr) ≡ sim_expr_inner sim_expr sim_expr).
    eapply anti_symm; first apply lattice_anti_symm; eapply sim_expr_inner_strong_mono.
    - reflexivity.
    - intros ??; by rewrite sim_expr_unfold.
    - reflexivity.
    - intros ??; by rewrite sim_expr_unfold.
  Qed.

  (* inversion lemmas *)
  Lemma sim_expr_inv_val e_s e_t:
    sim_expr e_t e_s →
    val e_t →
    ∃ e_s', no_forks e_s e_s' ∧ val e_s'.
  Proof using val_no_step is_val.
    rewrite sim_expr_unfold sim_expr_body_unfold /sim_expr_inner.
    intros [[Ht Hs]|Hstep] Hval; first done.
    destruct Hstep as [Hstep _]. eapply val_no_step in Hstep; naive_solver.
  Qed.

  Lemma sim_expr_inv_step e_s e_t e_t' T_t:
    sim_expr e_t e_s → step e_t e_t' T_t →
    T_t = [] ∧ sim_expr e_t' e_s ∨
    ∃ e_s' e_s'' T_s,
      no_forks e_s e_s' ∧
      step e_s' e_s'' T_s ∧
      length T_t = length T_s ∧
      ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s'' :: T_s) → sim_expr e_t e_s.
  Proof using val_no_step is_val.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    intros [[Ht Hs]|Hstep] Htgt; first (exfalso; eapply val_no_step; [apply Ht|]; eauto).
    destruct Hstep as [_ Hstep]. destruct (Hstep _ _ Htgt) as [[-> Hsim]|].
    - left. split; done.
    - right. eauto.
  Qed.

  (* the introduction lemmas *)
  Lemma sim_expr_intro_vals e_s e_t:
    val e_t →
    val e_s →
    sim_expr e_t e_s.
  Proof using is_val val_no_step.
    intros V1 V2.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    left. split; first done.
    exists e_s; split; last done.
    rewrite /no_forks; reflexivity.
  Qed.

  Lemma sim_expr_intro_step e_s e_t:
    (∃ e_t' T_t, step e_t e_t' T_t) →
    (∀ e_t' T_t, step e_t e_t' T_t →
     ∃ e_s' T_s, step e_s e_s' T_s ∧
     length T_s = length T_t ∧
     ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s' :: T_s) → sim_expr e_t e_s) →
    sim_expr e_t e_s.
  Proof using is_val val_no_step.
    intros CanStep NoStutter.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    right. split; first done.
    intros e_t' T_t Hstep.
    right. destruct (NoStutter e_t' T_t Hstep) as (e_s' & T_s & Hstep' & Hlen & Hall).
    exists e_s, e_s', T_s; split; first by (rewrite /no_forks; reflexivity).
    eauto.
  Qed.

  Lemma sim_expr_intro_stutter_source e_s e_t:
    (∃ e_t' T_f, step e_t e_t' T_f) →
    (∀ e_t' T_f, step e_t e_t' T_f → T_f = [] ∧ sim_expr e_t' e_s) →
    sim_expr e_t e_s.
  Proof using is_val val_no_step.
    intros CanStep Stutter.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    right. split; first done.
    intros e_t' T_t Hstep; eauto.
  Qed.

  Lemma sim_expr_intro_stutter_target e_s e_s' e_t:
    no_fork e_s e_s' →
    sim_expr e_t e_s' →
    sim_expr e_t e_s.
  Proof using is_val val_no_step.
    rewrite sim_expr_fixpoint /sim_expr_inner.
    intros Hfrk Hsim. destruct Hsim as [Vals|[CanStep AllSteps]].
    - rewrite sim_expr_fixpoint /sim_expr_inner.
      destruct Vals as (val_t & e_s'' & Hsteps & val_s).
      left. split; first done. exists e_s''.
      split; last done. eapply rtc_l; eauto.
    - rewrite sim_expr_fixpoint /sim_expr_inner.
      right. split; first done.
      intros e_t' T_t' Hstep. right.
      destruct (AllSteps e_t' T_t' Hstep) as [Stutter|NoStutter].
      + destruct Stutter as [-> Hsim].
        exists e_s, e_s', []. split; first by (rewrite /no_forks; reflexivity).
        split; first done. split; first done.
        simpl. set_solver.
      + destruct NoStutter as (e_s'' & e_s''' & T_s & Hfrk' & Hstep' & Hlen & Hall).
        exists e_s'', e_s''', T_s. split; first by eapply rtc_l.
        split; first done. split; first done.
        done.
  Qed.

  (* Thread Pool Simulation *)

  Definition all_values (O: gset nat) P :=
    (∀ i , i ∈ O → ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s).

  Definition must_step (post: pool → Prop) (must_step: pool → gset nat → list nat → Prop) (P: pool) (O: gset nat) (D: delays) :=
    delays_for P.(tgt) D →
    (all_values O P ∧ post P) ∨
    (* source stuttering *)
    (∃ P' I, pool_steps P.(src) I P'.(src) ∧ P'.(tgt) = P.(tgt) ∧ must_step P' (O ∖ I) D) ∨
    (* steps in target and source *)
    ((∃ T_t' i, pool_step P.(tgt) i T_t') ∧
     (∀ T_t' D' i,
        fair_pool_step P.(tgt) D i T_t' D' →
        ∃ P' I, P'.(tgt) = T_t' ∧
        pool_steps P.(src) I P'.(src) ∧
        must_step P' (O ∖ I) D'
  )).

  Definition sim_pool_body (sim_pool: pool → Prop) (P: pool) :=
    ∀ D, lfp (must_step sim_pool) P (threads P.(tgt)) D.

  Definition sim_pool := gfp sim_pool_body.

  Lemma must_step_strong_mono (sim_pool sim_pool': pool → Prop) (rec rec': pool → gset nat → list nat → Prop):
    sim_pool ⪯ sim_pool' →
    rec ⪯ rec' →
    must_step sim_pool rec ⪯ must_step sim_pool' rec'.
  Proof.
    intros Hpool Hrec P O D; rewrite /must_step.
    intros Hmust Hdel. destruct (Hmust Hdel) as [Values|[Stutter|Step]].
    - left; destruct Values; split; first eauto. by eapply Hpool.
    - right. left. destruct Stutter as (P' & I & Hsteps & Heq & HP').
      exists P', I. repeat split; eauto. by eapply Hrec.
    - right. right. destruct Step as [? Step]; split; first done.
      intros T_t' D' i Hstep.
      destruct (Step T_t' D' i Hstep) as (P' & I & Heq & Hsteps & HP).
      exists P', I. repeat split; auto.
      by eapply Hrec.
  Qed.

  Instance must_step_mono Φ: Mono (must_step Φ).
  Proof.
    split; intros ???; by eapply must_step_strong_mono.
  Qed.

  Instance sim_pool_mono: Mono sim_pool_body.
  Proof.
    split; intros sim_pool sim_pool' Hpool.
    rewrite /sim_pool_body. intros P Hlfp D.
    specialize (Hlfp D). revert Hlfp.
    revert D. generalize (threads P.(tgt)) as O.
    revert P. change (lfp (must_step sim_pool) ⪯ lfp (must_step sim_pool')).
    eapply lfp_mono; first apply _.
    intros rec. by eapply must_step_strong_mono.
  Qed.

(* proof structure:
  co-induction on the outer fixpoint
    we need to show that sim_expr_all is a post-fixpoint.
    induction on the set of threads
    + base case trivial
    + step case: let i be the new thread and IH the inductive hypothesis.
      induction on the least fixpoint of i
      * value case:
          - target is a value, source steps to a value.
            we can remove i and we are done with IH
      * step case:
          (we can step ∧ (we stuttered or we took a proper step))
          induction on the delay unil thread i is stepped again
          let j be the next thread that steps
          -- if j = i and we stuttered the source, then the claim follows from the lfp
          -- if j = i and we did not stutter, we can remove i and the claim follows
          -- if j ≠ i, then any step will decrease the delay of i.
             The claim follows with the IH for d.
*)

Definition sim_expr_all P := (∀ e_t e_s, (e_t, e_s) ∈ P → sim_expr e_t e_s).
Notation local_all := (lfp (must_step sim_expr_all)).


Lemma local_all_add_values P O O' D:
  local_all P O D →
  (∀ i, i ∈ O' → i ∈ O ∨ ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s) →
  local_all P O' D.
Proof using val_no_step.
  intros Hall; revert P O D Hall O'.
  change (local_all ⪯ λ P O D, ∀ O' : gset nat,
    (∀ i : nat, i ∈ O' → i ∈ O ∨ ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s)
    → local_all P O' D).
  eapply lfp_least_pre_fixpoint; intros P O D Hsim O' Hel.
  rewrite lfp_fixpoint {1}/must_step.
  intros Hdel. specialize (Hsim Hdel) as [Base|[Stutter|Step]].
  - left. destruct Base as [Base ?]; split; last done.
    intros i Hi. destruct (Hel _ Hi) as [?|(? & ? & Hlook & ? & ?)]; eauto.
  - right. left.  destruct Stutter as (P' & I & Hsteps & Htgt & IH).
    exists P', I. split; first done. split; first done.
    eapply IH. intros i [Hi Hni]%elem_of_difference.
    destruct (Hel _ Hi) as [|Hvals]; first set_solver.
    right. destruct Hvals as (e_t & e_s & Hlook & val_t & val_s).
    exists e_t, e_s. split; last done.
    eapply (pool_steps_value_preservation _ _ i) in Hsteps; [|by eauto|]; last first.
    { rewrite list_lookup_fmap Hlook //. }
    assert (P'.(tgt) !! i = Some e_t) as Htgt_look.
    { rewrite Htgt list_lookup_fmap Hlook //. }
    revert Hsteps Htgt_look.
    rewrite !list_lookup_fmap.
    destruct (P' !! i) as [[]|]; simpl; naive_solver.
  - right. right. destruct Step as [? Step]; split; first done.
    intros T_t' D' i Hstep. destruct (Step T_t' D' i Hstep) as (P' & I & Heq & Hsteps & Hpost).
    exists P', I. split; first done. split; first done.
    eapply Hpost. intros j Hj. eapply elem_of_difference in Hj as [Hj HI].
    destruct (Hel _ Hj) as [?|Hvals].
    { left; eapply elem_of_difference; eauto. }
    right. destruct Hvals as (e_t & e_s & Hlook & val_t & val_s).
    exists e_t, e_s; split; last eauto.
    eapply pool_steps_value_preservation in Hsteps; [|by apply val_s| by erewrite list_lookup_fmap, Hlook].
    rewrite -Heq in Hstep. inversion Hstep as [????? Hstep' ?]; subst.
    eapply pool_step_value_preservation in Hstep'; [|by apply val_t| by erewrite list_lookup_fmap, Hlook].
    revert Hsteps Hstep'. rewrite !list_lookup_fmap.
    destruct (P' !! j) as [[??]|]; simpl; naive_solver.
Qed.


Lemma local_all_weaken P O O' D:
  local_all P O D →
  O' ⊆ O →
  local_all P O' D.
Proof using val_no_step.
  intros H1 H2. eapply local_all_add_values; first done.
  naive_solver.
Qed.

Lemma local_all_delay_for P O D:
  (delays_for P.(tgt) D → local_all P O D) → local_all P O D.
Proof.
  rewrite lfp_fixpoint.
  rewrite /must_step; intros Hstep Hdel; eapply (Hstep Hdel Hdel).
Qed.


Lemma sim_expr_all_insert P i e_t e_s:
  sim_expr_all P →
  sim_expr e_t e_s →
  sim_expr_all (<[i:=(e_t, e_s)]> P).
Proof.
  intros Hall Hsim e_t' e_s' Hin.
  eapply elem_of_list_lookup_1 in Hin as [j Hlook].
  eapply list_lookup_insert_Some in Hlook as [(-> & Heq & _)|(Hne & Hlook)].
  - naive_solver.
  - by eapply Hall, elem_of_list_lookup_2.
Qed.

Lemma sim_expr_all_app P P' :
  sim_expr_all P →
  sim_expr_all P' →
  sim_expr_all (P ++ P').
Proof.
  intros HP HP' e_t e_s [|]%elem_of_app; eauto.
Qed.


Lemma local_all_stuttered i e_t e_t' e_s P O D' T_t':
  T_t' = <[i := e_t']> P.(tgt) →
  P !! i = Some (e_t, e_s) →
  local_all (<[i := (e_t', e_s)]> P) O D' →
  ∃ P' (I : gset nat), P'.(tgt) = T_t' ∧ pool_steps P.(src) I P'.(src) ∧ local_all P' (O ∖ I) D'.
Proof using val_no_step.
  intros Hupd Hlook Hall; exists (<[i := (e_t', e_s)]> P), ∅.
  rewrite !list_fmap_insert; split; first done.
  rewrite list_insert_id; last rewrite list_lookup_fmap Hlook //.
  split; first constructor. eapply local_all_weaken; eauto. set_solver.
Qed.



Lemma local_all_not_stuttered i e_t e_t' e_s e_s' e_s'' P O D' T_t' T_f_s T_f_t:
  T_t' = <[i := e_t']> P.(tgt) ++ T_f_t →
  P !! i = Some (e_t, e_s) →
  no_forks e_s e_s' →
  step e_s' e_s'' T_f_s →
  length T_f_t = length T_f_s →
  local_all (<[i := (e_t', e_s'')]> P ++ zip T_f_t T_f_s) (O ∖ {[i]}) D' →
  ∃ P' (I : gset nat), P'.(tgt) = T_t' ∧ pool_steps P.(src) I P'.(src) ∧ local_all P' (O ∖ I) D'.
Proof using val_no_step.
  intros Hupd Hlook Hfrk Hstep Hlen Hall; exists (<[i := (e_t', e_s'')]> P ++ zip T_f_t T_f_s), {[i]}.
  rewrite !fmap_app fst_zip ?Hlen // snd_zip ?Hlen // !list_fmap_insert Hupd.
  split; first done.
  split; last done.
  destruct Hfrk as [e_s|e_s e_s_mid e_s'].
  - eapply pool_steps_single, pool_step_iff.
    do 3 eexists; repeat split; first done.
    rewrite list_lookup_fmap Hlook //=.
  - eapply pool_steps_trans; first eapply (no_forks_pool_steps _ _ _ i); eauto.
    + rewrite list_lookup_fmap Hlook //.
    + eapply pool_steps_single, (pool_step_iff _ i).
      exists e_s', e_s'', T_f_s. split; first done.
      split; first (eapply list_lookup_insert, lookup_lt_Some; rewrite list_lookup_fmap Hlook //).
      rewrite list_insert_insert. done.
    + set_solver.
Qed.


Lemma sim_expr_to_pool P:
  sim_expr_all P → sim_pool P.
Proof using val_no_step.
  revert P. change (sim_expr_all ⪯ sim_pool).
  eapply gfp_greatest_post_fixpoint. rewrite /sim_pool_body.
  enough (∀ O D P, sim_expr_all P → O ⊆ threads P.(tgt) → local_all P O D) by (intros ??; eauto).
  induction O as [O IHO] using set_strong_ind.
  intros D P Hall Hsub.
  destruct (decide (O ≡ ∅)) as [Empty|[i Hel]%set_choose].
  - rewrite lfp_fixpoint {1}/must_step. intros Hdel.
    left. split; last done. intros i; set_solver.
  - specialize (Hsub _ Hel) as Hthread.
    eapply threads_spec in Hthread as (e & Hlook).
    eapply list_lookup_fmap_inv in Hlook as ([e_t e_s] & -> & Hlook).
    assert (sim_expr e_t e_s) as Hsim by eapply Hall, elem_of_list_lookup_2, Hlook.
    revert Hsim; rewrite sim_expr_unfold /sim_expr_body; intros Hsim.
    revert e_t e_s Hsim P Hall Hlook D Hsub.
    change (lfp (sim_expr_inner sim_expr) ⪯
            λ e_t e_s, ∀ P,
              sim_expr_all P →
              P !! i = Some (e_t, e_s) →
              ∀ D, O ⊆ threads P.(tgt) → local_all P O D).
    eapply lfp_strong_ind; first apply _.
    intros e_t e_s Hinner P Hall Hlook D Hsub.
    destruct Hinner as [Val|[CanStep AllSteps]].
    + destruct Val as (val_t & e_s' & Hsteps & val_s).
      destruct Hsteps as [e_s|e_s e_s' e_s'' Hstep Hsteps].
      * eapply (local_all_add_values _ (O∖{[i]})).
        -- eapply IHO; auto; set_solver.
        -- intros j Hj; destruct (decide (i = j)); subst; last set_solver.
          right; do 2 eexists; done.
      * rewrite lfp_fixpoint {1}/must_step. intros Hdel.
        right. left. exists (<[i := (e_t, e_s'')]> P), {[i]}.
        split.
        { rewrite list_fmap_insert; eapply no_forks_pool_steps; eauto.
          rewrite list_lookup_fmap Hlook //. }
        split.
        { rewrite list_fmap_insert //= list_insert_id // list_lookup_fmap Hlook //. }
        eapply IHO.
        -- set_solver.
        -- eauto using sim_expr_all_insert, sim_expr_intro_vals.
        -- rewrite list_fmap_insert.
          etrans; last eapply threads_update.
          etrans; set_solver.
    + assert (¬ val e_t) as Hnval by naive_solver.
      eapply local_all_delay_for; intros Hdom.
      destruct (Hdom i) as [d HD]; last clear Hdom.
      { apply active_threads_spec. eapply Hsub in Hel. eapply threads_spec in Hel.
        destruct Hel as [e Hel]. exists e. revert Hel.
        rewrite list_lookup_fmap Hlook //=. naive_solver.
      }
      revert D P HD Hsub Hall Hlook.
      induction (lt_wf d) as [d _ IHd].
      intros D P HD Hsub Hall Hlook.
      rewrite lfp_fixpoint {1}/must_step; intros Hdel.
      right. right. split.
      { destruct CanStep as (e' & T_f & Hstep).
        exists (<[i := e']> P.(tgt) ++ T_f), i.
        eapply pool_step_iff. do 3 eexists; split; first eauto.
        split; last done. by rewrite list_lookup_fmap Hlook. }
      intros T_t' D' j Hpool.
      eapply fair_pool_step_inv in Hpool as (e_j_t & e_j_t' & T_f  & Htgt & Hlookj & Hupd & Hdecr).
      destruct (decide (i = j)).
      * subst j. rewrite list_lookup_fmap Hlook //= in Hlookj.
        assert (e_j_t = e_t) as -> by congruence; clear Hlookj.
        rename e_j_t' into e_t'. destruct (AllSteps _ _ Htgt) as [[-> Steps]|NoStutter].
        -- eapply local_all_stuttered; [by rewrite right_id in Hupd|done|].
           eapply id in Steps as Steps'. (* FIXME: this step is not linear, but we should be able to make it linear *)
           revert Steps Steps'; rewrite {1}meet_left meet_right.
           intros IH Hsim.
           change (lfp _ _ _) with (sim_expr_body sim_expr e_t' e_s) in Hsim.
           revert Hsim; rewrite -sim_expr_unfold; intros Hsim.
           eapply IH; eauto using sim_expr_all_insert, list_lookup_insert, lookup_lt_Some.
           etrans; first eapply Hsub.
           rewrite list_fmap_insert; eapply threads_update.
        -- destruct NoStutter as (e_s' & e_s'' & T_s & Hfrk & Hsrc & Hlen & Hsims).
           eapply local_all_not_stuttered; eauto.
           eapply IHO; first set_solver; last first.
           { rewrite fmap_app list_fmap_insert.
            etrans; last eapply threads_weaken.
            etrans; last eapply threads_update.
            set_solver. }
           eapply sim_expr_all_app; first eapply sim_expr_all_insert.
           { done. }
           { eapply Hsims; simpl; set_solver. }
           { intros ???; eapply Hsims; simpl; set_solver. }
        * eapply list_lookup_fmap_inv in Hlookj as ([e_j_t_ e_j_s] & -> & Hlookj).
          rename e_j_t_ into e_j_t; simpl in Htgt.
          assert (sim_expr e_j_t e_j_s) as Hsim by eapply Hall, elem_of_list_lookup_2, Hlookj.
          eapply Hdecr in HD as (m & -> & HD'); last done.
          eapply sim_expr_step in Hsim as [Stutter|NoStutter]; last done.
          -- destruct Stutter as [-> Hsim].
             eapply local_all_stuttered; [by rewrite right_id in Hupd|done|].
             eapply IHd; eauto using sim_expr_all_insert.
             { rewrite list_fmap_insert; by etrans; last eapply threads_update. }
             { rewrite list_lookup_insert_ne //. }
          -- destruct NoStutter as (e_j_s' & e_j_s'' & T_s & Hfrk & Hsrc & Hlen & Hsims).
             eapply local_all_not_stuttered; eauto.
             eapply (local_all_weaken _ O); last set_solver.
             eapply IHd; eauto.
             { rewrite fmap_app list_fmap_insert.
               etrans; last eapply threads_weaken.
               etrans; last eapply threads_update.
               done. }
            { eapply sim_expr_all_app; first eapply sim_expr_all_insert.
              - done.
              - eapply Hsims; simpl; set_solver.
              - intros ???; eapply Hsims; simpl; set_solver. }
            { eapply lookup_app_l_Some. by rewrite list_lookup_insert_ne. }
Qed.


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

CoInductive safe_fair_div T : Prop :=
  safe_fair_div_step T':
  val_or_step T (threads T) T' →
  safe_fair_div T' →
  safe_fair_div T.

Lemma sim_pool_val_or_step P D:
  fair_div P.(tgt) D →
  sim_pool P →
  ∃ P' D', sim_pool P' ∧
           fair_div P'.(tgt) D' ∧
           val_or_step P.(src) (threads P.(src)) P'.(src).
Proof.
  intros Hfair. rewrite /sim_pool.
  rewrite {1}gfp_fixpoint. fold sim_pool. rewrite /sim_pool_body.
  intros Hlfp; specialize (Hlfp D).
  revert Hlfp. rewrite threads_src_tgt. generalize (threads P.(src)) as O.
  intros O Hlfp. revert P O D Hlfp Hfair.
  change (lfp (must_step sim_pool) ⪯
    λ P O D, fair_div P.(tgt) D → ∃ P' D',
      sim_pool P' ∧ fair_div P'.(tgt) D' ∧ val_or_step P.(src) O P'.(src)).
  eapply lfp_least_pre_fixpoint; intros P O D MustStep Hfair.
  destruct Hfair as [i T' D' Hstep Hdel Hfair].
  destruct (MustStep Hdel) as [Values|[Stutter|[CanStep AllSteps]]].
  - destruct Values as [Hvalues Hsim]; exists P, D. split; first done.
    split; first (econstructor; eauto).
    left. intros j Hj. eapply Hvalues in Hj as (e_t & e_s & Hlook & Hval1 & Hval2).
    exists e_s. rewrite list_lookup_fmap Hlook; split; done.
  - destruct Stutter as (P' & I & Hsteps & Htgt & IH).
    rewrite Htgt in IH. assert (fair_div P.(tgt) D) as Hfair' by (econstructor; eauto).
    destruct (IH Hfair') as (P'' & D'' & Hpool & Hfair'' & Hvalstep).
    exists P'', D''; split; first done. split; first done.
    econstructor; eauto.
  - specialize (AllSteps _ _ _ Hstep) as (P' & I & <- & Hpool & Post).
    destruct (Post Hfair) as (P'' & D'' & Hpool' & Hfair' & Hvals').
    exists P'', D''. split; first done.
    split; first done. econstructor; eauto.
Qed.

Lemma sim_pool_preserves_fair_termination P D:
  fair_div P.(tgt) D →
  sim_pool P →
  safe_fair_div P.(src).
Proof.
  revert P D; cofix IH. intros P D Hfair Hsim.
  destruct (sim_pool_val_or_step _ _ Hfair Hsim) as (P' & D' & Hsim' & Hfair' & Hval).
  econstructor; eauto.
Qed.


End fair_termination_preservation.