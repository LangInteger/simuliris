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

  (* an expression is active in a thread pool,
     if it is not a value *)
  Definition active_exprs T :=
    list_to_set (C := gset nat) (fmap fst (filter (λ '(i, e), ¬ val e) (imap pair T))).

  Lemma active_expr_spec T i:
    i ∈ active_exprs T ↔ ∃ e, T !! i = Some e ∧ ¬ val e.
  Proof.
    rewrite /active_exprs elem_of_list_to_set elem_of_list_fmap.
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


  Lemma active_exprs_remove P i e O:
    (O ⊆ active_exprs P.(tgt)) →
    (O ∖ {[i]} ⊆ active_exprs (<[i:=e]> P.(tgt))).
  Proof using val_no_step.
  intros Hsub j Hel. eapply elem_of_difference in Hel as [Hj Hne].
  assert (j ≠ i) as Hne' by set_solver.
  eapply active_expr_spec.
  eapply Hsub in Hj. eapply active_expr_spec in Hj as (e' & Hlook & Hnval).
  exists e'. rewrite list_lookup_insert_ne; last done. split; done.
  Qed.

  Lemma active_exprs_update T i e O:
    (O ⊆ active_exprs T) →
    ¬ val e →
    O ⊆ active_exprs (<[i:=e]> T).
  Proof using val_no_step.
  intros Hsub Hnval j Hel.
  eapply active_expr_spec.
  eapply Hsub in Hel. eapply active_expr_spec in Hel as (e' & Hlook & Hnval').
  destruct (decide (i = j)).
  - subst; exists e. split; last done.
    eapply list_lookup_insert, lookup_lt_Some, Hlook.
  - rewrite list_lookup_insert_ne; last done. exists e'. split; done.
  Qed.

  Lemma active_exprs_weaken T T':
    active_exprs T ⊆ active_exprs (T ++ T').
  Proof using val_no_step.
    intros j (e & Hlook & Hnval)%active_expr_spec.
    eapply active_expr_spec. exists e. split; last done.
    eapply lookup_app_l_Some, Hlook.
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
    D !! i = Some 0 →
    (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n') →
    fair_pool_step T D i T' D'.

  Definition delays_for T D :=
    ∀ i, i ∈ active_exprs T → is_Some (D !! i).



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

  Lemma fair_pool_step_inv T D i T' D':
    fair_pool_step T D i T' D' →
      ∃ e e' T_f, step e e' T_f ∧
      T !! i = Some e ∧
      T' = <[i := e']> T ++ T_f ∧
      D !! i = Some 0 ∧
      (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n').
  Proof.
    destruct 1 as [i T T' D D' Pool HD Hdecr].
    eapply pool_step_iff in Pool as (e & e' & T_f & Hstep & Hlook & Hupd).
    eauto 10.
  Qed.

  Lemma fair_pool_step_zero_inv T D i j T' D':
    fair_pool_step T D j T' D' →
    D !! i = Some 0 →
    pool_step T i T'.
  Proof.
    destruct 1 as [j T T' D D' Hstep Hzero Hdec]; intros HD.
    destruct (decide (i = j)) as [|Hne]; last first.
    { specialize (Hdec i 0 Hne HD) as [? [? ?]]; lia. }
    subst j. done.
  Qed.


  (* Per-Thread Simulation *)

  Definition sim_expr_inner (outer: relation expr) (inner: relation expr) (e_t e_s: expr) :=
    (* value case *)
    (val e_t ∧ val e_s) ∨
    (* source stutter case
    (∃ e_s', step e_s e_s' ∧ least e_t e_s') ∨ *)
    (* target step case *)
    ((∃ e_t' T_t, step e_t e_t' T_t) ∧
      (* stuttering *)
      ((∀ e_t' efs, step e_t e_t' efs → efs = [] ∧ inner e_t' e_s) ∨
      (* no stuttering *)
      (∀ e_t' T_t, step e_t e_t' T_t →
      ∃ e_s' T_s, step e_s e_s' T_s ∧
      length T_t = length T_s ∧
        ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s' :: T_s) → outer e_t e_s
    ))).

  Definition sim_expr_body outer := lfp (sim_expr_inner outer).
  Definition sim_expr := gfp sim_expr_body.

  Instance sim_expr_inner_mono outer: Mono (sim_expr_inner outer).
  Admitted.

  Instance sim_expr_body_mono: Mono sim_expr_body.
  Proof. Admitted.

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

  (* for the base case *)
  Lemma sim_expr_val e_s e_t: sim_expr e_t e_s → val e_t → val e_s.
  Proof using val_no_step is_val.
    rewrite sim_expr_unfold sim_expr_body_unfold /sim_expr_inner.
    intros [[Ht Hs]|Hstep] Hval; first done.
    destruct Hstep as [Hstep _]. eapply val_no_step in Hstep; naive_solver.
  Qed.

  Lemma sim_expr_step e_s e_t e_t' T_t:
    sim_expr e_t e_s → step e_t e_t' T_t →
    T_t = [] ∧ sim_expr e_t' e_s ∨
    ∃ e_s' T_s, step e_s e_s' T_s ∧ length T_t = length T_s ∧
      ∀ e_t e_s, (e_t, e_s) ∈ zip (e_t' :: T_t) (e_s' :: T_s) → sim_expr e_t e_s.
  Proof using val_no_step is_val.
    rewrite sim_expr_unfold sim_expr_body_unfold /sim_expr_inner.
    intros [[Ht Hs]|Hstep] Htgt; first (exfalso; eapply val_no_step; [apply Ht|]; eauto).
    destruct Hstep as [_ [Hstep|Hstep]].
    - left. edestruct Hstep; eauto. split; first done.
      by rewrite sim_expr_unfold. (* todo: include this in the unfold *)
    - right. eauto.
  Qed.

  (* Thread Pool Simulation *)

  (* we define the pool simulation *)
  Definition must_step (post: pool → Prop) (must_step: pool → gset nat → list nat → Prop) (P: pool) (O: gset nat) (D: delays) :=
    delays_for (P.(tgt)) D →
    ((∀ i, i ∈ O → ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s) ∧ post P) ∨
    ((∃ T_t' i, pool_step P.(tgt) i T_t') ∧
     (∀ T_t' D' i,
        fair_pool_step P.(tgt) D i T_t' D' →
        ∃ P' I, P'.(tgt) = T_t' ∧
        pool_steps P.(src) I P'.(src) ∧
        must_step P' (O ∖ I) D'
  )).

  Definition sim_pool_body (sim_pool: pool → Prop) (P: pool) :=
    (∀ e_t e_s, (e_t, e_s) ∈ P → val e_t → val e_s) ∧
    ∀ D O, O ⊆ active_exprs P.(tgt) → lfp (must_step sim_pool) P O D.

  Definition sim_pool := gfp sim_pool_body.

  Instance must_step_mono Φ: Mono (must_step Φ).
  Proof. Admitted.

  Lemma must_step_post_mono sim_pool sim_pool':
    sim_pool ⪯ sim_pool' →
    must_step sim_pool ⪯ must_step sim_pool'.
  Proof. Admitted.

  Instance sim_pool_mono: Mono sim_pool_body.
  Proof. Admitted.


(* proof structure:
  co-induction on the outer fixpoint
  - base case trivial
  - step-case: induction on the set of active expressions
    + base case trivial
    + step case: let i be the new thread.
      induction on the least fixpoint of i
      * value case: we are done because thread i is active
      * step case:
        (we can step ∧ (we stuttered or we took a proper step))
        induction on the delay unil thread i is stepped again
        -- base case: next step is i
           ++ if we stutter this step, we can use the lfp IH
           ++ if we do not sutter this step, we make progress in the source.
              we can remove the thread from the set of active exprs that need to be stepped
              the set decreased so we can use the first IH
        -- step case: after the next step, the delay has decreased and we can use the IH
*)

Definition sim_expr_all P := (∀ e_t e_s, (e_t, e_s) ∈ P → sim_expr e_t e_s).
Definition local_all := lfp (must_step sim_expr_all).
Definition local_steps O P :=
  ∀ D,
  O ⊆ active_exprs (P.*1) →
  local_all P O D.


Lemma local_all_add_values P O O' D:
  local_all P O D →
  (∀ i, i ∈ O' → i ∈ O ∨ ∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s) →
  local_all P O' D.
Proof using val_no_step.
  intros Hall; revert P O D Hall O'.
  change (local_all ⪯ λ P O D, ∀ O' : gset nat,
    (∀ i : nat, i ∈ O' → i ∈ O ∨ (∃ e_t e_s, P !! i = Some (e_t, e_s) ∧ val e_t ∧ val e_s))
    → local_all P O' D).
  eapply lfp_least_pre_fixpoint; intros P O D Hsim O' Hel.
  rewrite /local_all lfp_fixpoint {1}/must_step.
  intros Hdel. specialize (Hsim Hdel) as [Base|Step].
  - left. destruct Base as [Base ?]; split; last done.
    intros i Hi. destruct (Hel _ Hi) as [?|]; by eauto.
  - right. destruct Step as [? Step]; split; first done.
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
  rewrite /local_all lfp_fixpoint.
  rewrite /must_step; intros Hstep Hdel; eapply (Hstep Hdel Hdel).
Qed.


Lemma sim_expr_all_insert P i e_t e_s:
  sim_expr_all P → sim_expr e_t e_s → sim_expr_all (<[i:=(e_t, e_s)]> P).
Proof.
  intros Hall Hsim e_t' e_s' Hin.
  eapply elem_of_list_lookup_1 in Hin as [j Hlook].
  eapply list_lookup_insert_Some in Hlook as [(-> & Heq & _)|(Hne & Hlook)].
  - naive_solver.
  - by eapply Hall, elem_of_list_lookup_2.
Qed.

Lemma sim_expr_to_pool P:
  sim_expr_all P → sim_pool P.
Proof.
  revert P. change (sim_expr_all ⪯ sim_pool).
  eapply gfp_greatest_post_fixpoint. intros P Hsim. split.
  - intros e_t e_s Hel Hval. eapply sim_expr_val; last done. eapply (Hsim e_t e_s Hel).
  - intros D O; revert D. change (local_steps O P).
    revert P Hsim. induction O as [O IH] using set_strong_ind.
    destruct (decide (O ≡ ∅)) as [Empty|[i Hel]%set_choose].
    + intros P Hsize D Hsub. rewrite /local_all lfp_fixpoint {1}/must_step.
      intros Hdel. left. split; last done.
      intros i; set_solver.
    + intros P Hall D Hsub.
      specialize (Hsub _ Hel) as Hactive.
      eapply active_expr_spec in Hactive as (e & Hlook & Hnval).
      eapply list_lookup_fmap_inv in Hlook as ([e_t e_s] & -> & Hlook).
      simpl in Hnval.
      assert (sim_expr e_t e_s) as Hsim by eapply Hall, elem_of_list_lookup_2, Hlook.
      revert Hsim; rewrite sim_expr_unfold /sim_expr_body; intros Hsim.
      revert e_t e_s Hsim P Hall Hnval Hlook D Hsub.
      change (lfp (sim_expr_inner sim_expr) ⪯
              λ e_t e_s, ∀ P,
                sim_expr_all P →
                ¬ val e_t →
                P !! i = Some (e_t, e_s) →
                local_steps O P).
      eapply lfp_strong_ind; first apply _.
      intros e_t e_s Hinner P Hall Hnval Hlook D Hsub.
      destruct Hinner as [Val|[CanStep AllSteps]].
      * naive_solver.
      * eapply local_all_delay_for; intros Hdom.
        destruct (Hdom i) as [d HD]; first apply Hsub, Hel.
        clear Hdom.
        revert D P HD Hsub Hall Hlook.
        induction d as [|d IHd].
        -- intros D P HD Hsub Hall Hlook.
           rewrite /local_all lfp_fixpoint {1}/must_step.
           intros Hdom.
           right. split.
           { destruct CanStep as (e' & T_f & Hstep).
             exists (<[i := e']> P.*1 ++ T_f), i.
             eapply pool_step_iff. do 3 eexists; split; first eauto.
             split; last done. by rewrite list_lookup_fmap Hlook. }
           intros T_t' D' j Hpool.
           (* eapply fair_pool_step_inv in Hpool as (e_t_dup & e_t' & T_f & Hstep & Hdup & Hupd & Hj). *)
           eapply fair_pool_step_zero_inv in Hpool; last done.
           eapply (pool_step_iff) in Hpool as (e_t_dup & e_t' & T_f & Hstep & Hlook' & Hupd).
           assert (e_t_dup = e_t) as ->; last clear Hlook'.
           { revert Hlook'; rewrite list_lookup_fmap Hlook //=; naive_solver. }
           destruct AllSteps as [Stutter|NoStutter].
           ++ specialize (Stutter _ _ Hstep) as [-> Hcont].
              exists (<[i := (e_t', e_s)]> P), ∅.
              split. { by rewrite Hupd list_fmap_insert //= right_id. }
              split.
              { rewrite list_fmap_insert //= list_insert_id; first by constructor.
                rewrite list_lookup_fmap Hlook //=. }
              destruct (decide (val e_t')).
              ** revert Hcont. rewrite meet_right.
                 change (lfp (sim_expr_inner _) _ _) with (sim_expr_body sim_expr e_t' e_s).
                 rewrite -sim_expr_unfold. intros sim.
                 assert (val e_s) as v' by by eapply sim_expr_val.
                 eapply (local_all_add_values _ (O ∖ {[i]})).
                 { eapply IH.
                   - eapply subset_difference_elem_of, Hel.
                   - by eapply sim_expr_all_insert.
                   - rewrite list_fmap_insert //=. by eapply active_exprs_remove.
                 }
                 { intros k Hk. eapply elem_of_difference in Hk as [Hk _].
                   destruct (decide (i = k)); first subst.
                   - right. exists e_t', e_s. repeat split; auto.
                     eapply list_lookup_insert, lookup_lt_Some, Hlook.
                   - left. set_solver.
                 }
              ** apply id in Hcont as Hcont'; revert Hcont Hcont'; rewrite {1}meet_left {1}meet_right; intros Hcont Hsim.
               assert (local_steps O (<[i := (e_t', e_s)]> P)) as Hlocal.
                 { eapply Hcont; [|done|].
                   + eapply sim_expr_all_insert; first done.
                     by rewrite sim_expr_unfold /sim_expr_body.
                   + eapply list_lookup_insert, lookup_lt_Some, Hlook.
                  }
                 feed pose proof (Hlocal D').
                 { rewrite list_fmap_insert //=. eapply active_exprs_update; auto. }
                 { eapply local_all_weaken; first done. set_solver. }
          ++ specialize (NoStutter _ _ Hstep) as (e_s' & T_s & Hstep_src & Hlen & Hsim).
             exists (<[i := (e_t', e_s')]> P ++ zip T_f T_s), {[i]}.
             rewrite !fmap_app fst_zip; last lia.
             rewrite snd_zip; last lia.
             rewrite !list_fmap_insert.
             split; first done.
             split.
             { simpl. econstructor; [|eapply pool_no_steps|by rewrite left_id].
               eapply pool_step_iff. exists e_s, e_s', T_s.
               repeat split; eauto. by rewrite list_lookup_fmap Hlook. }
             assert (local_steps (O ∖ {[i]}) (<[i := (e_t', e_s')]> P ++ zip T_f T_s)) as Hlocal.
             { eapply IH; first by set_solver.
               intros t s [Hin|Hin]%elem_of_app.
               - eapply sim_expr_all_insert; [apply Hall| |apply Hin].
                 eapply Hsim; simpl; set_solver.
               - eapply Hsim; simpl; set_solver.
             }
             eapply Hlocal.
             { rewrite fmap_app. etrans; first by eapply active_exprs_remove.
               rewrite list_fmap_insert. eapply active_exprs_weaken. }
        -- intros D P HD Hsub Hall Hlook.
           rewrite /local_all lfp_fixpoint {1}/must_step.
           intros Hdel.
           right. split.
           { destruct CanStep as (e' & T_f & Hstep).
             exists (<[i := e']> P.*1 ++ T_f), i.
             eapply pool_step_iff. do 3 eexists; split; first eauto.
             split; last done. by rewrite list_lookup_fmap Hlook. }
           intros T_t' D' j Hfair.
           eapply fair_pool_step_inv in Hfair as (j_t & j_t' & T_f & Hstep & Hlook' & Hupd & HDj & Hdecr).
           assert (i ≠ j) as Hij by congruence.
           assert (∃ j_s, P !! j = Some (j_t, j_s)) as [j_s Hlook''].
           { revert Hlook'. rewrite list_lookup_fmap.
             destruct (P !! j) as [[]|]; simpl; naive_solver. }
           clear Hlook'.
           assert (sim_expr j_t j_s) as Hsim.
           { eapply Hall, elem_of_list_lookup_2, Hlook''. }
           eapply sim_expr_step in Hsim; last eauto.
           destruct Hsim as [Stutter|NoStutter].
           ++ exists (<[j := (j_t', j_s)]> P), ∅.
              destruct Stutter as [-> Hsim].
              rewrite !list_fmap_insert. subst T_t'.
              split; first by rewrite right_id.
              split.
              { simpl; rewrite list_insert_id; eauto using pool_no_steps.
                by rewrite list_lookup_fmap Hlook''. }
              eapply Hdecr in HD as (x & Heq & HD'); last done.
              assert (x = d) as -> by congruence; clear Heq.
              eapply (local_all_weaken _ O); last set_solver.
              eapply IHd; auto using sim_expr_all_insert; last first.
              { rewrite list_lookup_insert_ne //. }
              admit.
              (* we have the same value distinction here as before,
                 we should be able to remove the active_exprs assumption *)
           ++ destruct NoStutter as (j_s' & T_s & Hsrc & Hlen & Hall').
              exists (<[j := (j_t', j_s')]> P ++ zip T_f T_s), {[j]}.
              (* analogous to the previous case:
                 if j is still in O, then we have decreased O just now.
                 if j is not in O, then the d has decreased for this O
                 and we can use IHd. *)
              admit.
Admitted.