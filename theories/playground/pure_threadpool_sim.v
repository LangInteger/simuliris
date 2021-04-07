From iris.prelude Require Import options prelude.
From simuliris.playground Require Import fixpoints.
From stdpp Require Import gmap.


Section simulation.
  Context (expr: Type) (step: expr → expr → list expr → Prop)
          (val: expr → Prop) (is_val: ∀ e, Decision (val e))
          (val_no_step: ∀ e, val e → ¬ ∃ e' efs, step e e' efs).

  Notation pool := (list (expr * expr)).
  Notation delays := (list nat).

  Implicit Types (e: expr) (T: list expr) (D: delays) (P: pool).

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

  Inductive pool_step : list expr → nat → list expr → Prop :=
    take_pool_step i T_l e e' T_r T_f:
      step e e' T_f →
      i = length T_l →
      pool_step (T_l ++ e :: T_r) i (T_l ++ e' :: T_r ++ T_f).

  Inductive pool_steps : list expr → gset nat → list expr → Prop :=
    | pool_no_steps T: pool_steps T ∅ T
    | pool_do_steps T T' T'' i I:
      pool_step T i T' →
      pool_steps T' I T'' →
      pool_steps T (I ∪ {[i]}) T''.

  Inductive fair_pool_step : list expr → list nat → nat → list expr → list nat → Prop :=
    take_fair_step i T T' D D':
    pool_step T i T' →
    (∀ j n, j ≠ i → D !! j = Some n → ∃ n', n = S n' ∧ D' !! j = Some n') →
    fair_pool_step T D i T' D'.

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

  (* we define the pool simulation *)
  Definition must_step (post: pool → Prop) (must_step: pool → gset nat → list nat → Prop) (P: pool) (O: gset nat) (D: delays) :=
    (O ≡ ∅ ∧ post P) ∨
    ((∃ T_t' i, pool_step (P.*1) i T_t') ∧
     (∀ T_t' D' i,
        fair_pool_step (P.*1) D i T_t' D' →
        ∃ P' I, P'.*1 = T_t' ∧
        pool_steps (P.*2) I (P'.*2) ∧
        must_step P' (O ∖ I) D'
  )).

  Definition sim_pool_body (sim_pool: pool → Prop) (P: pool) :=
    (∀ e_t e_s, (e_t, e_s) ∈ P → val e_t → val e_s) ∧
    ∀ D O,
      O ⊆ active_exprs (P.*1) →
      (∀ i, i ∈ O → is_Some (D !! i)) →
      lfp (must_step sim_pool) P O D.

  Definition sim_pool :=
    gfp sim_pool_body.

  Instance must_step_mono Φ: Mono (must_step Φ).
  Proof. Admitted.
    (* split; intros must_step must_step' Himpl P O D Hstep.
    rewrite /simulation.must_step.
    destruct Hstep as [Base|Step]; first eauto.
    right. destruct Step as [CanStep AllSteps].
    split; first done. intros T_t' D' i Hincl Hstep.
    destruct (AllSteps T_t' D' i Hincl Hstep) as (P' & I & Heq & Hsteps & Rec).
    exists P', I. repeat split; [done..|].
    eapply Himpl, Rec.
  Qed. *)

  Lemma must_step_post_mono sim_pool sim_pool':
    sim_pool ⪯ sim_pool' →
    must_step sim_pool ⪯ must_step sim_pool'.
  Proof. Admitted.
  (*  intros Hle must_step P O D Hstep.
    rewrite /simulation.must_step.
    destruct Hstep as [Base|Step].
    - left. destruct Base; split; eauto. by eapply Hle.
    - right. done.
  Qed.*)

  Instance sim_pool_mono: Mono sim_pool_body.
  Proof. Admitted.
    (* split; intros sim_pool sim_pool';
      rewrite /simulation.sim_pool /sim_pool_body.
    intros Himpl P [Base MustStep].
    split; first done. clear Base.
    intros D. specialize (MustStep D).
    revert D MustStep.  generalize (active_exprs P.*1) as O. revert P.
    change (lfp (must_step sim_pool) ⪯ lfp (must_step sim_pool')).
    eapply lfp_mono; first apply _.
    eapply must_step_post_mono, Himpl.
  Qed. *)

(* we prove that the sim_expr simulations imply the pool simulation,
   but first we need a bunch of intermeditate results *)

(* for the base case *)
Lemma sim_expr_val e_s e_t: sim_expr e_t e_s → val e_t → val e_s.
Proof using val_no_step is_val.
  rewrite sim_expr_unfold sim_expr_body_unfold /sim_expr_inner.
  intros [[Ht Hs]|Hstep] Hval; first done.
  destruct Hstep as [Hstep _]. eapply val_no_step in Hstep; naive_solver.
Qed.


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
Definition local_steps O P :=
  ∀ D,
  O ⊆ active_exprs (P.*1) →
  (∀ i, i ∈ O → is_Some (D !! i)) →
  lfp (must_step sim_expr_all) P O D.


Lemma set_strong_ind (P: gset nat → Prop):
  (∀ O, (∀ O', O' ⊂ O → P O') → P O) → ∀ O, P O.
Proof.
  intros Step O. remember (size O) as n.
  revert O Heqn. induction (lt_wf n) as [n _ IHn].
  assert (∀ O, size O < n → P O) as IH by eauto.
  intros O Heqn. eapply Step.
  intros O' Hsub.
  eapply IH. subst n. by eapply subset_size.
Qed.


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

Lemma fair_pool_step_inv T D i T' D':
  fair_pool_step T D i T' D' →
  ∃ e e' T_f, step e e' T_f ∧
  T !! i = Some e ∧
  T' = <[i := e']> T ++ T_f ∧
  D !! i = Some 0.
Proof. Admitted.




(* TODO: we need to include information about D' *)
Lemma fair_pool_step_zero_inv T D i j T' D':
  fair_pool_step T D j T' D' →
  D !! i = Some 0 →
  pool_step T i T'.
Proof.
  destruct 1 as [j T T' D D' Hstep Hdec]; intros HD.
  destruct (decide (i = j)) as [|Hne]; last first.
  { specialize (Hdec i 0 Hne HD) as [? [? ?]]; lia. }
  subst j. done.
Qed.

Lemma pool_step_lookup e T i T':
  pool_step T i T' →
  T !! i = Some e →
  ∃ e' T_f, step e e' T_f.
Proof. Admitted.
  (* destruct 1 as [j T T' D D' Hstep Hdec]; intros HD.
  destruct (decide (i = j)) as [|Hne]; last first.
  { specialize (Hdec i 0 Hne HD) as [? [? ?]]; lia. }
  subst j. done.
Qed. *)



Lemma sim_expr_to_pool P:
  sim_expr_all P → sim_pool P.
Proof.
  revert P. change (sim_expr_all ⪯ sim_pool).
  eapply gfp_greatest_post_fixpoint. intros P Hsim. split.
  - intros e_t e_s Hel Hval. eapply sim_expr_val; last done. eapply (Hsim e_t e_s Hel).
  - intros D O; revert D. change (local_steps O P).
    revert P Hsim. induction O as [O IH] using set_strong_ind.
    destruct (decide (O ≡ ∅)) as [Empty|[i Hel]%set_choose].
    + intros P Hsize Hall D Hsub. rewrite lfp_fixpoint /must_step.
      left. eauto.
    + intros P Hall D Hsub Hdom.
      specialize (Hsub _ Hel) as Hactive.
      eapply active_expr_spec in Hactive as (e & Hlook & Hnval).
      eapply list_lookup_fmap_inv in Hlook as ([e_t e_s] & -> & Hlook).
      simpl in Hnval.
      assert (sim_expr e_t e_s) as Hsim by eapply Hall, elem_of_list_lookup_2, Hlook.
      revert Hsim; rewrite sim_expr_unfold /sim_expr_body; intros Hsim.
      revert e_t e_s Hsim P Hall Hnval Hlook D Hsub Hdom.
      change (lfp (sim_expr_inner sim_expr) ⪯
              λ e_t e_s, ∀ P,
                sim_expr_all P →
                ¬ val e_t →
                P !! i = Some (e_t, e_s) →
                local_steps O P).
      eapply lfp_least_pre_fixpoint;
        intros e_t e_s Hinner P Hall Hnval Hlook D Hsub Hdom.
      destruct Hinner as [Val|[CanStep AllSteps]].
      * naive_solver.
      * pose proof (Hdom _ Hel) as [d HD].
        revert D P HD Hdom Hsub Hall Hlook.
        induction d as [|d IHd].
        -- intros D P HD Hdom Hsub Hall Hlook.
           rewrite lfp_fixpoint {1}/must_step.
           right. split.
           { destruct CanStep as (e' & T_f & Hstep).
             exists (<[i := e']> P.*1 ++ T_f), i.
             eapply pool_step_iff. do 3 eexists; split; first eauto.
             split; last done. by rewrite list_lookup_fmap Hlook. }
           intros T_t' D' j Hpool.
           (* eapply fair_pool_step_inv in Hpool as (e_t_dup & e_t' & T_f & Hstep & Hdup & Hupd & Hj). *)
           eapply fair_pool_step_zero_inv in Hpool; last done.
           eapply (pool_step_lookup e_t) in Hpool as (e_t' & T_f & Hstep); last admit.
           destruct AllSteps as [Stutter|NoStutter].
           ++ specialize (Stutter _ _ Hstep) as [-> Hcont].
              destruct (decide (val e_t')).
              ** admit. (* if the target has reached a value, we obtain the source as a value from the simulation *)

              ** exists (<[i := (e_t', e_s)]> P), ∅.
                 split; first admit.
                 assert (local_steps O (<[i := (e_t', e_s)]> P)) as Hlocal.
                 { eapply Hcont; admit. }
                 feed pose proof (Hlocal D').
                 { admit.  }
                 { admit. }
                 split; first admit.
                 admit.
          ++ specialize (NoStutter _ _ Hstep) as (e_s' & T_s & Hstep_src & Hlen & Hsim).
             exists (<[i := (e_t', e_s')]> P ++ zip T_f T_s), {[i]}.
             split; first admit.
             split; first admit.
             assert (local_steps (O ∖ {[i]}) (<[i := (e_t', e_s')]> P ++ zip T_f T_s)) as Hlocal.
             { eapply IH; admit. }
             eapply Hlocal.
             { admit. }
             { admit. }
        -- intros D P HD Hdom Hsub Hall Hlook.
           rewrite lfp_fixpoint {1}/must_step.
           right. split; first admit. (* can step *)
           intros T_t' D' j Hfair.
           eexists _, ∅. split; first admit.
           split; first admit.
           (* the P needs to be the updated one *)
           feed pose proof (IHd D' P).
           { admit. }
           { admit. }
           { admit. (* we need a case analysis whether this has terminated in a value *) }
           { admit. (* we can just unfold one of them for one step *) }
           { admit. (* j stepped, so the result ist still the same *) }
           admit. (* is exactly H *)
Admitted.