From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import
  fairness relations language behavior global_sim fairness_adequacy.
Import bi.



Section meta_level_simulation.

  Context {PROP : bi}.
  Context {Λ : language}.
  Context {s : simulirisG PROP Λ}.
  Context {PROP_bupd : BiBUpd PROP}.
  Context {PROP_affine : BiAffine PROP}.
  Context {PROP_forall : BiPureForall PROP}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Context (p_t p_s: prog Λ).

  (* we pull out the simulation to a meta-level simulation,
     the set V tracks which threads are already values in both target and source *)
  Definition msim (T_t: tpool Λ) (σ_t: state Λ)  (T_s: tpool Λ) (σ_s: state Λ) (V: gset nat) :=
    sat (state_interp p_t σ_t p_s σ_s T_s ∗ ⌜∀ i, i ∈ V → ∃ v_t v_s, T_t !! i = Some (of_val v_t) ∧ T_s !! i = Some (of_val v_s)⌝ ∗ [∗ list] i↦e_t; e_s ∈ T_t;T_s, gsim_expr (lift_post (ext_rel i)) i e_t e_s).

  Lemma msim_length T_t T_s σ_t σ_s V:
    msim T_t σ_t T_s σ_s V → length T_t = length T_s.
  Proof.
    intros Hsim. eapply sat_elim, sat_mono, Hsim.
    iIntros "(_ & _ & Hsims)". rewrite big_sepL2_alt.
    iDestruct "Hsims" as "[$ _]".
  Qed.

  Lemma msim_add_val (v_t: val Λ) (T_t T_s: tpool Λ) (σ_t σ_s: state Λ) i V:
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    T_t !! i = Some (of_val v_t) →
    ∃ T_s' σ_s' I, pool_steps p_s T_s σ_s I T_s' σ_s' ∧ msim T_t σ_t T_s' σ_s' (V ∪ {[i]}).
  Proof.
    intros Hsim Hsafe Hlook. eapply msim_length in Hsim as Hlen.
    assert (is_Some (T_s !! i)) as [e_s Hlook'].
    { eapply lookup_lt_is_Some; rewrite -Hlen; eapply lookup_lt_is_Some; eauto. }
    rewrite /msim in Hsim. eapply sat_mono in Hsim.
    - eapply sat_bupd in Hsim.
      eapply sat_exists in Hsim as [T_s' Hsim]; exists T_s'.
      eapply sat_exists in Hsim as [σ_s' Hsim]; exists σ_s'.
      eapply sat_exists in Hsim as [I Hsim]; exists I.
      eapply sat_sep in Hsim as [Hdone Hsim].
      eapply sat_elim in Hdone. split; [exact Hdone|exact Hsim].
    - simpl; clear Hsim. iIntros "(SI & %Hvals & Hsims)".
      iPoseProof (big_sepL2_insert_acc with "Hsims") as "[Hsim Hpost]"; eauto.
      rewrite gsim_expr_unfold. iMod ("Hsim" with "[$SI]") as "[Val|Step]".
      + iPureIntro. by erewrite fill_empty.
      + iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI Post]".
        iDestruct "Post" as (v_t' v_s Heq1 Heq2) "Val". rewrite fill_empty.
        eapply of_val_inj in Heq1 as <-. subst e_s'.
        eapply no_forks_pool_steps in Hnfs as (I & Hpool & _); last done.
        iModIntro. iExists (<[i := (of_val v_s)]> T_s), σ_s', I.
        iSplit; first done. iFrame. iSplit.
        * iPureIntro. intros j. destruct (decide (j = i)) as [->|Hne].
          { exists v_t, v_s. split; first done.
            eapply list_lookup_insert, lookup_lt_Some, Hlook'. }
          intros Hj; assert (j ∈ V) as Hj' by set_solver.
          rewrite list_lookup_insert_ne //. eauto.
        * rewrite -{2}(list_insert_id T_t i (of_val v_t)) //. iApply "Hpost".
          iApply gsim_expr_base. iExists v_t, v_s. by iFrame.
      + iDestruct "Step" as "[%Hred _]".
        destruct Hred as (e_t' & σ_t' & efs & Hprim).
        exfalso. by eapply val_prim_step.
  Qed.

  Lemma msim_proj_val (T_t T_s: tpool Λ) (σ_t σ_s: state Λ) i V:
    i ∈ V →
    pool_safe p_s T_s σ_s →
    msim T_t σ_t T_s σ_s V →
    ∃ v_t v_s,
      T_t !! i = Some (of_val v_t) ∧
      T_s !! i = Some (of_val v_s) ∧
      sat (state_interp p_t σ_t p_s σ_s T_s ∗ ext_rel i v_t v_s).
  Proof.
    intros Hel Hsafe Hsim. rewrite /msim in Hsim. eapply sat_mono in Hsim.
    - eapply sat_bupd in Hsim.
      eapply sat_exists in Hsim as [v_t Hsim]; exists v_t.
      eapply sat_exists in Hsim as [v_s Hsim]; exists v_s.
      eapply sat_sep in Hsim as [Hlook1%sat_elim Hsim].
      split; first exact Hlook1.
      eapply sat_sep in Hsim as [Hlook2%sat_elim Hsim].
      split; first exact Hlook2.
      exact Hsim.
    - simpl. iIntros "(SI & %Vals & Hsims)".
      destruct (Vals i Hel) as (v_t & v_s & Hlook1 & Hlook2).
      iPoseProof (big_sepL2_insert_acc with "Hsims") as "[Hsim _]"; eauto.
      rewrite gsim_expr_unfold. iMod ("Hsim" with "[$SI]") as "[Val|Step]".
      + iPureIntro. by erewrite fill_empty.
      + iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI Hpost]". rewrite fill_empty.
        iModIntro. iExists v_t, v_s.
        do 2 (iSplit; first done).
        inversion Hnfs; subst.
        * rewrite list_insert_id //. iFrame. iDestruct "Hpost" as (v_t' v_s' ->%of_val_inj ->%of_val_inj) "$".
        * exfalso. by eapply val_prim_step.
      + iDestruct "Step" as "[%Hred _]". destruct Hred as (e_t' & σ_t' & efs & Hstep).
        exfalso. by eapply val_prim_step.
  Qed.


  Lemma msim_step (T_t T_t' T_s: tpool Λ) (σ_t σ_t' σ_s: state Λ) i V:
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    pool_step p_t T_t σ_t i T_t' σ_t' →
    ∃ T_s' σ_s' J, pool_steps p_s T_s σ_s J T_s' σ_s' ∧ msim T_t' σ_t' T_s' σ_s' V.
  Proof.
    intros Hsim Hsafe Hstep. eapply pool_step_iff in Hstep as Hstep'.
    destruct Hstep' as (e_t & e_t' & efs & Hprim & Hlook & Hupd).
    eapply msim_length in Hsim as Hlen.
    assert (is_Some (T_s !! i)) as [e_s Hlook'].
    { eapply lookup_lt_is_Some; rewrite -Hlen; eapply lookup_lt_is_Some; eauto. }
    rewrite /msim in Hsim. eapply sat_mono in Hsim.
    - eapply sat_bupd in Hsim.
      eapply sat_exists in Hsim as [T_s' Hsim]; exists T_s'.
      eapply sat_exists in Hsim as [σ_s' Hsim]; exists σ_s'.
      eapply sat_exists in Hsim as [J Hsim]; exists J.
      eapply sat_sep in Hsim as [Hdone Hsim].
      eapply sat_elim in Hdone. split; [exact Hdone|exact Hsim].
    - simpl; clear Hsim. iIntros "(SI & %Hvals & Hsims)".
      iPoseProof (big_sepL2_insert_acc with "Hsims") as "[Hsim Hpost]"; eauto.
      rewrite gsim_expr_unfold. iMod ("Hsim" with "[$SI]") as "[Val|Step]".
      + iPureIntro. by erewrite fill_empty.
      + iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI Post]".
        iDestruct "Post" as (v_t' v_s Heq1 Heq2) "Val".
        subst e_t. exfalso. by eapply val_prim_step.
      + iDestruct "Step" as "[_ Step]".
        iMod ("Step" with "[//]") as "[(-> & SI & Hsim) | NoStutter]".
        * iModIntro. iExists T_s, σ_s, [].
          iSplit; first by iPureIntro; constructor.
          iFrame. rewrite Hupd right_id. iSplit.
          { iPureIntro. intros j Hj. eapply Hvals in Hj as (v_t & v_s & Hlook1 & Hlook2).
            exists v_t, v_s. split; last done. eapply pool_step_value_preservation, Hlook1.
            rewrite Hupd right_id in Hstep. done. }
          iSpecialize ("Hpost" $! e_t' e_s with "Hsim").
          rewrite (list_insert_id T_s) //.
        * iDestruct "NoStutter" as (e_s' e_s'' σ_s' σ_s'' efs_s Hnfs Hprim' Hlen') "(SI & Hsim & Hforks)".
          rewrite fill_empty.
          eapply no_forks_then_prim_step_pool_steps in Hnfs as (J & Hsteps & _); eauto.
          iModIntro. iExists _, _, _; iSplit; first done.
          iFrame. iSplit.
          { iPureIntro. intros j Hj. eapply Hvals in Hj as (v_t & v_s & Hlook1 & Hlook2).
            exists v_t, v_s. split; eauto using pool_step_value_preservation, pool_steps_value_preservation. }
          iSpecialize ("Hpost" $! e_t' e_s'' with "Hsim").
          rewrite Hupd. iApply (big_sepL2_app with "Hpost [Hforks]").
          by rewrite insert_length Hlen.
  Qed.

  Lemma msim_not_stuck (T_t T_s: tpool Λ) (σ_t σ_s: state Λ) V i e_t :
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    T_t !! i = Some e_t →
    ¬ stuck p_t e_t σ_t.
  Proof.
    intros Hsim Hreach Hstuck. eapply sat_elim, sat_bupd, sat_mono, Hsim.
    eapply msim_length in Hsim as Hlen.
    assert (is_Some (T_s !! i)) as [e_s Hlook'].
    { eapply lookup_lt_is_Some; rewrite -Hlen; eapply lookup_lt_is_Some; eauto. }
    iIntros "(SI & _ & Hsims)".
    iPoseProof (big_sepL2_insert_acc with "Hsims") as "[Hsim Hpost]"; eauto.
    rewrite gsim_expr_unfold. iMod ("Hsim" with "[$SI]") as "[Val|Step]".
    + iPureIntro. by erewrite fill_empty.
    + iDestruct "Val" as (e_s' σ_s' Hnfs) "[SI Post]".
      iDestruct "Post" as (v_t' v_s Heq1 Heq2) "Val".
      iModIntro. iPureIntro. intros [Heq _].
      rewrite Heq1 to_of_val in Heq. naive_solver.
    + iDestruct "Step" as "[%Hred _]".
      iModIntro. iPureIntro. intros [_ Hirr].
      by apply not_reducible in Hred.
  Qed.

  Lemma msim_sim_pool T_t σ_t T_s σ_s V:
    msim T_t σ_t T_s σ_s V →
    sat (state_interp p_t σ_t p_s σ_s T_s ∗ sim_pool (zip T_t T_s)).
  Proof.
    intros Hsim.
    eapply sat_mono, Hsim. iIntros "($ & _ & Hsims)".
    rewrite big_sepL2_alt. iDestruct "Hsims" as "[_ Hsims]".
    iApply gsim_expr_to_pool. done.
  Qed.

  (* derived lemmas *)
  Lemma msim_steps T_t T_s σ_t σ_s T_t' σ_t' I V:
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    pool_steps p_t T_t σ_t I T_t' σ_t' →
    ∃ T_s' σ_s' J, pool_steps p_s T_s σ_s J T_s' σ_s' ∧
    msim T_t' σ_t' T_s' σ_s' V.
  Proof.
    intros Hsim Hsafe; induction 1 as [T_t σ_t|T_t T_t' T_t'' σ_t σ_t' σ_t'' i I Hstep Hsteps IH] in T_s, σ_s, Hsim, Hsafe.
    - exists T_s, σ_s, []. eauto using Pool_steps_refl.
    - eapply msim_step in Hstep as (T_s' & σ_s' & J1 & Hsteps_src & Hsim'); [|by eauto..].
      eapply IH in Hsim' as (T_s'' & σ_s'' & J2 & Hsteps_src' & Hsim''); last by eapply pool_steps_safe.
      exists T_s'', σ_s'', (J1 ++ J2). split; last done.
      by eapply pool_steps_trans.
  Qed.

  Lemma msim_safety T_t T_s σ_t σ_s V:
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    pool_safe p_t T_t σ_t.
  Proof.
    intros Hsim Hsafe (T_t' & σ_t' & I & Hsteps & Hstuck).
    eapply msim_steps in Hsteps as (T_s' & σ_s' & J & Hsteps_src & Hsim'); [|eauto..].
    destruct Hstuck as (e_t & i & Hlook & Hstuck).
    eapply msim_not_stuck; eauto using pool_steps_safe.
  Qed.

  Lemma msim_fair_divergence T_t T_s σ_t σ_s V:
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    fair_div p_t T_t σ_t →
    fair_div p_s T_s σ_s.
  Proof.
    intros Hsim Hsafe Hfair.
    eapply msim_length in Hsim as Hlen.
    eapply fair_div_traditional_coind in Hfair;
    last by eapply msim_safety.
    eapply fair_div_coind_delay_iff in Hfair as [D Hfair].
    eapply msim_sim_pool in Hsim as Hpool.
    eapply fair_div_coind_traditional.
    assert (T_s = (zip T_t T_s).*2) as ->.
    { rewrite snd_zip // Hlen //. }
    eapply sim_pool_preserves_fair_termination.
    - rewrite fst_zip // Hlen //.
    - rewrite snd_zip // Hlen //.
    - rewrite snd_zip // Hlen //.
  Qed.

  Lemma msim_finish_source (T_t T_s: tpool Λ) (σ_t σ_s: state Λ) U V:
    (∀ i, i ∈ U → ∃ v_t, T_t !! i = Some (of_val v_t)) →
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    ∃ T_s' σ_s' I, pool_steps p_s T_s σ_s I T_s' σ_s' ∧ msim T_t σ_t T_s' σ_s' (V ∪ U).
  Proof.
    intros Hsub. revert V T_s σ_t σ_s.
    induction (set_wf U) as [U _ IH]; intros V T_s σ_t σ_s Hsim Hsafe.
    destruct (decide (U ≡ ∅)) as [->%leibniz_equiv|[i Hi]%set_choose].
    - exists T_s, σ_s, []. split; first constructor.
      by replace (V ∪ ∅) with V by set_solver.
    - eapply Hsub in Hi as Hx; destruct Hx as [v_t Hlook].
      eapply msim_add_val in Hsim as (T_s' & σ_s' & I & Hsteps & Hsim); [|eauto..].
      eapply (IH (U ∖ {[i]})) in Hsim as (T_s'' & σ_s'' & J & Hsteps'' & Hsim); first last.
      + by eapply pool_steps_safe.
      + set_solver.
      + set_solver.
      + exists T_s'', σ_s'', (I ++ J). split; first by eapply pool_steps_trans.
        revert Hsim.
        replace (V ∪ {[i]} ∪ (U ∖ {[i]})) with (V ∪ U); first done.
        eapply leibniz_equiv. rewrite -union_assoc. f_equiv.
        rewrite union_comm difference_union. set_solver.
  Qed.

  Lemma msim_return T_t T_t' T_s σ_t σ_s σ_t' I V:
    msim T_t σ_t T_s σ_s V →
    pool_safe p_s T_s σ_s →
    pool_steps p_t T_t σ_t I T_t' σ_t' →
    ∃ T_s' σ_s' J U,
      pool_steps p_s T_s σ_s J T_s' σ_s' ∧
      msim T_t' σ_t' T_s' σ_s' U ∧
      (∀ i v_t, T_t' !! i = Some (of_val v_t) →
      ∃ v_s, T_s' !! i = Some (of_val v_s) ∧ sat (state_interp p_t σ_t' p_s σ_s' T_s' ∗ ext_rel i v_t v_s)).
  Proof.
    (* first we exectute the simulation to v_t *)
    intros Hsim Hstuck Htgt; eapply msim_steps in Hsim as (T_s' & σ_s' & J1 & Hsrc & Hsim); [|eauto..].
    (* then we add finish all the threads where the target has been evaluated to a value *)
    eapply msim_finish_source with (U := threads T_t' ∖ active_threads T_t') in Hsim as (T_s'' & σ_s'' & J2 & Hsrc' & Hsim); first last.
    - by eapply pool_steps_safe.
    - intros i [Ht Hact]%elem_of_difference.
      eapply threads_spec in Ht as [e Hlook].
      destruct (to_val e) as [v_t|] eqn: He.
      + eapply of_to_val in He. exists v_t. by subst.
      + exfalso. eapply Hact, active_threads_spec; eauto.
    - exists T_s'', σ_s'', (J1 ++ J2), (V ∪ threads T_t' ∖ active_threads T_t').
      repeat split; eauto using pool_steps_trans.
      intros i v_t Hlook.
      eapply msim_proj_val with (i := i) in Hsim as (v_t' & v_s & Hlook1 & Hlook2 & Hsat).
      3: { eapply pool_steps_safe; [done|]. by eapply pool_steps_safe. }
      { exists v_s. split; first done. rewrite Hlook1 in Hlook.
        by eapply Some_inj, of_val_inj in Hlook as ->. }
      eapply elem_of_union_r. eapply elem_of_difference.
      rewrite threads_spec active_threads_spec. split; first eauto.
      intros (e & Hlook' & Hnval). rewrite Hlook' in Hlook.
      eapply Some_inj in Hlook. rewrite Hlook in Hnval.
      rewrite to_of_val in Hnval. naive_solver.
  Qed.

End meta_level_simulation.




Section adequacy_statement.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : simulirisG PROP Λ}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Variable (I: state Λ → state Λ → Prop).
  Variable (main: string) (u: val Λ).
  Variable (O: val Λ → val Λ → Prop).

  Let B := beh_rel I main u O.

  Lemma adequacy p_t p_s:
    (* pre *)
    sat (prog_rel p_t p_s ∗
      (∀ σ_t σ_s, ⌜I σ_t σ_s⌝ -∗ state_interp p_t σ_t p_s σ_s [of_call main u]) ∗
      progs_are p_t p_s ∗
      ext_rel 0 u u) →
    (* post *)
    (∀ v_t v_s σ_t σ_s T_s, sat (state_interp p_t σ_t p_s σ_s T_s ∗ ext_rel 0 v_t v_s) → O v_t v_s) →
    B p_t p_s.
  Proof.
    intros Hpre Hpost σ_t σ_s HI Hsafe.
    eapply (safe_call_in_prg p_s empty_ectx _ _ _ main) in Hsafe as Hlook; last (rewrite fill_empty; constructor).
    destruct Hlook as [K_s Hlook].
    assert (msim (sat:=sat) p_t p_s [of_call main u] σ_t [of_call main u] σ_s ∅) as Hsim.
    { rewrite /msim. eapply sat_mono, Hpre.
      iIntros "(Hloc & SI & Hprogs & Hunit)".
      iSpecialize ("SI" with "[//]"). iFrame.
      iSplit; first by iPureIntro; intros ??; set_solver.
      simpl. iSplit; last done.
      iApply (local_to_global_call with "Hloc Hprogs Hunit"); eauto. }
    split; last split.
    - intros Hfair. eapply msim_fair_divergence; eauto.
    - intros v_t T_t σ_t' J Hsteps.
      eapply msim_return in Hsim as (T_s & σ_s' & J' & U & Hsteps' & _ & Hvals); eauto.
      destruct (Hvals 0 v_t) as (v_s & Hlook' & Hsat); first done.
      destruct T_s as [|? T_s]; first done.
      simpl in Hlook'. injection Hlook' as [= ->].
      eapply Hpost in Hsat. eauto 10.
    - by eapply msim_safety.
  Qed.

End adequacy_statement.

Section adequacy_statement_alt.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : simulirisG PROP Λ}.
  Context {sat: PROP → Prop} {Sat: Satisfiable sat}.
  Arguments sat _%I.

  Variable (I: state Λ → state Λ → Prop).
  Variable (main: string) (u: val Λ).
  Variable (O: val Λ → val Λ → Prop).

  Let B := beh_rel I main u O.

  (** Derive from the above an adequacy theorem with just a single [sat]. *)
  Lemma adequacy_alt p_t p_s:
    sat (
      (* The programs are related *)
      prog_rel p_t p_s ∗
      (* The initial states satisfy the state interpretation *)
      (∀ σ_t σ_s, ⌜I σ_t σ_s⌝ -∗ state_interp p_t σ_t p_s σ_s [of_call main u]) ∗
      (* The programs are in the state *)
      progs_are p_t p_s ∗
      (* The "unit" argument to main is related *)
      ext_rel 0 u u ∗
      (* Logically related values are observationally related *)
      ∀ v_s v_t, ext_rel 0 v_t v_s -∗ ⌜O v_t v_s⌝) →
    B p_t p_s.
  Proof.
    intros Hsat. eapply sat_frame_intro in Hsat; last first.
    { iIntros "(H1 & H2 & H3 & H4 & F)". iSplitL "F"; first iExact "F".
      iCombine "H1 H2 H3 H4" as "H". iExact "H". }
    eapply (@adequacy PROP _ _ _ _ _ (sat_frame _) _); first apply Hsat.
    intros v_t v_s σ_t σ_s T_s Hsat_post. eapply sat_elim, sat_mono, Hsat_post.
    iIntros "(H & _ & Hval)". by iApply "H".
  Qed.

End adequacy_statement_alt.
