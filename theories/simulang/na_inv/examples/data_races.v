From iris Require Import bi.bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior.
From simuliris.simulang.na_inv Require Export inv.
From simuliris.simulang.na_inv Require Import readonly_refl adequacy.
From iris.prelude Require Import options.

Import bi.

(** * Examples for exploiting UB of data-races. *)

Section data_race.
  Context `{naGS Σ}.

  (** This optimization replaces multiples loads with a single load. *)
  Definition remove_load_s : expr :=
    "l" <- !"l" + !"l";;
    !"l".

  Definition remove_load_t : expr :=
    let: "v" := !"l" in
    let: "r" := "v" + "v" in
    "l" <- "r";;
    "r".

  Lemma remove_load_sim:
    ⊢ log_rel remove_load_t remove_load_s.
  Proof.
    log_rel.
    iIntros "%v_t %v_s #Hv_l !# %π Hc". simpl_subst.

    source_bind (! _)%E. iApply source_red_irred_unless. iIntros ([l_s ->]).
    iPoseProof (gen_val_rel_loc_source with "Hv_l") as (l_t ->) "#Hl". iApply source_red_base. iModIntro.
    to_sim. iApply (sim_bij_exploit_store with "Hl Hc"); [|done|].
    { intros. reach_or_stuck_fill (_ <- _)%E => /=.
      (* skip over first load *)
      reach_or_stuck_bind (! _)%E.
      eapply reach_or_stuck_irred; first apply _.
      intros (l & v & n & [= <-] & Hs_mem). eapply reach_or_stuck_load; [done.. | ].
      eapply reach_or_stuck_refl. simpl.

      (* skip over snd load *)
      reach_or_stuck_bind (! _)%E.
      eapply reach_or_stuck_load; [done.. | ]. eapply reach_or_stuck_refl.

      (* skip over add *)
      reach_or_stuck_bind (_ + _)%E.
      eapply reach_or_stuck_irred; first apply _.
      intros [(z & ->) _].
      eapply reach_or_stuck_pure; first apply _; first done.
      eapply reach_or_stuck_refl.

      apply: reach_or_stuck_irred => ?.
      apply: reach_or_stuck_refl. apply post_in_ectx_intro. naive_solver.
    }
    iIntros (v_t v_s) "Hl_t Hl_s #Hv Hc". do 2 source_load. target_load.
    source_bind (_ + _)%E. iApply source_red_irred_unless.
    iIntros "[(%z & ->) _]". iPoseProof (gen_val_rel_litint_source with "Hv") as "->".
    sim_pures. source_store. to_target. target_let. target_binop.
    (* TODO: something weird is going on with the simplification here.
      Z.add is unfolded... *)
    generalize (z + z)%Z => z'.
    target_store. sim_pures. source_load.
    iApply (sim_bij_release NaExcl with "Hl Hc [$] [$] []"); [ by simplify_map_eq| done| ].
    iIntros "Hc". rewrite delete_insert //.
    sim_val. iFrame. done.
  Qed.

  (** This optimization hoists the read of "n" out of the loop. *)
  Definition hoist_load_s : expr :=
     let: "r" := ref #0  in
     let: "i" := ref #0  in
     while: !"i" ≠ ! "n" do
       "r" <- !"r" + !"i";;
       "i" <- !"i" + #1
     od;;
     let: "res" := !"r" in
     Free "r";;
     Free "i";;
     "res".

  Definition hoist_load_t : expr :=
     let: "r" := ref #0  in
     let: "i" := ref #0  in
     let: "nval" := ! "n" in
     while: !"i" ≠ "nval" do
       "r" <- !"r" + !"i";;
       "i" <- !"i" + #1
     od;;
     let: "res" := !"r" in
     Free "r";;
     Free "i";;
     "res".

  Lemma int_is_unboxed (z : Z) : val_is_unboxed #z.
  Proof. done. Qed.

  Lemma hoist_load_sim:
    ⊢ log_rel hoist_load_t hoist_load_s.
  Proof.
    log_rel.
    iIntros "%n_t1 %n_s1 #Hrel1 !# %π Hc".

    source_alloc lr_s as "Hlr_s" "Hfr_s". sim_pures.
    source_alloc li_s as "Hli_s" "Hfi_s". sim_pures.
    target_alloc lr_t as "Hlr_t" "Hfr_t". sim_pures.
    target_alloc li_t as "Hli_t" "Hfi_t". sim_pures.
    destruct (if n_s1 is #(LitLoc _) then true else false) eqn:Heq. 2: {
      source_while.
      source_bind (! _)%E. iApply source_red_irred_unless.
      iIntros ([l_s ?]); simplify_eq.
    }
    destruct n_s1 as [[| | | |n_s |]| | |] => //.
    iDestruct (gen_val_rel_loc_source with "Hrel1") as (n_t ->) "Hbij".
    iApply (sim_bij_exploit_load with "Hbij Hc"); [|done|]. {
      intros.
      reach_or_stuck_fill (While _ _)%E => /=.
      apply: reach_or_stuck_head_step; [ by econstructor|].
      reach_or_stuck_fill (! _)%E => /=.
      apply: reach_or_stuck_irred => ?.
      apply: reach_or_stuck_refl. apply: post_in_ectx_intro. naive_solver.
    }
    iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
    iDestruct (heap_mapsto_ne with "Hlr_s Hl_s") as %Hne1.
    iDestruct (heap_mapsto_ne with "Hli_s Hl_s") as %Hne2.

    (* hint for the [sim_pure] automation to reduce the comparison *)
    specialize int_is_unboxed as Hunb.

    (* initiate coinduction *)
    target_load. sim_pures.
    sim_bind (While _ _) (While _ _).
    (* the invariant: we just thread through our ownership, with the invariant that
      [r] and [i] point to the same integer values.
      (retaining this information eases our live in the loop proof significantly)
    *)
    set (inv := (
      ∃ z_i z_r : Z,
      †lr_s…s 1 ∗ †li_s…s 1 ∗ †lr_t…t 1 ∗ †li_t…t 1 ∗
      lr_s ↦s #z_r ∗ li_s ↦s #z_i ∗ lr_t ↦t #z_r ∗ li_t ↦t #z_i ∗
      n_t ↦t{#q} v_t ∗ n_s ↦s{#q} v_s ∗ na_locs π (<[n_s:=(n_t, NaRead q)]> ∅))%I).
    iApply (sim_while_while _ _ _ _ _ inv with "[-]").
    { rewrite /inv. eauto with iFrame. }
    iIntros "!> (%z_i & %z_r & ? & ? & ? & ? & Hlr_s & Hli_s & Hlr_t & Hli_t & Hl_t&Hl_s&Hc)".
    source_load. source_load. target_load. sim_pures.
    destruct (bool_decide (#z_i = v_s)) eqn:Heq_v_s.
    - (* compare equal in the source; leave the loop *)
      apply bool_decide_eq_true_1 in Heq_v_s. subst v_s.
      val_discr_source "Hv".
      rewrite bool_decide_eq_true_2; last done.
      sim_pures. iApply sim_expr_base. iLeft. iApply lift_post_val.

      sim_pures. source_load. target_load. sim_pures.
      (* cleanup *)
      source_free. source_free. target_free. target_free. sim_pures.
      iApply (sim_bij_release (NaRead q) with "Hbij Hc Hl_t Hl_s [//]").
      { apply lookup_insert. }
      rewrite delete_insert; last done. iIntros "Hc".
      sim_val. eauto.
    - (* compare unequal and take another trip around the loop *)
      apply bool_decide_eq_false_1 in Heq_v_s.
      destruct (bool_decide (#z_i = v_t)) eqn:Heq_v_t.
      { (* contradiction *)
        apply bool_decide_eq_true_1 in Heq_v_t. subst v_t.
        val_discr_target "Hv". done.
      }
      sim_pures.
      source_load. source_load. source_store.
      source_load. source_store.
      target_load. target_load. target_store.
      target_load. target_store.
      sim_pures. iApply sim_expr_base. iRight.
      iSplitR; first done. iSplitR; first done.
      iExists (z_i + 1)%Z, (z_r + z_i)%Z.
      iFrame.
  Qed.

  (** This optimization hoists the read of "m" out of the loop. We
  need to unrole the loop once because the loop condition can be an
  arbitrary expression [e] that does not write to the heap. *)
  Definition hoist_load_unknown_s (e : expr) : expr :=
     let: "r" := ref #0  in
     let: "i" := ref #0  in
     while: e do
       "r" <- !"r" + !"m";;
       "i" <- !"i" + #1
     od;;
     Free "i";;
     let: "res" := !"r" in
     Free "r";;
     "res".

  Definition hoist_load_unknown_t (e : expr) : expr :=
    let: "i" := ref #0 in
    if: e then
      let: "mval" := !"m" in
      let: "r" := ref "mval" in
      "i" <- !"i" + #1;;
      while: e do
        "r" <- !"r" + "mval";;
        "i" <- !"i" + #1
      od;;
      Free "i";;
      let: "res" := !"r" in
      Free "r";;
      "res"
    else
      Free "i";;
      #0.

  Lemma hoist_load_unknown_sim e:
    free_vars e ⊆ list_to_set ["n"; "i"] →
    gen_expr_wf readonly_wf e →
    ⊢ log_rel (hoist_load_unknown_t e) (hoist_load_unknown_s e).
  Proof.
    move => He ?. log_rel.
    iIntros "%v_t1 %v_s1 #Hrel1 %v_t2 %v_s2 #Hrel2 !# %π Hc".

    source_alloc lr_s as "Hlr_s" "Hfr_s". sim_pures.
    source_alloc li_s as "Hli_s" "Hfi_s". sim_pures.
    target_alloc li_t as "Hli_t" "Hfi_t". sim_pures.
    iApply sim_update_si. iApply (sim_bij_freeable_ne_val with "Hrel1 Hfi_s"). iIntros (Hne3) "Hfi_s".
    iApply sim_update_si. iApply (sim_bij_freeable_ne_val with "Hrel1 Hfr_s"). iIntros (Hne1) "Hfr_s".
    iApply (sim_bij_insert with "Hfi_t Hfi_s Hli_t Hli_s []"); [done..|]. iIntros "#Hbiji".
    source_while. to_sim.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply (sim_refl with "[] [Hc]");
      [compute_done | etrans; [eassumption|compute_done]
       | apply: readonly_log_rel_structural [] ∅ | done | | |]. {
        rewrite !dom_insert_L. iApply big_sepS_intro. iIntros "!#" (x Hin).
        rewrite map_lookup_zip_with.
        destruct (decide (x = "n")); [| destruct (decide (x = "i")); [|exfalso; set_solver]]; by simplify_map_eq.
    }
    { iFrame. unfold mapsto_list, na_locs_in_mapsto_list. iSplit; [|done]. iPureIntro. set_solver. }
    iIntros (v_t v_s) "(_ & Hc & _) Hv". iApply lift_post_val.
    source_bind (If _ _ _). discr_source. val_discr_source "Hv".
    revert select (bool) => -[]; sim_pures; sim_pures; last first.
    - sim_bind (Free _) (Free _). iApply (sim_bij_free with "Hbiji Hc"); [done|]. iIntros "Hc".
      sim_val. source_load. source_free. sim_pures. sim_val. by iFrame.
    - source_bind (! _)%E. iApply source_red_irred_unless.
      iIntros ([l_s ?]); simplify_eq.
      iDestruct (gen_val_rel_loc_source with "Hrel1") as (l_t ->) "Hbij".
      do 3 iApply source_red_base. do 3 iModIntro.
      iApply (sim_bij_exploit_load with "Hbij Hc"); [|done|]. {
        intros. reach_or_stuck_fill (! _)%E => /=.
        apply: reach_or_stuck_irred => ?.
        apply: reach_or_stuck_refl. apply: post_in_ectx_intro. naive_solver.
      }
      iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
      iDestruct (heap_mapsto_ne with "Hlr_s Hl_s") as %Hne2.
      source_load. sim_pures. source_load. sim_pures.
      source_bind (_ + _)%E. iApply source_red_irred_unless.
      iIntros ([[??] [m ?]]); simplify_eq.
      iDestruct (gen_val_rel_litint_source with "Hv") as %->. sim_pures. rewrite Z.add_0_l.
      source_store.
      target_load. target_alloc lr_t as "Hlr_t" "Hfr_t". sim_pures.
      iApply (sim_bij_insert with "Hfr_t Hfr_s Hlr_t Hlr_s []"); [done..|]. iIntros "#Hbijr".
      sim_bind (! _)%E (! _)%E. iApply (sim_bij_load with "Hbiji Hc"); [|done|].
      { rewrite lookup_insert_ne //. by destruct l_s, li_s => -[??]. }
      iIntros (v_t v_s) "Hv1 Hc". sim_val.
      source_bind (_ + _)%E. discr_source. val_discr_source "Hv1"; simplify_eq. sim_pures. sim_pures.
      sim_bind (_ <- _)%E (_ <- _)%E. iApply (sim_bij_store_na with "Hbiji Hc"); [|done|].
      { rewrite lookup_insert_ne //. by destruct l_s, li_s => -[??]. }
      iIntros "Hc". sim_val. sim_pures.

      sim_bind (While _ _) (While _ _).
      iApply (sim_while_while _ _ _ _ _ (
         l_t ↦t{#q} #m ∗ l_s ↦s{#q} #m ∗ na_locs π (<[l_s:=(l_t, NaRead q)]> ∅))%I with "[-]").
      { eauto with iFrame. }
      iIntros "!> (Hl_t&Hl_s&Hc)".
      sim_bind (subst_map _ _) (subst_map _ _).
      iApply (sim_refl with "[] [Hc Hl_t Hl_s]");
        [compute_done | etrans; [eassumption|compute_done]
         | apply (readonly_log_rel_structural [(l_t, l_s, #m ,#m , q)]) | done | | |]. {
        rewrite !dom_insert_L. iApply big_sepS_intro. iIntros "!#" (x Hin).
        rewrite map_lookup_zip_with.
        destruct (decide (x = "n")); [| destruct (decide (x = "i")); [|exfalso; set_solver]]; by simplify_map_eq.
      } {
        iFrame "∗ Hrel1". iSplit; [| by eauto ]. iPureIntro.
        move => ??? /lookup_insert_Some[[??]|[??]]; simplify_eq. by eexists 0, _, _.
      }
      iIntros (??) "(_ & Hc & Hm) Hb". rewrite /mapsto_list /=. iApply lift_post_val.
      iDestruct "Hm" as "[(Hl_t & Hl_s & _ & _) _]".
      discr_source. val_discr_source "Hb".
      revert select (bool) => -[]; sim_pures.
      + source_load. sim_pures.
        sim_bind (! _)%E (! _)%E.
        iApply (sim_bij_load_na with "Hbijr Hc"); [by simplify_map_eq|].
        iIntros (??) "Hv'' Hc". sim_val.
        source_bind (_ + _)%E. discr_source. val_discr_source "Hv''"; simplify_eq. sim_pures. sim_pures.
        sim_bind (_ <- _)%E (_ <- _)%E.
        iApply (sim_bij_store_na with "Hbijr Hc"); [by simplify_map_eq| done |].
        iIntros "Hc". sim_val. sim_pures.

        sim_bind (! _)%E (! _)%E.
        iApply (sim_bij_load_na with "Hbiji Hc").
        { rewrite lookup_insert_ne //. by destruct l_s, li_s => -[??]. }
        iIntros (??) "Hv''' Hc". sim_val.
        source_bind (_ + _)%E. discr_source. val_discr_source "Hv'''"; simplify_eq. sim_pures. sim_pures.
        sim_bind (_ <- _)%E (_ <- _)%E.
        iApply (sim_bij_store_na with "Hbiji Hc"); [ | done |].
        { rewrite lookup_insert_ne //. by destruct l_s, li_s => -[??]. }
        iIntros "Hc". sim_val. sim_pures.

        iApply sim_expr_base. iRight. by iFrame.
      + iApply sim_expr_base. iLeft. iApply lift_post_val.
        sim_pures. sim_bind (FreeN _ _)%E (FreeN _ _)%E.
        iApply (sim_bij_free with "Hbiji Hc"). {
          move => i ?. rewrite lookup_insert_ne //. by destruct l_s, li_s => -[??].
        }
        iIntros "Hc". sim_val. sim_pures.
        sim_bind (! _)%E (! _)%E.
        iApply (sim_bij_load_na with "Hbijr Hc"); [by simplify_map_eq|].
        iIntros (??) "Hv'' Hc". sim_val. sim_pures.
        sim_bind (FreeN _ _)%E (FreeN _ _)%E.
        iApply (sim_bij_free with "Hbijr Hc"). {
          move => i ?. rewrite lookup_insert_ne //.
          destruct (decide (i = 0%Z)); [subst |lia]. by rewrite loc_add_0.
        }
        iIntros "Hc".
        iApply (sim_bij_release (NaRead _) with "Hbij Hc [$] [$] Hv"); [by simplify_map_eq| ].
        iIntros "Hc". rewrite delete_insert //.
        sim_val. sim_pures. sim_val; by iFrame.
  Qed.

End data_race.

Section closed.
  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma hoist_load_ctx :
    ctx_ref hoist_load_t hoist_load_s.
  Proof.
    intros ??.
    set Σ := #[naΣ].
    apply (log_rel_adequacy Σ)=>?.
    by apply hoist_load_sim.
  Qed.

  (** Obtain a closed proof of [ctx_ref]. *)
  Lemma hoist_load_unknown_ctx e :
    free_vars e ⊆ list_to_set ["n"; "i"] →
    gen_expr_wf readonly_wf e →
    ctx_ref (hoist_load_unknown_t e) (hoist_load_unknown_s e).
  Proof.
    intros ??.
    set Σ := #[naΣ].
    apply (log_rel_adequacy Σ)=>?.
    by apply hoist_load_unknown_sim.
  Qed.
End closed.
