From simuliris.simplang Require Import lang notation tactics class_instances proofmode gen_log_rel parallel_subst wf.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang.na_inv Require Export inv.
From simuliris.simplang.na_inv Require Import readonly_refl adequacy.

(** * Examples for exploiting UB of data-races. *)

Section data_race.
  Context `{naGS Σ}.


  (*
    problem of establishing disjointness:
    option 1: add comparsion in target (and make op sem for that realistic)
*)

  Definition remove_store_and_load_opt : expr :=
    let: "v2" := !"l2" in
    let: "r" := "v2" + "v2" in
    "l1" <- "r";;
    "r".


  Definition remove_store_and_load : expr :=
    "l1" <- !"l2";;
    "l1" <- !"l1" + !"l2";;
    !"l1".

  Lemma remove_store_and_load_sim:
    ⊢ log_rel remove_store_and_load_opt remove_store_and_load.
  Proof.
    log_rel.
    iIntros "%v2_t %v2_s #Hv2 %v1_t %v1_s #Hv1 !# %π Hc". simpl_subst.

    sim_bind (! _)%E (! _)%E. iApply sim_irred_unless; first done. iIntros ([l1_s ->]).
    iPoseProof (gen_val_rel_loc_source with "Hv1") as (l_t1 ->) "#Hl1".
    iApply (sim_bij_exploit_load with "Hl1 Hc"); [|done|].
    { intros. apply: reach_or_stuck_refl. by apply: post_in_ectx_intro. }
    iIntros (q v_t v_s) "Hl1_t Hl1_s Hv Hc". source_load. target_load. sim_val. sim_pures.
    sim_bind (Val v_t) (_ <- _)%E. iApply sim_irred_unless; first done. iIntros ([l2_s ->]).
    iPoseProof (gen_val_rel_loc_source with "Hv2") as (l_t2 ->) "#Hl2".

    destruct (decide (l1_s = l2_s)); simplify_eq.
  Abort.

  Definition reg_promote_loop_opt fname : expr :=
     let: "refn" := ref ! "n" in
     while: #0 < ! "refn" do
       Call f#fname #2;;
       "refn" <- !"refn" - #1
     od;;
     if: #0 < "n" then
       "x" <- #2;;
       #2
     else
       #0.


  Definition reg_promote_loop fname : expr :=
     let: "refn" := ref ! "n" in
     let: "res" := ref #0 in
     while: #0 < ! "refn" do
       "x" <- #1;;
       "x" <- #2;;
       "res" <- !"x";;
       (* Should not access x (e.g. because it does not access the
       heap) and should not do synchronization. *)
       Call f#fname !"res";;
       "refn" <- !"refn" - #1
     od;;
     !"res".

  Lemma reg_promote_loop_sim f:
    ⊢ log_rel (reg_promote_loop_opt f) (reg_promote_loop f).
  Proof.
    log_rel.
  Abort.

  Definition hoist_load_opt (e : expr) : expr :=
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

  Definition hoist_load (e : expr) : expr :=
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

  Lemma hoist_load_sim e:
    free_vars e = list_to_set ["n"; "i"] →
    gen_expr_wf readonly_wf e →
    ⊢ log_rel (hoist_load_opt e) (hoist_load e).
  Proof.
    move => He ?. log_rel.
    iIntros "%v_t1 %v_s1 #Hrel1 %v_t2 %v_s2 #Hrel2 !# %π Hc".

    source_alloc lr_s as "Hlr_s" "Hfr_s". sim_pures.
    source_alloc li_s as "Hli_s" "Hfi_s". sim_pures.
    target_alloc li_t as "Hli_t" "Hfi_t". sim_pures.
    iApply sim_update_si. iApply (sim_bij_freeable_ne_val with "Hrel1 Hfi_s"). iIntros (Hne3) "Hfi_s".
    iApply sim_update_si. iApply (sim_bij_freeable_ne_val with "Hrel1 Hfr_s"). iIntros (Hne1) "Hfr_s".
    iApply (sim_bij_insert with "Hfi_t Hfi_s Hli_t Hli_s []"); [done|]. iIntros "#Hbiji".
    source_while. to_sim.
    sim_bind (subst_map _ _) (subst_map _ _).
    iApply (sim_refl with "[] [Hc]");
      [compute_done | rewrite He; compute_done
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
    - source_bind (! _)%E. iApply source_red_irred_unless; first done.
      iIntros ([l_s ?]); simplify_eq.
      iDestruct (gen_val_rel_loc_source with "Hrel1") as (l_t ->) "Hbij".
      do 3 iApply source_red_base. do 3 iModIntro.
      iApply (sim_bij_exploit_load with "Hbij Hc"); [|done|]. {
        intros. reach_or_stuck_fill (! _)%E => /=.
        apply: reach_or_stuck_refl. apply: post_in_ectx_intro. naive_solver.
      }
      iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
      iDestruct (heap_mapsto_ne with "Hlr_s Hl_s") as %Hne2.
      source_load. sim_pures. source_load. sim_pures.
      source_bind (_ + _)%E. iApply source_red_irred_unless; first done.
      iIntros ([[??] [m ?]]); simplify_eq.
      iDestruct (gen_val_rel_litint_source with "Hv") as %->. sim_pures. rewrite Z.add_0_l.
      source_store.
      target_load. target_alloc lr_t as "Hlr_t" "Hfr_t". sim_pures.
      iApply (sim_bij_insert with "Hfr_t Hfr_s Hlr_t Hlr_s []"); [done|]. iIntros "#Hbijr".
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
        [compute_done | rewrite He; compute_done
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

  (* TODO: try also other direction (or maybe another example that adds loads and that makes more sense) *)

  Definition register_pressure_opt : expr :=
     let: "z" := !"a" + #1 in
     "z" + !"a".

  Definition register_pressure_load : expr :=
     let: "y" := !"a" in
     let: "z" := "y" + #1 in
     "z" + "y".


  (* TODO: go over memory model papers (promising semantics paper)

   prove some reorderings:
   - reordering reads
   - reordering writes to different locations
   - compact two reads
   - ...

   TODO: try to find something about Concurrent CompCert, what is used by VST
*)

End data_race.

Section closed.
  (** Obtain a closed proof of [ctx_rel]. *)
  Lemma hoist_load_ctx e :
    free_vars e = list_to_set ["n"; "i"] →
    gen_expr_wf readonly_wf e →
    ctx_rel (hoist_load_opt e) (hoist_load e).
  Proof.
    intros ??.
    set Σ := #[naΣ].
    apply (log_rel_adequacy Σ)=>?.
    by apply hoist_load_sim.
  Qed.
End closed.
