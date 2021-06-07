From simuliris.simplang Require Import lang notation tactics class_instances proofmode heap_bij_races.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.

(** * Examples for exploiting UB of data-races. *)

Section data_race.
  Context `{nabijG Σ}.

  (*
    problem of establishing disjointness:
    option 1: add comparsion in target (and make op sem for that realistic)
*)

  Definition remove_store_and_load_opt :=
    (λ: "a", let: "l1" := Fst "a" in
             let: "l2" := Snd "a" in
             let: "v2" := !"l2" in
             let: "r" := "v2" + "v2" in
             "l1" <- "r";;
             "r"
    )%E.

  Definition remove_store_and_load :=
    (λ: "a", let: "l1" := Fst "a" in
             let: "l2" := Snd "a" in
             "l1" <- !"l2";;
             "l1" <- !"l1" + !"l2";;
             !"l1"
    )%E.

  Lemma remove_store_and_load_sim π:
    ⊢ sim_ectx π remove_store_and_load_opt remove_store_and_load val_rel.
  Proof.
    iIntros (v_t v_s) "[Hc Hrel]". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2 & ->)).
    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2) "(-> & #Hrel1 & Hrel2')".
    sim_pures.
    sim_pures.
    source_bind (! _)%E.
    iApply source_red_irred_unless; first done.
    iIntros ((l_s2 & ->)).
    iPoseProof (val_rel_loc_source with "Hrel2'") as (l_t2 ->) "#Hrel2".
    sim_pures. simpl. rewrite -!source_red_base. do 2 iModIntro.

    sim_bind (_) (! _)%E.
  Abort.
    (* iApply (sim_bij_exploit_load with "Hrel2 Hc"); [intros; apply: no_forks_refl|done|]. *)
    (* iIntros (q v_t v_s) "Hl_t2 Hl_s2 Hv Hc". iApply sim_expr_base. *)
    (* source_load. target_load. sim_pures. *)

  (* Abort. *)

  Definition reg_promote_loop_opt f :=
    (λ: "a",
     let: "n" := Fst "a" in
     let: "x" := Snd "a" in
     let: "refn" := ref ! "n" in
     while: #0 < ! "refn" do
       Call ##f #2;;
       "refn" <- !"refn" - #1
     od;;
     if: #0 < "n" then
       "x" <- #2;;
       #2
     else
       #0
    )%E.

  Definition reg_promote_loop f :=
    (λ: "a",
     let: "n" := Fst "a" in
     let: "x" := Snd "a" in
     let: "refn" := ref ! "n" in
     let: "res" := ref #0 in
     while: #0 < ! "refn" do
       "x" <- #1;;
       "x" <- #2;;
       "res" <- !"x";;
       (* Should not access x (e.g. because it does not access the
       heap) and should not do synchronization. *)
       Call ##f !"res";;
       "refn" <- !"refn" - #1
     od;;
     !"res"
    )%E.

  Lemma reg_promote_loop_sim π f:
    ⊢ sim_ectx π (reg_promote_loop_opt f) (reg_promote_loop f) val_rel.
  Proof.
    iIntros (v_t v_s) "[Hc Hrel]". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2 & ->)).
    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2) "(-> & #Hrel1 & Hrel2')".
    sim_pures.
    sim_pures.

  Abort.

  Definition hoist_load_opt :=
    (λ: "a",
     let: "n" := Fst "a" in
     let: "m" := Snd "a" in
     if: "n" < #1 then
       #0
     else
       let: "mval" := !"m" in
       let: "r" := ref "mval" in
       let: "i" := ref #1 in
       while: ! "i" < "n" do
         "r" <- !"r" + "mval";;
         (* Call ##f "x";; *)
         "i" <- !"i" + #1
       od;;
       Free "i";;
       let: "res" := !"r" in
       Free "r";;
       "res"
    )%E.

  Definition hoist_load :=
    (λ: "a",
     let: "n" := Fst "a" in
     let: "m" := Snd "a" in
     let: "r" := ref #0  in
     let: "i" := ref #0  in
     while: ! "i" < "n" do
       "r" <- !"r" + !"m";;
       (* Call ##f "x";; *)
       "i" <- !"i" + #1
     od;;
     Free "i";;
     let: "res" := !"r" in
     Free "r";;
     "res"
    )%E.

  Lemma hoist_load_sim π:
    ⊢ sim_ectx π hoist_load_opt hoist_load val_rel.
  Proof.
    iIntros (v_t v_s) "[Hc Hrel]". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2' & ->)).
    sim_pures.

    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2) "(-> & #Hrel1 & #Hrel2)".
    sim_pures.
    source_alloc lr_s as "Hlr_s" "Hfr_s". sim_pures.
    source_alloc li_s as "Hli_s" "Hfi_s". sim_pures.
    source_while. source_load.
    source_bind (_ < _)%E. iApply source_red_irred_unless; first done.
    iIntros ([[??] [??]]); simplify_eq.
    iDestruct (val_rel_litint_source with "Hrel1") as %->. sim_pures. sim_pures.
    case_bool_decide; [rewrite bool_decide_false;[|lia]|rewrite bool_decide_true;[|lia]]; sim_pures.
    - source_free. sim_pures. source_load. sim_pures. source_free. sim_pures. by sim_val.
    - source_bind (! _)%E. iApply source_red_irred_unless; first done.
      iIntros ([l_s ?]); simplify_eq.
      iDestruct (val_rel_loc_source with "Hrel2") as (l_t ->) "Hbij".
      do 2 iApply source_red_base. do 2 iModIntro.
      iApply (sim_bij_exploit_load with "Hbij Hc"); [|done|]. {
        intros. reach_or_stuck_fill (! _)%E => /=.
        apply: reach_or_stuck_refl. apply: post_in_ectx_intro. naive_solver.
      }
      iIntros (q v_t v_s) "Hl_t Hl_s #Hv Hc".
      iDestruct (heap_mapsto_ne with "Hlr_s Hli_s") as %Hne1.
      iDestruct (heap_mapsto_ne with "Hlr_s Hl_s") as %Hne2.
      iDestruct (heap_mapsto_ne with "Hli_s Hl_s") as %Hne3.
      source_load. sim_pures. source_load. sim_pures.
      source_bind (_ + _)%E. iApply source_red_irred_unless; first done.
      iIntros ([[??] [m ?]]); simplify_eq.
      iDestruct (val_rel_litint_source with "Hv") as %->. sim_pures. rewrite Z.add_0_l.
      source_store. source_load. source_store. sim_pures.

      target_load. target_alloc lr_t as "Hlr_t" "Hfr_t". target_alloc li_t as "Hli_t" "Hfi_t".
      sim_pures.
      iApply (sim_bij_insert with "Hfi_t Hfi_s Hli_t Hli_s []"); [done|]. iIntros "#Hbiji".
      iApply (sim_bij_insert with "Hfr_t Hfr_s Hlr_t Hlr_s []"); [done|]. iIntros "#Hbijr".
      sim_bind (While _ _) (While _ _).
      iApply (sim_while_while _ _ _ _ _ (
         l_t ↦t{#q} #m ∗ l_s ↦s{#q} #m ∗ na_locs π (<[l_s:=(l_t, NaRead q)]> ∅))%I with "[-]").
      { eauto with iFrame. }
      iIntros "!> (Hl_t&Hl_s&Hc)".
      sim_bind (! _)%E (! _)%E.
      iApply (sim_bij_load_na with "Hbiji Hc"); [by simplify_map_eq|].
      iIntros (??) "Hv' Hc". sim_val.
      source_bind (_ < _)%E. iApply source_red_irred_unless; first done.
      iIntros ([[??] [??]]); simplify_eq.
      iDestruct (val_rel_litint_source with "Hv'") as %->. sim_pures. sim_pures.
      case_bool_decide; sim_pures.
      + source_load. sim_pures.
        sim_bind (! _)%E (! _)%E.
        iApply (sim_bij_load_na with "Hbijr Hc"); [by simplify_map_eq|].
        iIntros (??) "Hv'' Hc". sim_val.
        source_bind (_ + _)%E. iApply source_red_irred_unless; first done.
        iIntros ([[??] [??]]); simplify_eq.
        iDestruct (val_rel_litint_source with "Hv''") as %->. sim_pures. sim_pures.
        sim_bind (_ <- _)%E (_ <- _)%E.
        iApply (sim_bij_store_na with "Hbijr Hc"); [by simplify_map_eq| done |].
        iIntros "Hc". sim_val. sim_pures.

        sim_bind (! _)%E (! _)%E.
        iApply (sim_bij_load_na with "Hbiji Hc"); [by simplify_map_eq|].
        iIntros (??) "Hv''' Hc". sim_val.
        source_bind (_ + _)%E. iApply source_red_irred_unless; first done.
        iIntros ([[??] [??]]); simplify_eq.
        iDestruct (val_rel_litint_source with "Hv'''") as %->. sim_pures. sim_pures.
        sim_bind (_ <- _)%E (_ <- _)%E.
        iApply (sim_bij_store_na with "Hbiji Hc"); [by simplify_map_eq| done |].
        iIntros "Hc". sim_val. sim_pures.

        iApply sim_expr_base. iRight. by iFrame.
      + iApply sim_expr_base. iLeft. iApply lift_post_val.
        sim_pures.
        sim_bind (FreeN _ _)%E (FreeN _ _)%E.
        iApply (sim_bij_free with "Hbiji Hc"). {
          move => i ?. rewrite lookup_insert_ne //.
          destruct (decide (i = 0%Z)); [subst |lia]. by rewrite loc_add_0.
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
        iIntros "Hc". sim_val. sim_pures. by sim_val.
  Qed.

  (* TODO: try also other direction (or maybe another example that adds loads and that makes more sense) *)

  Definition register_pressure_opt :=
    (λ: "a",
     let: "z" := !"a" + #1 in
     "z" + !"a"
    )%E.

  Definition register_pressure_load :=
    (λ: "a",
     let: "y" := !"a" in
     let: "z" := "y" + #1 in
     "z" + "y"
    )%E.


  (* TODO: go over memory model papers (promising semantics paper)

   prove some reorderings:
   - reordering reads
   - reordering writes to different locations
   - compact two reads
   - ...

   TODO: try to find something about Concurrent CompCert, what is used by VST
*)

End data_race.
