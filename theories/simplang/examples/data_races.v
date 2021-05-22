From simuliris.simplang Require Import lang notation tactics class_instances heap_bij.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.

(** * Examples for exploiting UB of data-races. *)

Section data_race.
  Context `{sbijG Σ}.

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
    ⊢ sim_ectx val_rel π remove_store_and_load_opt remove_store_and_load val_rel.
  Proof.
    iIntros (v_t v_s) "Hrel". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2 & ->)).
    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2) "(-> & #Hrel1 & Hrel2')".
    sim_pures.
    sim_pures.

  Abort.

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
    ⊢ sim_ectx val_rel π (reg_promote_loop_opt f) (reg_promote_loop f) val_rel.
  Proof.
    iIntros (v_t v_s) "Hrel". sim_pures.

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
     let: "m" := Fst (Snd "a") in
     let: "x" := Snd (Snd "a") in
     let: "refi" := ref #0 in
     if: "n" < #1 then
       #0
     else
       let: "mval" := !"m" in
       while: ! "refi" < "n" do
         "x" <- "mval";;
         "refi" <- !"refi" + #1
       od;;
       #0
    )%E.

  Definition hoist_load :=
    (λ: "a",
     let: "n" := Fst "a" in
     let: "m" := Fst (Snd "a") in
     let: "x" := Snd (Snd "a") in
     let: "refi" := ref #0 in
     while: ! "refi" < "n" do
       "x" <- !"m";;
       "refi" <- !"refi" + #1
     od;;
       #0
    )%E.

  Lemma hoist_load_sim π:
    ⊢ sim_ectx val_rel π hoist_load_opt hoist_load val_rel.
  Proof.
    iIntros (v_t v_s) "Hrel". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2' & ->)).
    sim_pures.

    source_bind (Fst v_s2').
    iApply source_red_irred_unless; first done.
    iIntros ((v_s2 & v_s3 & ->)).
    sim_pures.

    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2') "(-> & #Hrel1 & Hrel2')".
    iPoseProof (val_rel_pair_source with "Hrel2'") as (v_t2 v_t3) "(-> & #Hrel2 & Hrel3)".
    sim_pures.

  Abort.
End data_race.
