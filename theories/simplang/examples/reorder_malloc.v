From simuliris.simplang Require Import lang notation tactics class_instances heap_bij heapbij_refl.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.

(** * Simple example for re-ordering two allocs and then passing the related locations to an external function. *)

Section reorder.
  Context `{sbijG Σ}.

  Definition alloc2_and_cont :=
    (λ: "a", let: "v1" := Fst "a" in
             let: "v2" := Fst (Snd "a") in
             let: "cont" := Snd (Snd "a") in
             let: "l1" := Alloc "v1" in
             let: "l2" := Alloc "v2" in
             Call "cont" ("l1", "l2")
    )%E.

  Definition alloc2_and_cont' :=
    (λ: "a", let: "v1" := Fst "a" in
             let: "v2" := Fst (Snd "a") in
             let: "cont" := Snd (Snd "a") in
             let: "l1" := Alloc "v2" in
             let: "l2" := Alloc "v1" in
             Call "cont" ("l2", "l1")
    )%E.

  Lemma alloc2_reorder π:
    ⊢ sim_ectx val_rel π alloc2_and_cont alloc2_and_cont' val_rel.
  Proof.
    iIntros (v_t v_s) "Hrel". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2' & ->)).
    sim_pures.

    source_bind (Fst v_s2').
    iApply source_red_irred_unless; first done.
    iIntros ((v_s2 & v_s_cont & ->)).
    sim_pures.

    source_alloc l1_s as "Hl1_s" "Ha1_s".
    source_alloc l2_s as "Hl2_s" "Ha2_s".
    sim_pures.

    iApply sim_irred_unless.
    { destruct v_s_cont as [[] | | | ]; done. }
    iIntros ((fcont & ->)).

    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2') "(-> & #Hrel1 & Hrel2')".
    iPoseProof (val_rel_pair_source with "Hrel2'") as (v_t2 v_t_cont) "(-> & #Hrel2 & #Hrel_cont)".
    iPoseProof (val_rel_litfn_source with "Hrel_cont") as "->".
    sim_pures.

    target_alloc l1_t as "Hl1_t" "Ha1_t".
    target_alloc l2_t as "Hl2_t" "Ha2_t".
    sim_pures.

    iApply (sim_bij_insert with "Ha1_t Ha2_s Hl1_t Hl2_s Hrel1"); iIntros "#Hbij_1".
    iApply (sim_bij_insert with "Ha2_t Ha1_s Hl2_t Hl1_s Hrel2"); iIntros "#Hbij_2".

    iApply sim_call; [done | done | simpl; by eauto ].
  Qed.

End reorder.
