From simuliris.simplang Require Import lang notation tactics class_instances heap_bij.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.

(** * Simple example for re-ordering two allocs and then passing the related locations to an external function. *)

Section reorder.
  Context `{sbijG Σ}.

  Fixpoint val_rel (v_t v_s : val) {struct v_s} :=
    (match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
        l_t ↔h l_s
    | LitV l_t, LitV l_s =>
        ⌜l_t = l_s⌝
    | PairV v1_t v2_t, PairV v1_s v2_s =>
        val_rel v1_t v1_s ∧ val_rel v2_t v2_s
    | InjLV v_t, InjLV v_s =>
        val_rel v_t v_s
    | InjRV v_t, InjRV v_s =>
        val_rel v_t v_s
    | _,_ => False
    end)%I.
  Instance : sheapInv Σ := heap_bij_inv val_rel.
  Instance val_rel_pers v_t v_s : Persistent (val_rel v_t v_s).
  Proof.
    induction v_s as [[] | | | ] in v_t |-*; destruct v_t as [ [] | | | ]; apply _.
  Qed.

  Lemma val_rel_pair_source v_t v_s1 v_s2 :
    val_rel v_t (v_s1, v_s2) -∗
    ∃ v_t1 v_t2, ⌜v_t = PairV v_t1 v_t2⌝ ∗
      val_rel v_t1 v_s1 ∗
      val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_t as [[] | v_t1 v_t2 | |]; simpl; try done.
    iExists v_t1, v_t2. iDestruct "H" as "[#H1 #H2]". eauto.
  Qed.

  Lemma val_rel_litfn_source v_t fn_s :
    val_rel v_t (LitV $ LitFn $ fn_s) -∗ ⌜v_t = LitV $ LitFn $ fn_s⌝.
  Proof.
    simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done.
  Qed.

  Lemma val_rel_loc_source v_t l_s :
    val_rel v_t (LitV $ LitLoc l_s) -∗
    ∃ l_t, ⌜v_t = LitV $ LitLoc l_t⌝ ∗ l_t ↔h l_s.
  Proof.
    destruct v_t as [[ | | | | l_t | ] | | | ]; simpl;
        first [iIntros "%Ht"; congruence | iIntros "#Ht"; eauto].
  Qed.


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

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  Lemma alloc2_reorder :
    ⊢ sim_ectx val_rel alloc2_and_cont alloc2_and_cont' val_rel.
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

    source_alloc l1_s as "Hl1_s".
    source_alloc l2_s as "Hl2_s".
    sim_pures.

    iApply sim_irred_unless.
    { destruct v_s_cont as [[] | | | ]; done. }
    iIntros ((fcont & ->)).

    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2') "(-> & #Hrel1 & Hrel2')".
    iPoseProof (val_rel_pair_source with "Hrel2'") as (v_t2 v_t_cont) "(-> & #Hrel2 & #Hrel_cont)".
    iPoseProof (val_rel_litfn_source with "Hrel_cont") as "->".
    sim_pures.

    target_alloc l1_t as "Hl1_t".
    target_alloc l2_t as "Hl2_t".
    sim_pures.

    iApply (sim_bij_insert with "Hl1_t Hl2_s Hrel1"); iIntros "#Hbij_1".
    iApply (sim_bij_insert with "Hl2_t Hl1_s Hrel2"); iIntros "#Hbij_2".

    iApply sim_call; [done | done | simpl; by eauto ].
  Qed.

  Definition alloc2_use :=
    (λ: "a", let: "l1" := Fst "a" in
             let: "l2" := Snd "a" in
             let: "v1" := ! "l1" in
             let: "v2" := ! "l2" in
             ("v1", "v2")
    )%E.

  Lemma use_related :
    ⊢ sim_ectx val_rel alloc2_use alloc2_use val_rel.
  Proof.
    iIntros (v_t v_s) "Hrel". sim_pures.

    source_bind (Fst v_s).
    iApply source_red_irred_unless; first done.
    iIntros ((v_s1 & v_s2 & ->)).
    sim_pures.

    iPoseProof (val_rel_pair_source with "Hrel") as (v_t1 v_t2) "(-> & Hrel1 & Hrel2)".
    sim_pures.

    source_bind (! v_s1)%E.
    iApply source_red_irred_unless; first done.
    iIntros ((l_s & ->)).
    iApply source_red_base; iModIntro.
    to_sim.
    iPoseProof (val_rel_loc_source with "Hrel1") as (l_t) "(-> & #Hbij1)".
    sim_load v_t1 v_s1 as "Hv1".
    sim_pures.

    source_bind (! v_s2)%E.
    iApply source_red_irred_unless; first done.
    iIntros ((l_s2 & ->)).
    iApply source_red_base; iModIntro.
    to_sim.
    iPoseProof (val_rel_loc_source with "Hrel2") as (l_t2) "(-> & #Hbij2)".
    sim_load v_t2 v_s2 as "Hv2".
    sim_pures.

    iModIntro; simpl. eauto.
  Qed.
End reorder.
