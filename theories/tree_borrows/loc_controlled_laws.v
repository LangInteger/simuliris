From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_inv.
From simuliris.tree_borrows Require Import tree_access_laws logical_state inv_accessors trees_equal.
From iris.prelude Require Import options.

Lemma loc_controlled_access_outside l tk sc cids σ σ' kind blk off1 sz acc_tg lu_tg b Mcall :
  apply_within_trees (memory_access_maybe_nonchildren_only b kind cids acc_tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ !! l = shp σ' !! l →
  scs σ = scs σ' →
  state_wf σ →
  ¬ (l.1 = blk ∧ off1 ≤ l.2 < off1 + sz) →
  loc_controlled Mcall l lu_tg tk sc σ →
  loc_controlled Mcall l lu_tg tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hnin Hlc.
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. by rewrite Heq3.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold).
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      split; first by rewrite -Heq3.
      split; first by rewrite -Heq3.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_outside_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew lu_tg t' = rel_dec trold lu_tg t') as Hreldec.
      { destruct (decide (l.1 = blk)) as [<- | Hne].
        - rewrite /apply_within_trees Hx /= in Happly.
          apply bind_Some in Happly as (newtr & H1 & [= H2]).
          rewrite -H2 lookup_insert in Htrnew.
          erewrite (access_same_rel_dec H1). congruence.
        - apply bind_Some in Happly as (itwrong & Hwrong & (y & Hy & [= Hacc])%bind_Some).
          rewrite -Hacc lookup_insert_ne // Hx in Htrnew. congruence. }
      rewrite rel_dec_flip2 in Hothers. rewrite rel_dec_flip2.
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. by rewrite Heq3 Heq2 Heq_scs.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold). rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hstuff).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      destruct Hstuff as (Hsame & Hothers).
      split_and!; first by rewrite -Heq3.
      split_and!; first by rewrite -Heq3 -Heq2 -Heq_scs.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_outside_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew lu_tg t' = rel_dec trold lu_tg t') as Hreldec.
      { destruct (decide (l.1 = blk)) as [<- | Hne].
        - rewrite /apply_within_trees Hx /= in Happly.
          apply bind_Some in Happly as (newtr & H1 & [= H2]).
          rewrite -H2 lookup_insert in Htrnew.
          erewrite (access_same_rel_dec H1). congruence.
        - apply bind_Some in Happly as (itwrong & Hwrong & (y & Hy & [= Hacc])%bind_Some).
          rewrite -Hacc lookup_insert_ne // Hx in Htrnew. congruence. }
      rewrite rel_dec_flip2 in Hothers. rewrite rel_dec_flip2.
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold & Hluold & Htrold & Hisinit & Hsame & Hothers).
    assert (trees_lookup σ.(strs) l.1 lu_tg itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_outside in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew & Htrnew & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    exists itnew, trnew. do 2 (split; first done).
    split; first by rewrite -Hpermold.
    split; first by rewrite -Hpermold.
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { destruct (decide (l.1 = blk)) as [<-|Hne].
      - rewrite /apply_within_trees Htrold /= in Happly.
        eapply bind_Some in Happly as (? & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        injection Htrnew as ->. eapply memory_access_wf; last done.
        destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
      - eapply bind_Some in Happly as (? & H1 & (? & H2 & [= H3])%bind_Some).
        rewrite -H3 lookup_insert_ne // in Htrnew.
        destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { destruct (decide (l.1 = blk)) as [<-|Hne].
      - rewrite /apply_within_trees Htrold /= in Happly.
        eapply bind_Some in Happly as (? & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        injection Htrnew as ->. rewrite /tree_unique.
        by erewrite tree_apply_access_same_count.
      - eapply bind_Some in Happly as (? & H1 & (? & H2 & [= H3])%bind_Some).
        rewrite -H3 lookup_insert_ne // Htrold in Htrnew. congruence.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

(* not generalized to maybe_nonchildren_only since this one is specific *)
Lemma loc_controlled_write_becomes_active l sc cids σ σ' blk off1 sz tg vls scold tkkold Mcall:
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  (write_mem (blk, off1) vls (shp σ)) = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  length vls = sz →
  trees_contain tg (strs σ) blk →
  list_to_heaplet vls off1 !! l.2 = Some sc →
  loc_controlled Mcall l tg (tk_unq tkkold) scold σ →
  (* we also prove that it's usable *)
  loc_controlled Mcall l tg (tk_unq tk_act) sc σ' ∧ bor_state_pre l tg (tk_unq tk_act) σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Hcontain Hsc Hold.
  assert (shp σ' !! l = Some sc) as Hheap.
  { rewrite -Heq_shp /=.
    destruct (write_mem_lookup_case (blk, off1) vls (shp σ) l) as [(i&Hil&->&HH)|(Hwrong&_)].
    2: { eapply list_to_heaplet_lookup_Some in Hsc. exfalso.
         eapply (Hwrong (Z.to_nat (l.2 - off1))); first lia.
         eapply injective_projections; first done.
         simpl. lia. }
    rewrite HH. rewrite list_to_heaplet_nth // in Hsc. }
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (trnew&Haccess&[= Hstrs])%bind_Some).
  rewrite /trees_contain /trees_at_block Htrold in Hcontain.
  eapply wf_tree_tree_unique in Hcontain as Hunique; last by eapply Hwf_pre.
  eapply unique_lookup in Hunique as (itold & Hdet).
  assert (tree_lookup trold tg itold) as Hitold by done.
  assert (off1 ≤ l.2 < off1 + sz) as Hinbound.
  { subst sz. by eapply list_to_heaplet_lookup_Some. }
  eapply apply_trees_access_lookup_general in Happlys as Happlyself.
  2: done. 3: by exists trold. 2: eassumption.
  destruct Happlyself as (itnew & Hlunew & _ & _ & Happlyself).
  assert (perm (item_lookup itnew l.2) = Active ∧ initialized (item_lookup itnew l.2) = PermInit ∧ bor_state_pre l tg (tk_unq tkkold) σ) as (Hactive&Hisinit&Hpre2).
  { eapply bind_Some in Happlyself as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
    simpl in Hperm1,Hperm2|-*. rewrite trees_rel_dec_refl /= in Hperm1|-*.
    rewrite most_init_comm.
    pose (ppo := item_lookup itold l.2). fold ppo.
    enough (pv = Active ∧ (initialized ppo = PermInit → perm (ppo) ≠ Disabled) ∧ (initialized ppo = PermInit → perm ppo = Frozen → protector_is_active (iprot itold) (scs σ))) as (H1&H2).
    { split; first done. simpl. rewrite /bor_state_pre_unq. split; first done.
      eexists. split; last apply H2.
      eexists; by subst blk. } subst ppo.
    repeat case_match; simplify_eq; done. }
  split; last first.
  { exists itnew. split; first by rewrite Hblk. by rewrite Hactive. }
  intros _. split; last done.
  rewrite -Hstrs /trees_lookup lookup_insert in Hlunew.
  destruct Hlunew as (?&[= <-]&Hlunew).
  exists itnew, trnew.
  split; first done.
  split; first rewrite -Hstrs Hblk lookup_insert //.
  split; first done.
  split; first by rewrite Hactive.
  destruct (Hold Hpre2) as ((it'&tr'&Htr'&Hlu'&_&_&Holdothers)&_).
  assert (tr' = trold) as ->.
  { rewrite Hblk Htrold in Hlu'. congruence. }
  intros itmod tmod Hlumod.
  eapply apply_trees_access_lookup_general_rev in Happlys.
  2: done. 2: eassumption. 2: { exists trnew; split; last done. rewrite -Hstrs lookup_insert //. }
  destruct Happlys as (itold' & (tr'&Htr''&Hluold) & _ & _ & Hperm).
  assert (tr' = trold) as ->.
  { rewrite Htrold in Htr''. congruence. }
  specialize (Holdothers _ _ Hluold).
  rewrite /trees_rel_dec Htrold /= /apply_access_perm /= /apply_access_perm_inner in Hperm.
  erewrite <-access_same_rel_dec; last done. clear Happlyself.
  rewrite rel_dec_flip2 in Holdothers|-*.
  eapply bind_Some in Hperm as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
  rewrite /= in Hperm1,Hperm2|-*.
  destruct rel_dec as [[[]|]|[|]], (perm (item_lookup itold' l.2)) as [[] []| | |], (initialized (item_lookup itold' l.2)) as [];
    repeat (simpl; try simpl in Hperm1; try simpl in Holdothers; simplify_eq; try done; try simpl in Hperm2; destruct bool_decide).
Qed.

Lemma loc_controlled_write_invalidates_others l sc σ σ' blk off1 sz tg_acc tg_lu tk Mcall A:
  apply_within_trees (memory_access AccessWrite σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  tg_acc ≠ tg_lu →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  bor_state_pre l tg_lu tk σ' →
  A. (* false *)
Proof.
  intros Happly Heq_scs Hwf Hblk Hsz Htgne Htgin Hcontrol Hpre.
  subst blk. exfalso.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert. }
  destruct tk as [|tkk|].
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis).
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      intros Hdis. eapply Hnondis.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite -Hx3. rewrite !Hdis in Hx1. simpl.
      assert (x1 = x2) as ->. 1: destruct (initialized _), bool_decide; simplify_eq; try done; destruct x1; by simplify_eq.
      clear Hx2.
      rewrite /apply_access_perm_inner in Hx1. destruct trees_rel_dec; by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hfrozen & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    (* old perm is frozen, it can not have survived the write *)
    pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
    rewrite Hfrozen /= in Hx1. destruct (trees_rel_dec (strs σ) l.1 tg_acc tg_lu); try done.
    pose proof Hx1 as [= <-].
    assert (x2 = Disabled) as -> by (destruct (initialized _), bool_decide; simplify_eq; done).
    rewrite -Hx3 in Hnondis. done.
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis & Hfreezeprot). 
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite /apply_access_perm_inner in Hx1.
      rewrite -Hx3 /most_init /= in Hnondis Hfreezeprot.
      rewrite bool_decide_decide in Hx1,Hx2.
      destruct trees_rel_dec as [[]|[]], (perm (item_lookup itold l.2)), (initialized (item_lookup itold l.2)) as []; simplify_eq; try done.
      all: try specialize (Hnondis eq_refl).
      all: (try destruct decide); try by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hsame & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    rewrite /trees_contain /trees_at_block Htrold in Htgin.
    pose proof Htgin as Hunq%wf_tree_tree_unique.
    2: by eapply (state_wf_tree_unq _ Hwf).
    pose proof Hunq as (itaccold&Hdet)%unique_lookup.
    assert (tree_lookup trold tg_acc itaccold) as Hitaccold by done.
    destruct (rel_dec trold tg_acc tg_lu) as [foreignpos|[isimm|]] eqn:Hreldec.
    + eapply apply_trees_access_lookup_general in Happly as Hitrev.
      2: apply Hwf. 2: eassumption. 2: exists trold; split; first done; last exact Hitaccold.
      destruct Hitrev as (itaccnew & (trnew' & Htrnew' & Hitaccnew) & Hinititacc & Hprotitacc & Hpermitacc).
      assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
      rewrite trees_rel_dec_refl in Hpermitacc.
      specialize (Hothers _ _ Hitaccold).
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some. clear Hpermit.
      pose proof Hpermitacc as (y1&Hy1&(y2&Hy2&[=Hy3])%bind_Some)%bind_Some. clear Hpermitacc.
      rewrite /apply_access_perm_inner in Hx1,Hy1.
      rewrite -!Hx3 -!Hprotit -?Heq_scs /= in Hnondis Hfreezeprot Hx1 Hx2.
      rewrite /trees_rel_dec Htrold in Hx1.
      rewrite !bool_decide_decide in Hx1,Hx2,Hy1,Hy2.
      rewrite Hreldec in Hx1,Hothers.
      destruct foreignpos as [pp|].
      all: destruct (perm (item_lookup itold l.2)) as [[][]| | |], 
                    (initialized (item_lookup itold l.2)) as []; 
             simpl in *; simplify_eq; try done.
      all: repeat (destruct decide; simplify_eq; try done).
      all: destruct (perm (item_lookup itaccold l.2)) as [[][]| | |], 
                    (initialized (item_lookup itaccold l.2)) as []; 
             simpl in *; simplify_eq; try specialize (Hnondis eq_refl); try destruct Hsame as (?&?&?); try done.
    + pose proof Hreldec as HH.
      rewrite /rel_dec in HH.
      edestruct (decide (ParentChildIn _ _ _)) as [HPC|]; last done.
      edestruct (decide (ParentChildIn _ _ _)) as [|HNPC]; first done.
      injection HH as Hisimm.
      eapply lookup_implies_contains in Hitold as Hluin.
      assert (StrictParentChildIn tg_lu tg_acc trold) as HSPC.
      { destruct HPC; last done. subst tg_lu. rewrite rel_dec_refl in Hreldec; done. }
      eapply immediate_sandwich in HSPC as (tsw&H1&H2).
      2-3: by eapply Hwf.
      eapply contains_child in Hluin as Htwin.
      2: right; by eapply Immediate_is_StrictParentChild.
      destruct (@unique_implies_lookup tsw trold) as (itsw&Hitswold).
      1: by eapply Hwf.
      eapply apply_trees_access_lookup_general in Happly as Hitrev.
      2: apply Hwf. 2: eassumption. 2: exists trold; split; first done; last exact Hitswold.
      destruct Hitrev as (itswnew & (trnew' & Htrnew' & Hitswnew) & Hinititsw & Hprotitsw & Hpermitsw).
      assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
      specialize (Hothers _ _ Hitswold).
      rewrite /trees_rel_dec Htrold in Hpermitsw.
      rewrite /rel_dec decide_True // /maybe_non_children_only /= in Hpermitsw.
      rewrite /rel_dec decide_True // /= in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite /rel_dec decide_False // /= in Hothers.
      2: { intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
           all: eapply Hwf; first done. all: done. }
      rewrite decide_True // /= in Hothers.
      pose proof Hpermitsw as (y1&Hy1&(y2&Hy2&[=Hy3])%bind_Some)%bind_Some. clear Hpermitsw.
      rewrite /apply_access_perm Hothers /= in Hy1. done.
    + eapply Htgne, rel_this_antisym. 3: done. 2: apply Hitold. done.
  - destruct Hcontrol as ((itold&trold'&Hitold&Htrold'&Hactive&Hunq)&_); first done.
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    rewrite /trees_contain /trees_at_block Htrold in Htgin.
    pose proof Htgin as Htgunq%wf_tree_tree_unique.
    2: by eapply (state_wf_tree_unq _ Hwf).
    pose proof Htgunq as (itaccold&Hdet)%unique_lookup.
    assert (tree_lookup trold tg_acc itaccold) as Hitaccold by done.
    eapply Htgne; symmetry. eapply Hunq; try done.
Qed.



Lemma loc_controlled_read_preserved l sc σ σ' blk off1 sz tg_acc tg_lu tk Mcall b:
  apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hlc.
  subst blk.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert. }
  rewrite /loc_controlled.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros Hdis. eapply apply_access_perm_read_not_disabled in Hdis; done.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_read_initialized.
      split; first by eapply apply_access_perm_read_frozen.
      intros itnew' t' Hit'.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      specialize (Hothers _ _ Hitoldlu').
      assert (rel_dec trnew t' tg_lu = rel_dec trold t' tg_lu) as Hreldec.
      { rewrite /apply_within_trees Hx /= in Happly.
        apply bind_Some in Happly as (newtr & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        erewrite (access_same_rel_dec H1). congruence. }
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
      rewrite /trees_rel_dec Htrold in Hperm2.
      edestruct maybe_non_children_only_effect_or_nop as [Heqc|Heqc]; erewrite Heqc in Hperm2.
      2: by injection Hperm2 as <-.
      assert (lazy_perm_wf (item_lookup itold' l.2)) as Hwitold'.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwitold'.
      clear Heqc. rewrite /apply_access_perm /apply_access_perm_inner /= in Hperm2.
      repeat (case_match; simpl in Hperm2; simplify_eq; try rewrite <- Hperm2; try (specialize (Hwitold' eq_refl)); try done).
  - intros (it & Htrlu & Hndis & Hfrzprot).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. split.
      1: intros HH Hdis; eapply apply_access_perm_read_not_disabled in Hdis; last done.
      1: eapply Hndis; try done; by eapply apply_access_perm_read_initialized.
      intros Hinit Hfrz. rewrite Heq2 Heq_scs. eapply Hfrzprot.
      1: erewrite apply_access_perm_read_initialized; done.
      1: erewrite apply_access_perm_read_frozen; done.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2. rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hstuff).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      destruct Hstuff as (Hisinit & Hsame & Hothers).
      assert (lazy_perm_wf (item_lookup itold l.2)) as Hwfitold.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold. rewrite /bor_state_post_unq.
      split; first by eapply apply_access_perm_read_initialized.
      match goal with |- (?A ∧ ?B) => assert (A ∧ match trees_rel_dec (strs σ) l.1 tg_acc tg_lu with 
          Foreign (Parent _) => act = tk_res ∨ (b = true) | Foreign _ => act = tk_res | _ => True end) as (Hfp&Hactres) end.
      { clear Hothers. rewrite -Heq2 -Heq_scs. edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Heq3.
        2: { injection Heq3 as <-. rewrite He2. split; first done. by right. }
        pose proof Heq3 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
        rewrite -HH -?Heq_scs /= in Hfrzprot|-*.
        rewrite /apply_access_perm_inner in Hx1.
        repeat (case_match; simplify_eq; (try specialize (Hwfitold eq_refl)); (try (destruct Hsame; [ idtac ])); try done; try (split; [done | (try by left); by right ])).
        all: exfalso.
        all: eapply bool_decide_eq_false_1; last apply (Hfrzprot eq_refl eq_refl). all: done. }
      split; first done.
      intros itnew' t' Hit'.
      rewrite /lazy_perm_wf in Hwfitold.
      assert (trees_lookup (strs σ') l.1 t' itnew') as Hit'' by by exists trnew.
      eapply apply_trees_access_lookup_general_rev in Hit''; [|eapply Happly|eapply Hwf|done].
      destruct Hit'' as (itold' & (x & Hx & Hitoldlu') & HHHH).
      assert (x = trold) as -> by congruence.
      assert (lazy_perm_wf (item_lookup itold' l.2)) as Hwfitold'.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold'.
      specialize (Hothers _ _ Hitoldlu').
      assert (∀ tg1 tg2, rel_dec trnew tg1 tg2 = rel_dec trold tg1 tg2) as Hreldec_strong.
      { intros tg1 tg2. rewrite /apply_within_trees Hx /= in Happly.
        apply bind_Some in Happly as (newtr & H1 & [= H2]).
        rewrite -H2 lookup_insert in Htrnew.
        erewrite (access_same_rel_dec H1). congruence. }
      assert (rel_dec trnew t' tg_lu = rel_dec trold t' tg_lu) as Hreldec.
      { eapply Hreldec_strong. }
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2).
      edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Hperm2.
      2: injection Hperm2 as <-; apply Hothers.
      pose proof Hperm2 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
      rewrite -HH -?Heq_scs /= in |-*.
      rewrite /apply_access_perm_inner in Hx1. clear Heqcc. clear Hfp.
      rewrite /trees_rel_dec Htrold in Hactres HH Hx1 Hne.
      rewrite /trees_contain /trees_at_block Htrold in Htgin.
      assert (wf_tree trold) as Hwfold by by eapply Hwf.
      opose proof (rel_dec_concat_foreign _ tg_acc t' tg_lu _ _ _ _) as HtransiF.
      1-4: try done; eapply wf_tree_tree_unique; try done; by eapply lookup_implies_contains.
      repeat (case_match; simplify_eq; (try specialize (Hwfitold' eq_refl)); 
          (try edestruct (HtransiF _ _ eq_refl eq_refl) as (?&?)); simplify_eq; try done).
      all: destruct Hactres as [?|Hactres]; first done.
      all: subst b; destruct Hne as [?|Hne]; first done.
      all: erewrite Hreldec_strong in Hreldec;
           edestruct rel_dec_parent_parent_is_parent as (p&Hp); [exact Hwfold| | | | |exact Hreldec|..]; [| | | |done|]; [done|eapply Hitoldlu'|eapply Hluold|..]; [done|]; subst; exfalso; by eapply Hne.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold' & Hluold & Htrold' & Hisinit & Hsame & Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (trees_lookup σ.(strs) l.1 tg_lu itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_general in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew' & Htrnew' & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    assert (trnew' = trnew) as -> by congruence.
    assert (tg_lu = tg_acc) as <-.
    { eapply trees_contain_trees_lookup_1 in Htgin as (it&tr&Htr&HH). 2: apply Hwf.
      assert (tr = trold) as -> by congruence. by eapply Hothers. }
    exists itnew, trnew. do 2 (split; first done). split.
    { by eapply apply_access_perm_read_initialized. }
    rewrite trees_rel_dec_refl in Hpermold.
    edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&acckind&He2)]; erewrite Heqcc in Hpermold.
    2: done.
    rewrite /apply_access_perm Hsame /= in Hpermold.
    split.
    { repeat (case_match; simpl in *; simplify_eq; try done). all: by rewrite -Hpermold. }
    intros it' t' Hluit'.
    assert (wf_tree trnew) as Hwfnew.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert in Htrnew.
      injection Htrnew as ->. eapply memory_access_wf; last done.
      destruct Hwf as [_ Hwf _ _]. by eapply Hwf.
    }
    assert (tree_unique t' trnew) as Hunq.
    { eapply wf_tree_tree_unique. 2: apply Hluit'. done. }
    assert (tree_unique t' trold) as Hunqold.
    { rewrite /apply_within_trees Htrold /= in Happly.
      eapply bind_Some in Happly as (? & H1 & [= H2]).
      rewrite -H2 lookup_insert in Htrnew.
      injection Htrnew as ->. rewrite /tree_unique.
      by erewrite tree_apply_access_same_count.
    }
    eapply unique_exists in Hunqold as Hextold.
    eapply unique_lookup in Hunqold as (it & Hitdet).
    eapply Hothers. done.
Qed.

Lemma loc_controlled_read_preserved_everywhere l sc σ σ' blk off1 sz tg_acc tg_lu tk Mcall b:
  apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  trees_contain tg_acc σ.(strs) blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Hhp Hcs Hwf Hcont.
  destruct (decide ((l.1 = blk ∧ off1 ≤ l.2 < off1 + sz))) as [(Hblk&Hoff)|Hne].
  - by eapply loc_controlled_read_preserved.
  - eapply loc_controlled_access_outside; try done. by rewrite Hhp.
Qed.

Lemma protected_priv_loc_does_not_survive_access σ σ' M_tag M_hl M_call off1 sz blk tg_acc tg_lu l acc Mcall :
  apply_within_trees (memory_access acc σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  call_set_interp M_call σ →
  M_tag !! tg_acc = Some (tk_pub, ()) →
  priv_loc M_tag M_hl M_call tg_lu l →
  (∀ tg tk sc, M_tag !! tg = Some (tk, ()) → heaplet_lookup M_hl (tg, l) = Some sc → loc_controlled Mcall l tg tk sc σ) →
  False.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hcs Hactually_public Hpl Hlc.
  destruct Hpl as (tk&Htk&(sc&Hsc)&Hpriv).
  eapply trees_contain_trees_lookup_1 in Htgin as (itacc&(tr&Htr&Hitacc)); last apply Hwf.
  specialize (Hlc tg_lu tk sc Htk Hsc).
  destruct Hpriv as [->|(cc&->&Hcc)].
  - destruct Hlc as ((it&tr'&Hit&Htr'&Hactive&Hunq)&_); first done.
    assert (tr' = tr) as -> by congruence.
    enough (tg_lu = tg_acc) as -> by congruence.
    eapply Hunq. done.
  - destruct Hcc as (Mcc&HMcc&Lcc&b&HLcc&Hlincc&->%prot_le_def). 2: done.
    specialize (Hcs _ _ HMcc) as (Hccact&Hcs).
    specialize (Hcs _ _ HLcc) as (Htgluvalid&Hcs). 
    specialize (Hcs l _ Hlincc) as (itlu&(tr'&Htr'&Hitlu)&Hprot1&Hprot2&Hcs).
    assert (tr' = tr) as -> by congruence.
    destruct Hlc as (Hlc&_).
    { eexists. split; first by eexists. split; first done.
      intros _ _. by eexists. }
    destruct Hlc as (itlu'&tr'&Hitlu'&Htr''&Hisinit&Hsame&Hothers).
    assert (tr' = tr) as -> by congruence.
    assert (itlu' = itlu) as -> by by eapply tree_lookup_unique.
    subst blk.
    assert (perm (item_lookup itlu l.2) = Active) as Hisactive.
    { destruct perm as [[][]| | |]; try done; by destruct Hsame. }
    destruct (rel_dec tr tg_acc tg_lu) as [fk|[ck|]] eqn:Hreldec.
    + assert (trees_lookup σ.(strs) l.1 tg_lu itlu) as Hitluold by by eexists.
      pose Hitluold as HH.
      eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
      destruct HH as (itlunew&(trnew&Htrnew&Hitlunew)&Hinitplu&Hiprotlu&Hpermlu).
      rewrite /trees_rel_dec Htr in Hpermlu.
      assert (protector_is_active (iprot itlunew) (scs σ)) as Hisprot.
      { exists cc. rewrite -Hiprotlu //. }
      rewrite Hreldec /= /apply_access_perm /apply_access_perm_inner Hisactive /= in Hpermlu.
      rewrite bool_decide_eq_true_2 // Hisinit /= in Hpermlu.
      by destruct acc.
    + assert (StrictParentChildIn tg_lu tg_acc tr) as HSPC.
      { rewrite /rel_dec in Hreldec. destruct decide as [[->|HSPC]|?]; try done.
        rewrite decide_True in Hreldec; last by left. done. }
      assert (tree_contains tg_lu tr) as Hluin.
      1: by eapply lookup_implies_contains.
      eapply immediate_sandwich in HSPC as (tsw&Hs1&Hs2).
      2-3: by eapply Hwf.
      eapply contains_child in Hluin as Hswin.
      2: right; by eapply Immediate_is_StrictParentChild.
      assert (tree_unique tsw tr) as Hswinunq by by eapply Hwf.
      eapply unique_implies_lookup in Hswinunq as (itsw&Hitsw).
      assert (trees_lookup σ.(strs) l.1 tsw itsw) as Hitswold by by eexists.
      pose Hitswold as HH.
      eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
      destruct HH as (itswnew&(trnew&Htrnew&Hitswnew)&Hinitpsw&Hiprotsw&Hpermsw).
      specialize (Hothers _ _ Hitsw).
      rewrite /trees_rel_dec Htr // in Hpermsw.
      rewrite /= /rel_dec decide_True // in Hpermsw.
      rewrite /= /rel_dec decide_True in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite decide_False in Hothers.
      2: { intros HPC2. eapply immediate_parent_not_child; try done. all: by eapply Hwf. }
      rewrite decide_True // in Hothers.
      rewrite /= /apply_access_perm /apply_access_perm_inner /= !Hothers /= in Hpermsw.
      by destruct acc.
    + enough (tg_lu = tg_acc) as -> by congruence.
      symmetry.
      eapply rel_this_antisym; last done.
      all: by eapply lookup_implies_contains.
Qed.


(* not generalized to maybe_nonchildren_only since this one is specific *)
Lemma loc_controlled_write_invalidates_pub l cids σ σ' blk off1 sz tg scold Mcall (A:Prop):
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  state_wf σ →
  l.1 = blk →
  trees_contain tg (strs σ) blk →
  (off1 ≤ l.2 < off1 + sz) →
  loc_controlled Mcall l tg tk_pub scold σ →
  A.
Proof.
  intros Happly Hwf Hblk Hcontain Hinbound Hold.
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (trnew&Haccess&[= Hstrs])%bind_Some).
  rewrite /trees_contain /trees_at_block Htrold in Hcontain.
  assert (strs σ' !! blk = Some trnew) as Htrnew.
  1: rewrite -Hstrs lookup_insert //.
  eapply wf_tree_tree_unique in Hcontain as Hunique; last by eapply Hwf_pre.
  eapply unique_lookup in Hunique as (itold & Hdet).
  assert (tree_lookup trold tg itold) as Hitold by done.
  eapply apply_trees_access_lookup_general in Happlys as Happlyself.
  2: done. 3: by exists trold. 2: eassumption.
  destruct Happlyself as (itnew & Hlunew & _ & _ & Happlyself).
  rewrite trees_rel_dec_refl /= /apply_access_perm /apply_access_perm_inner /= in Happlyself.
  destruct Hold as ((itold'&trold'&Htrold'&Hitold'&Hisinit&Hfrozen&Hothers)&_).
  { exists itold. subst blk. split; first by eexists.
    intros Hdis. rewrite Hdis in Happlyself. done. } 
  assert (trold' = trold) as -> by congruence.
  assert (itold' = itold) as -> by by eapply tree_lookup_unique.
  rewrite Hfrozen in Happlyself. done.
Qed.

Lemma loc_controlled_write_invalidates_pub' l cids σ σ' blk off1 sz tg scold Mcall :
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  state_wf σ →
  l.1 = blk →
  trees_contain tg (strs σ) blk →
  (off1 ≤ l.2 < off1 + sz) →
  loc_controlled Mcall l tg tk_pub scold σ →
  loc_controlled Mcall l tg tk_pub scold σ'.
Proof.
  eapply loc_controlled_write_invalidates_pub.
Qed.

Lemma loc_controlled_add_protected l tg tk sc σ σ' Mcall :
  shp σ = shp σ' →
  strs σ = strs σ' →
  state_wf σ →
  (∀ blk tg it c, trees_lookup σ.(strs) blk tg it → protector_is_for_call c it.(iprot) → call_is_active c σ.(scs) ↔ call_is_active c σ'.(scs)) →
  loc_controlled Mcall l tg tk sc σ →
  loc_controlled (<[snc σ := ∅]> Mcall) l tg tk sc σ'.
Proof.
  intros Hhp Htrs Hwf Hscs Hlc Hpre.
  assert (∀ blk tg it, trees_lookup σ.(strs) blk tg it → protector_is_active it.(iprot) σ.(scs) ↔ protector_is_active it.(iprot) σ'.(scs)) as HHscs.
  { intros blk tg' it H1; split; intros (c&H2&H3); exists c. all: split; first done. all: by eapply Hscs. }
  rewrite -Hhp.
  destruct tk as [|acc|].
  all: rewrite /loc_controlled /bor_state_pre /bor_state_own in Hlc,Hpre|-*.
  1,3: rewrite Htrs in Hlc; apply Hlc, Hpre.
  destruct Hlc as ((it&tr&Htr&Hit&Hinit&Hsame&Hothers)&Hhpc).
  - destruct Hpre as (itp&Hitp&HH).
    setoid_rewrite <- HHscs in HH. 2: by rewrite Htrs.
    exists itp. by rewrite Htrs.
  - split; last done.
    exists it, tr. rewrite -Htrs. split_and!; try done.
    split. 2: done.
    clear Hothers.
    case_match; try done.
    case_match; try done. destruct Hsame as (->&Hprot&Hcs).
    split_and!; first done.
    + setoid_rewrite <- HHscs; first done.
      by eexists.
    + destruct (iprot it) as [itprot|] eqn:Hitprot; last done.
      rewrite /prot_in_call_set /= /call_set_in' lookup_insert_ne //.
      specialize (state_wf_tree_compat _ Hwf _ _ Hit) as Hwfcompat.
      setoid_rewrite every_node_iff_every_lookup in Hwfcompat.
      2: by eapply wf_tree_tree_item_determined, Hwf.
      specialize (Hwfcompat _ _ Htr).
      opose proof (item_cid_valid _ _ _ Hwfcompat (itprot.(call)) _) as ?. 2: lia.
      rewrite Hitprot. by destruct itprot.
Qed.






Lemma apply_within_trees_set_fold {X} `{Countable X} (fn : X → option (tree item) → option (tree item)) (S : tree item → gset X) (blk : block) (trs trs' : trees) :
  apply_within_trees (λ tr, set_fold fn (Some tr) (S tr)) blk trs = Some trs' →
  (∀ x y z, fn x y = Some z → is_Some y) →
  ∃ tr0, trs !! blk = Some tr0 ∧
         set_fold (λ el trso, trs ← trso; apply_within_trees (λ tr, fn el (Some tr)) blk trs) (Some trs) (S tr0) = Some trs'.
Proof.
  intros (tr0&Htr0&(trr&Htrr&[= <-])%bind_Some)%bind_Some Hf.
  exists tr0. split; first done.
  rewrite /set_fold /= in Htrr|-*.
  induction (elements (S tr0)) as [|el1 E IH] in trr,Htrr|-*.
  - simpl in *. injection Htrr as ->. by rewrite insert_id.
  - simpl in *. pose proof Htrr as Htrr'. eapply Hf in Htrr as (sy&Htrr).
    specialize (IH _ Htrr). rewrite IH. simpl. rewrite Htrr in Htrr'.
    rewrite /apply_within_trees /= lookup_insert /= Htrr' /= insert_insert //.
Qed.

Lemma apply_within_trees_tag_count_preserves_exists tg blk1 blk2 trs trs' fn :
  apply_within_trees fn blk1 trs = Some trs' →
  preserve_tree_tag_count fn →
  trees_contain tg trs blk2 →
  trees_contain tg trs' blk2.
Proof.
  intros (tr1&Htr1&(tr2&Htr2&[= <-])%bind_Some)%bind_Some H2.
  rewrite /trees_contain /trees_at_block.
  destruct (trs !! blk2) as [tr|] eqn:Htr; last done.
  intros Hcontains.
  destruct (decide (blk2 = blk1)) as [Heq|Hne].
  - subst blk2. assert (tr = tr1) as -> by congruence.
    rewrite lookup_insert. eapply count_gt0_exists.
     erewrite <- H2; last done. eapply count_gt0_exists. done.
  - rewrite lookup_insert_ne; last done. by rewrite Htr.
Qed.

Lemma loc_controlled_tree_read_all_protected_initialized_1 l blk sc σ σ' tg_lu tk Mcall tg_acc (L : gset _) SS:
  let fn := (λ tr, set_fold (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead (scs σ) tg_acc (l, 1%nat)) (Some tr) L) in
  let PS := (λ σ (S : gset (nat * gset Z)), (∀ tg x, (tg, x) ∈ S → trees_contain tg (strs σ) blk)) in
  apply_within_trees fn blk (strs σ) = Some (strs σ') →
  state_wf σ →
  PS σ SS →
  shp σ = shp σ' →
  scs σ = scs σ' →
  snc σ = snc σ' →
  snp σ = snp σ' →
  (∃ L, (tg_acc, L) ∈ SS) →
  loc_controlled Mcall l tg_lu tk sc σ →
  (loc_controlled Mcall l tg_lu tk sc σ' ∧ state_wf σ') ∧ PS σ' SS.
Proof.
  intros fn PS.
  intros (tr0&Htr0&Hrefold)%apply_within_trees_set_fold; last first.
  1: intros ? [?|]?; simpl; done.
  clear tr0 Htr0. subst fn. revert L σ' Hrefold.
  eapply (set_fold_ind_L (λ r (M : gset _), ∀ σ', r = Some (strs σ') → _ → _ → _ → _ → _ → _ → _ → _ → (loc_controlled Mcall l tg_lu tk sc σ' ∧ _) ∧ PS σ' SS)).
  { intros σ' [= H1] ?? H2 H3 H4 H5 _ ?. destruct σ, σ'; simpl in *; simplify_eq; done. }
  intros off L [trs2|] Hnin IH σ' H1 Hwf HPS H2 H3 H4 H5 Hcont Hlc; last done.
  simpl in H1.
  pose (σ2 := mkState σ.(shp) trs2 σ.(scs) σ.(snp) σ.(snc)).
  destruct (IH σ2) as ((IH2 & Hwf2) & HPS2).
  1-9: simpl; done.
  destruct Hcont as (L'&Hcont).
  split_and!.
  - eapply loc_controlled_read_preserved_everywhere; last exact IH2.
    1: exact H1. 1-3: simpl; done.
    eapply HPS2, Hcont.
  - destruct σ'. simpl in *; simplify_eq. eapply (read_step_wf_inner σ2). 2: exact H1.
    2: done. eapply HPS2, Hcont.
  - subst PS. simpl. intros tg X HX.
    specialize (HPS2 tg X HX). eapply apply_within_trees_tag_count_preserves_exists.
    1: exact H1. 2: exact HPS2. eapply memory_access_tag_count.
Qed.

Lemma loc_controlled_tree_read_all_protected_initialized l blk c sc σ σ' tg_lu tk Mcall:
  apply_within_trees (tree_read_all_protected_initialized (scs σ) c) blk (strs σ) = Some (strs σ') →
  state_wf σ →
  shp σ = shp σ' →
  scs σ = scs σ' →
  snc σ = snc σ' →
  snp σ = snp σ' →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ' ∧ state_wf σ'.
Proof.
  rewrite /tree_read_all_protected_initialized.
  intros (tr0&Htr0&Hrefold)%apply_within_trees_set_fold; last first.
  1: intros [??] [?|]?; simpl; done.
  intros Hwf.
  remember (tree_get_all_protected_tags_initialized_locs c tr0) as S eqn:HeqS.
  remember S as S2 eqn:HeqS2 in HeqS.
  pose (PS := λ σ (S : gset (nat * gset Z)), (∀ tg x, (tg, x) ∈ S → trees_contain tg (strs σ) blk)).
  assert (PS σ S2) as HH.
  { subst S S2. intros tg ? (it&Hit&_)%tree_all_protected_initialized_elem_of. 2: by eapply Hwf.
    rewrite /trees_contain /trees_at_block Htr0. by eapply lookup_implies_contains. }
  assert (S ⊆ S2) as HSS by by subst.
  intros H1 H2 H3 H4 H5. match goal with |- ?g => eenough (g ∧ PS σ' S2) as (HH1&?) end; first exact HH1. revert H1 H2 H3 H4 H5. clear HeqS HeqS2.
  revert S S2 σ' HH HSS Hrefold Hwf.
  eapply (set_fold_ind_L (λ r (M : gset _), ∀ S' σ', PS σ S' → M ⊆ S' → r = Some (strs σ') → _ → _ → _ → _ → _ → _ → (loc_controlled Mcall l tg_lu tk sc σ' ∧ _) ∧ PS σ' S')).
  { intros S2 σ' HPS HSS [= H1] Hwf H2 H3 H4 H5 Hlc.
    destruct σ, σ'; simpl in *; simplify_eq; done. }
  intros [tg_acc L] S [trs2|] Hnin IH SS σ' Hcont HSS H1 Hwf H2 H3 H4 H5 Hlc; last done.
  simpl in H1.
  pose (σ2 := mkState σ.(shp) trs2 σ.(scs) σ.(snp) σ.(snc)).
  destruct (IH SS σ2) as ((IH2 & Hwf2) & HPS2).
  { intros ?? H; by eapply Hcont. }
  { etransitivity; last eapply HSS. eapply union_subseteq_r. }
  1-6: simpl; done. 1: done.
  rewrite /set_fold in H1.
  eapply (loc_controlled_tree_read_all_protected_initialized_1 _ _ _ σ2).
  1: exact H1. 1: done. 2-5: simpl; done. 3: done.
  1: exact HPS2. eexists.
  eapply HSS, elem_of_union. left. by eapply elem_of_singleton.
Qed.

Lemma loc_controlled_trees_read_all_protected_initialized_1 l c sc σ σ' tg_lu tk Mcall:
  trees_read_all_protected_initialized (scs σ) c (strs σ) = Some (strs σ') →
  shp σ = shp σ' →
  scs σ = scs σ' →
  snc σ = snc σ' →
  snp σ = snp σ' →
  state_wf σ →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ' ∧ state_wf σ'.
Proof.
  revert σ'.
  eapply (set_fold_ind_L (λ r M, ∀ σ', r = Some (strs σ') → _ → _ → _ → _ → _ → _ → loc_controlled Mcall l tg_lu tk sc σ' ∧ _)).
  { intros σ' [= H1] H2 H3 H4 H5 Hwf.
    rewrite /loc_controlled /bor_state_pre /bor_state_own /bor_state_pre_unq /bor_state_post_unq.
    rewrite !H1 !H2 !H3. intros H. split; first exact H.
    clear H. destruct σ, σ'; simpl in *; subst; done. }
  intros blk S [trs2|] Hblk IH σ'; last done. simpl.
  intros Happly Hhp Hcs Hnc Hnp Hwf H1.
  pose (σ2 := mkState σ.(shp) trs2 σ.(scs) σ.(snp) σ.(snc)).
  destruct (IH σ2) as (IH2 & Hwf2).
  1: done. 1-4: simpl; done. 1-2: done.
  eapply loc_controlled_tree_read_all_protected_initialized with (σ := σ2). 1: exact Happly.
  2-5: simpl; done. 2: eapply IH; simpl; done. done.
Qed.

Lemma loc_controlled_trees_read_all_protected_initialized l c sc σ σ' tg_lu tk Mcall:
  trees_read_all_protected_initialized (scs σ) c (strs σ) = Some (strs σ') →
  shp σ = shp σ' →
  scs σ ∖ {[ c ]} = scs σ' →
  snc σ = snc σ' →
  snp σ = snp σ' →
  state_wf σ →
  Mcall !! c = Some ∅ →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled (delete c Mcall) l tg_lu tk sc σ'.
Proof.
  intros H1 H2 H3 H4 H5 HWF Hcalls Hlc1.
  pose (σ2 := mkState σ.(shp) σ'.(strs) σ.(scs) σ.(snp) σ.(snc)).
  odestruct (loc_controlled_trees_read_all_protected_initialized_1 _ _ _ σ σ2) as (Hlc2&HWF2).
  1: done. 1-5: done. 1: exact Hlc1.
  destruct σ' as [x1 x2 x3 x4 x5]. simpl in *. subst x1 x3 x4 x5.
  intros Hpre'. simpl.
  edestruct Hlc2 as (Hpost&HHL).
  { destruct tk; [done| |done].
    destruct Hpre' as (it&Hit1&Hit2&Hit3). exists it.
    split_and!; try done.
    intros Hini Hperm. destruct (Hit3 Hini Hperm) as (cc&Hcc1&Hcc2).
    exists cc. split; try done. eapply elem_of_difference, Hcc2. }
  split; last done.
  destruct tk; [done| |done].
  destruct Hpost as (it&tr&Hit&Htr&Hinit&Hown&Hothers).
  exists it, tr. do 3 (split; first done). split; last done.
  clear Hothers. repeat (case_match; try done; []).
  destruct Hown as (Ho1&(cc&Hcc1&Hcc2)&Ho3). split; first done.
  destruct (iprot it) as [[p cc2]|]; last done. injection Hcc1 as ->.
  assert (c ≠ cc) as Hne.
  { intros ->. simpl in Ho3. destruct Ho3 as (M&HM&b&X&HX&_). rewrite Hcalls in HM. injection HM as <-.
    rewrite lookup_empty in HX. done. }
  split.
  - exists cc. split; first done. simpl. rewrite /call_is_active. eapply elem_of_difference; split; first done. set_solver.
  - destruct Ho3 as (M&HM&HHM). exists M; split; last done.
    rewrite /= lookup_delete_ne; done.
Qed.








