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
    + exists itold. split; first done. by rewrite Heq3.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold). rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      split_and!; first by rewrite -Heq3.
      split.
      { intros Hfrz. ospecialize (Hsame _). 1: by rewrite Heq3 Heq_scs Heq2. by rewrite -Heq3 -Heq2 -Heq_scs. }
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
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2 -Hprot2 -Heq_scs.
      destruct (rel_dec trold lu_tg t') as [[]|[]]; simpl in *. 1,3,4: eapply Hothers.
      destruct Hothers as [Heff|Hothers]; first by left. right.
      destruct (perm (item_lookup itold' l.2)) as [[]?| | |]; try done.
      * destruct Hothers as [H|[H|H]]; try eauto.
        right. right. by rewrite -Heq2 -Heq3.
      * destruct Hothers as [H|H]; try eauto.
        right. by rewrite -Heq2 -Heq3.
      * destruct Hothers as [H|H]; try eauto.
        right. by rewrite -Heq2 -Heq3.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold & Hluold & Htrold & Hisinit & Hsame & Hnoprot & Hothers).
    assert (trees_lookup σ.(strs) l.1 lu_tg itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_outside in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew & Htrnew & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    exists itnew, trnew. do 2 (split; first done).
    split; first by rewrite -Hpermold.
    split; first by rewrite -Hpermold.
    split; first by rewrite -Hprotold.
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
Lemma loc_controlled_write_becomes_active l sc σ σ' blk off1 sz tg vls scold tkkold Mcall:
  apply_within_trees (memory_access AccessWrite σ.(scs) tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  (write_mem (blk, off1) vls (shp σ)) = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  length vls = sz →
  trees_contain tg (strs σ) blk →
  list_to_heaplet vls off1 !! l.2 = Some sc →
  loc_controlled Mcall l tg (tk_unq tkkold) scold σ →
  (* we also prove that it's usable *)
  loc_controlled Mcall l tg (tk_unq tk_act) sc σ'.
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
  assert (perm (item_lookup itnew l.2) = Active ∧ initialized (item_lookup itnew l.2) = PermInit ∧ bor_state_pre l tg (tk_unq tkkold) σ ∧ ((initialized (item_lookup itold l.2) = PermInit → perm (item_lookup itold l.2) = Frozen → protector_is_active (iprot itold) (scs σ)))) as (Hactive&Hisinit&Hpre2&Hpre3).
  { eapply bind_Some in Happlyself as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
    simpl in Hperm1,Hperm2|-*. rewrite trees_rel_dec_refl /= in Hperm1|-*.
    rewrite most_init_comm.
    pose (ppo := item_lookup itold l.2). fold ppo.
    enough (pv = Active ∧ (initialized ppo = PermInit → perm (ppo) ≠ Disabled) ∧ (initialized ppo = PermInit → perm ppo = Frozen → protector_is_active (iprot itold) (scs σ))) as (H1&H2&H3).
    { split; first done. simpl. rewrite /bor_state_pre_unq. split; first done.
      eexists. 2: done. eexists. split; last apply H2.
      eexists; by subst blk. } subst ppo. 
    repeat case_match; simplify_eq; done. }
  intros _. split; last done.
  rewrite -Hstrs /trees_lookup lookup_insert in Hlunew.
  destruct Hlunew as (?&[= <-]&Hlunew).
  exists itnew, trnew.
  split; first done.
  split; first rewrite -Hstrs Hblk lookup_insert //.
  split; first done.
  split.
  { intros _. by rewrite Hactive. } 
  destruct (Hold Hpre2) as ((it'&tr'&Htr'&Hlu'&_&Hrst)&_).
  assert (tr' = trold) as ->.
  { rewrite Hblk Htrold in Hlu'. congruence. }
  destruct Hrst as (_&Holdothers).
  intros itmod tmod Hlumod.
  eapply apply_trees_access_lookup_general_rev in Happlys as Happlys'.
  2: done. 2: eassumption. 2: { exists trnew; split; last exact Hlumod. rewrite -Hstrs lookup_insert //. }
  destruct Happlys' as (itold' & (tr'&Htr''&Hluold) & HX1 & HX2 & Hperm).
  assert (tr' = trold) as ->.
  { rewrite Htrold in Htr''. congruence. }
  specialize (Holdothers _ _ Hluold).
  rewrite /trees_rel_dec Htrold /= /apply_access_perm /= /apply_access_perm_inner in Hperm.
  erewrite <-access_same_rel_dec; last done. clear Happlyself.
  rewrite rel_dec_flip2 in Holdothers|-*.
  eapply bind_Some in Hperm as (prm&Hperm1&(pv&Hperm2&[= Hrev])%bind_Some).
  rewrite /= in Hperm1,Hperm2|-*.
  destruct (rel_dec trold tg tmod) as [[[]|]|[|]] eqn:Hreldec; simpl in *.
  3: { destruct Holdothers as [Heff|Holdothers].
       1: left; by rewrite -Hrev Heff /=.
       rewrite -Hrev /=. assert (prm = pv) as ->. { clear -Hperm2. repeat case_match; by simplify_eq. }
       right. destruct (perm (item_lookup itold' l.2)) as [[]| | |]; simplify_eq; try done.
       rewrite bool_decide_decide in Hperm1. rewrite -Heq_scs. destruct (decide (protector_is_active (iprot itmod) (scs σ))).
       all: simplify_eq. 1: done. by left. } 
  all: rewrite -?Hrev; destruct (perm (item_lookup itold' l.2)) as [[] []| | |], (initialized (item_lookup itold' l.2)) as [];
    repeat (simpl; try simpl in Hperm1; try simpl in Holdothers; simplify_eq; try simpl in Hperm2; try done; destruct bool_decide).
  simpl in *. congruence.
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
      intros Hini Hdis.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite -Hx3 /= Hini /= in Hnondis. eapply Hnondis; first done. rewrite !Hdis in Hx1. simpl.
      assert (x1 = x2) as ->. 1: destruct (most_init _ _), bool_decide; simplify_eq; try done; destruct x1; by simplify_eq.
      clear Hx2.
      rewrite /apply_access_perm_inner in Hx1. destruct trees_rel_dec; by simplify_eq. }
    destruct Hcontrol as (itold' & trold' & Hitold' & Htrold' & Hisinit & Hfrozen & Hothers).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    assert (itold' = itold) as -> by by eapply tree_lookup_unique. clear Hitold'.
    (* old perm is frozen, it can not have survived the write *)
    pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
    rewrite Hfrozen /= in Hx1. destruct (trees_rel_dec (strs σ) l.1 tg_acc tg_lu); try done.
    pose proof Hx1 as [= <-].
    assert (x2 = Disabled) as -> by (destruct (most_init _ _), bool_decide; simplify_eq; done).
    rewrite -Hx3 Hisinit in Hnondis. by eapply Hnondis.
  - destruct Hpre as (itnew&(trnew'&Htrnew'&Hitnew)&Hnondis). 
    assert (trnew' = trnew) as -> by congruence. clear Htrnew'.
    eapply apply_trees_access_lookup_general_rev in Happly as Hitrev.
    2: apply Hwf. 2: eassumption. 2: exists trnew; split; first done; last exact Hitnew.
    destruct Hitrev as (itold & (trold' & Htrold' & Hitold) & Hinitit & Hprotit & Hpermit).
    assert (trold' = trold) as -> by congruence. clear Htrold'.
    destruct Hcontrol as (Hcontrol&_).
    { exists itold. split; first by eexists.
      pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite /apply_access_perm_inner in Hx1.
      rewrite -Hx3 /most_init /= in Hnondis.
      rewrite bool_decide_decide in Hx1,Hx2.
      destruct trees_rel_dec as [[]|[]], (perm (item_lookup itold l.2)), (initialized (item_lookup itold l.2)) as []; simpl in Hx2; simplify_eq; try done.
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
    ospecialize (Hsame _).
    { pose proof Hpermit as (x1&Hx1&(x2&Hx2&[=Hx3])%bind_Some)%bind_Some.
      rewrite /apply_access_perm_inner in Hx1.
      rewrite -Hx3 /most_init /= in Hnondis.
      rewrite bool_decide_decide in Hx1,Hx2.
      destruct trees_rel_dec as [[]|[]], (perm (item_lookup itold l.2)), (initialized (item_lookup itold l.2)) as []; simpl in Hx2; simplify_eq; try done.
      all: try specialize (Hnondis eq_refl).
      all: (try destruct decide); try by simplify_eq. }
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
      rewrite -!Hx3 -!Hprotit -?Heq_scs /= in Hnondis Hx1 Hx2.
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

Definition pointer_kind_to_tag_unprotected (pk : pointer_kind) : option tag_kind := match pk with
  Box im | MutRef im => match im with TyFrz => Some (tk_unq tk_res) | _ => None end (* can not have unprotected IM pointers around *)
| ShrRef => Some tk_pub end.

Definition pointer_kind_to_tag_protected (pk : pointer_kind) : tag_kind := match pk with
  Box _ | MutRef _ => tk_unq tk_res (* for protected, IM is not an issue *)
| ShrRef => tk_pub end.

Definition pointer_kind_to_tag_maybe_protected (rk : retag_kind) (pk : pointer_kind) : option tag_kind := match rk with
  Default => pointer_kind_to_tag_unprotected pk
| FnEntry => Some (pointer_kind_to_tag_protected pk) end.


Lemma pointer_kind_to_tag_maybe_protected_spec rk pk tk :
  pointer_kind_to_tag_maybe_protected rk pk = Some tk →
  (pk = ShrRef ∧ tk = tk_pub ∨ (∃ im, (pk = Box im ∨ pk = MutRef im) ∧ tk = tk_unq tk_res ∧ (rk = Default → im = TyFrz))).
Proof.
  assert (FnEntry = Default → InteriorMut = TyFrz) as HH by done.
  destruct rk, pk as [[]|[]|]; simpl; intros H; simplify_eq; eauto 10.
Qed.

Lemma if_both_sides_same {T} (b:bool) (t:T) : (if b then t else t) = t.
Proof. by destruct b. Qed.

Lemma loc_controlled_read_after_reborrow_creates Mcall cids l sc tg_cld tg_par tk σ σ' pk rk trs1 cc blk off1 sz:
  apply_within_trees (create_child cids tg_par tg_cld pk rk cc) blk σ.(strs) = Some trs1 →
  apply_within_trees (memory_access AccessRead cids tg_cld (off1, sz)) blk trs1 = Some σ'.(strs) →
  state_wf σ → wf_trees trs1 →
  l.1 = blk →
  trees_contain tg_par (strs σ) blk →
  ¬ trees_contain tg_cld (strs σ) blk →
  shp σ' !! l = Some sc →
  off1 ≤ l.2 < off1 + sz →
  cc ∈ σ'.(scs) →
  (rk = FnEntry → prot_in_call_set Mcall (Some {| strong := pointer_kind_to_strength pk; call := cc |}) tg_cld l) →
  pointer_kind_to_tag_maybe_protected rk pk = Some tk →
  loc_controlled Mcall l tg_cld tk sc σ'.
Proof.
  intros Hcreate Happly Hwf Hwf1 Hblk Hcont Hncont Hhp Hbound Hscs Hcallset Htk.
  intros _. split; last done.
  eapply bind_Some in Hcreate as (tr&Htr&(tr1&Hcreate&[= Htr1])%bind_Some).
  eassert (trees_lookup trs1 blk tg_cld _) as Hlucld1.
  { subst trs1. rewrite /trees_lookup /= lookup_insert /=. eexists; split; first done.
    unshelve eapply create_child_determined. 9: done. 1: exact σ.(scs). all: rewrite /trees_contain /trees_at_block Htr // in Hcont,Hncont. }
  pose (create_new_item tg_cld pk Default cc) as itcld. fold itcld in Hlucld1.
  eapply apply_trees_access_lookup_general in Happly as Happlyself.
  2: done. 3: apply Hlucld1. 2: exact Hbound.
  destruct Happlyself as (itcld'&Hitcld'&Hinitcld&Hiprotcld&Haccesscld).
  rewrite /= trees_rel_dec_refl -Hiprotcld /= {1} /item_lookup lookup_empty /= in Haccesscld.
  rewrite /apply_access_perm /= in Haccesscld.
  assert (∀ T (k:option T), match pointer_kind_to_perm pk with Disabled => None | _ => k end = k) as Hmatch1.
  1: by destruct pk.
  rewrite Hmatch1 /= Hmatch1 /= if_both_sides_same /= in Haccesscld. clear Hmatch1.
  injection Haccesscld as Haccesscld.
  destruct Hitcld' as (tr'&Htr'&Hitcld').
  destruct (pointer_kind_to_tag_maybe_protected_spec _ _ _ Htk) as [(->&->)|(im&H&->&Him)].
  - eexists itcld', tr'. split; first done. split; first by congruence.
    rewrite /bor_state_own_on.
    rewrite -Haccesscld; simpl. do 2 (split; first done).
    intros ito' to Hito'.
    eapply apply_trees_access_lookup_general_rev in Happly as Happlyself.
    2: done. 3: exists tr'; split; first congruence; exact Hito'. 2: exact Hbound.
    destruct Happlyself as (ito&Hito&Hinito&Hiproto&Haccesso).
    rewrite /trees_rel_dec -Htr1 lookup_insert /= in Haccesso.
    erewrite (memory_access_same_rel_dec false) in Haccesso.
    2: { eapply bind_Some in Happly as (x&Hx&(y&Hy&[= HH])%bind_Some).
         rewrite -Htr1 lookup_insert in Hx. assert (x = tr1) as -> by congruence.
         rewrite -HH lookup_insert in Htr'. assert (y = tr') as -> by congruence.
         exact Hy. }
    rewrite rel_dec_flip2 /apply_access_perm in Haccesso.
    eapply bind_Some in Haccesso as (p1&Hp1&(p2&Hp2&[= HH])%bind_Some).
    rewrite /apply_access_perm_inner in Hp1.
    destruct (rel_dec tr' to tg_cld) as [[]|[]], (perm (item_lookup ito l.2)) as [[] []| | |], (bool_decide (protector_is_active (iprot ito') cids)).
    all: simpl in Hp1; try discriminate Hp1; injection Hp1 as <-.
    all: destruct (initialized (item_lookup ito l.2)); simpl in Hp2; try discriminate Hp2; injection Hp2 as <-.
    all: try done. all: rewrite -HH; simpl; done.
  - eexists itcld', tr'. split; first done. split; first by congruence.
    rewrite /bor_state_own_on /bor_state_post_unq -Haccesscld; simpl. split; first done. split.
    { destruct im.
      2: destruct H as [-> | ->]; done.
      assert (protector_is_active (iprot itcld') (scs σ') ∧ prot_in_call_set Mcall (iprot itcld') tg_cld l).
      2: destruct H as [-> | ->]; done.
      destruct rk; last by (specialize (Him eq_refl)).
      rewrite -Hiprotcld. split.
      - exists cc; split; done.
      - eapply Hcallset. done. }
    intros ito' to Hito'.
    eapply apply_trees_access_lookup_general_rev in Happly as Happlyself.
    2: done. 3: exists tr'; split; first congruence; exact Hito'. 2: exact Hbound.
    destruct Happlyself as (ito&Hito&Hinito&Hiproto&Haccesso).
    rewrite /trees_rel_dec -Htr1 lookup_insert /= in Haccesso.
    erewrite <- (memory_access_same_rel_dec false).
    2: { eapply bind_Some in Happly as (x&Hx&(y&Hy&[= HH])%bind_Some).
         rewrite -Htr1 lookup_insert in Hx. assert (x = tr1) as -> by congruence.
         rewrite -HH lookup_insert in Htr'. assert (y = tr') as -> by congruence.
         exact Hy. }
    rewrite rel_dec_flip2 /apply_access_perm in Haccesso.
    eapply bind_Some in Haccesso as (p1&Hp1&(p2&Hp2&[= HH])%bind_Some).
    rewrite /apply_access_perm_inner in Hp1.
    destruct (rel_dec tr1 to tg_cld) as [[]|pos] eqn:Hreldec.
    3: { rewrite /rel_dec in Hreldec. destruct (decide (ParentChildIn tg_cld to tr1)) as [Hc|]; last done.
         destruct (decide (ParentChildIn to tg_cld tr1)) as [Hc2|Hc2].
         1: by injection Hreldec as <-.
         exfalso. eapply insertion_order_nonparent. 4: done. 4: exact Hc.
         - destruct Hito as (tr1X&HX&Hito). assert (tr1X = tr1) as ->.
           { rewrite -Htr1 lookup_insert in HX. congruence. }
           injection Hcreate as <-.
           eapply remove_false_preserves_exists. 2: eapply Hito.
           simpl. intros ->. eapply Hc2. by left.
         - intros Hx. eapply Hncont. by rewrite /trees_contain /trees_at_block Htr.
         - by rewrite /trees_contain /trees_at_block Htr in Hcont. }
    2: enough (match perm (item_lookup ito' l.2) with Active => False | _ => True end) as Heno.
    2: { eapply bind_Some in Happly as (X&HX&(Y&Happly&[= HY])%bind_Some).
         assert (X = tr1) as ->. { rewrite -Htr1 lookup_insert // in HX; congruence. }
         assert (Y = tr') as ->. { rewrite -HY lookup_insert /= in Htr'; congruence. }
         destruct (perm (item_lookup ito' l.2)) as [[]| | |] eqn:Heq; simpl. 3: done. 2,3: right; left; done.
         all: right; tauto. }
    all: destruct (perm (item_lookup ito l.2)) as [[] []| | |], (bool_decide (protector_is_active (iprot ito') cids)).
    all: simpl in Hp1; try discriminate Hp1; injection Hp1 as <-.
    all: destruct (initialized (item_lookup ito l.2)); simpl in Hp2; try discriminate Hp2; injection Hp2 as <-.
    all: try done. all: rewrite -HH; simpl; try done; tauto.
Qed.

Lemma create_child_tree_lookup C tg_par tg_cld pk rk cc tr tr' tg it :
  tg ≠ tg_cld →
  create_child C tg_par tg_cld pk rk cc tr = Some tr' →
  tree_lookup tr tg it ↔ tree_lookup tr' tg it.
Proof.
  intros Hne [= <-].
  split; intros (Hcont&Hdet); split.
  - by eapply insert_preserves_exists.
  - setoid_rewrite <- insert_true_preserves_every; first done.
    simpl. intros H; done.
  - eapply insert_false_infer_exists; last done. simpl. done.
  - setoid_rewrite insert_true_preserves_every; first done.
    simpl. intros H; done.
Qed.

Lemma create_child_tree_lookup_new C tg_par tg_cld pk rk cc tr tr' it :
  tree_contains tg_par tr → ¬ tree_contains tg_cld tr →
  create_child C tg_par tg_cld pk rk cc tr = Some tr' →
  tree_lookup tr' tg_cld it → it = create_new_item tg_cld pk rk cc.
Proof.
  intros Hin Hnin Hcc Hlu.
  eapply tree_lookup_unique. 1: eapply Hlu.
  eapply create_child_determined. all: done.
Qed.

Lemma create_child_tree_lookup_general C tg_par tg_cld pk rk cc tr tr' tg it :
  tree_contains tg_par tr → ¬ tree_contains tg_cld tr →
  create_child C tg_par tg_cld pk rk cc tr = Some tr' →
  tree_lookup tr' tg it → tg ≠ tg_cld ∧ tree_lookup tr tg it ∨ tg = tg_cld ∧ it = create_new_item tg_cld pk rk cc.
Proof.
  intros Hin Hnin Hcc Hlu. destruct (decide (tg = tg_cld)) as [->|Hne].
  - right. split; first done. by eapply create_child_tree_lookup_new.
  - left. split; first done. by eapply create_child_tree_lookup.
Qed.

Lemma create_child_rel_dec tg1 tg2 C tg_par tg_cld pk rk cc tr tr' :
  tg1 ≠ tg_cld → tg2 ≠ tg_cld →
  create_child C tg_par tg_cld pk rk cc tr = Some tr' →
  rel_dec tr tg1 tg2 = rel_dec tr' tg1 tg2.
Proof.
  intros Hn1 Hn2 [= <-]. pose (create_new_item tg_cld pk rk cc) as it. fold it.
  rewrite /rel_dec /=.
  destruct (decide (ParentChildIn tg2 tg1 tr)) as [HPC1|HPC1].
  all: setoid_rewrite (insert_eqv_rel _ _ it) in HPC1; [|done..].
  all: try erewrite (decide_True _ _ HPC1); try erewrite (decide_False _ _ HPC1).
  all: f_equal.
  all: destruct (decide (ParentChildIn tg1 tg2 tr)) as [HPC2|HPC2].
  all: setoid_rewrite (insert_eqv_rel _ _ it) in HPC2; [|done..].
  all: try erewrite (decide_True _ _ HPC2); try erewrite (decide_False _ _ HPC2).
  all: f_equal.
  1: destruct (decide (ImmediateParentChildIn tg2 tg1 tr)) as [HPC3|HPC3].
  3: destruct (decide (ImmediateParentChildIn tg1 tg2 tr)) as [HPC3|HPC3].
  all: setoid_rewrite (insert_eqv_imm_rel _ _ it) in HPC3; [|done..].
  all: try erewrite (decide_True _ _ HPC3); try erewrite (decide_False _ _ HPC3).
  all: f_equal.
Qed.

Lemma create_child_rel_dec_new tg1 tg2 C tg_par tg_cld pk rk cc tr tr' rr :
  wf_tree tr → wf_tree tr' →
  tree_contains tg_par tr → ¬ tree_contains tg_cld tr → tree_contains tg2 tr' →
  create_child C tg_par tg_cld pk rk cc tr = Some tr' →
  rel_dec tr' tg1 tg2 = rr →
  tg2 ≠ tg_cld →
  (tg1 ≠ tg_cld ∧ rel_dec tr tg1 tg2 = rr) ∨
  (tg1 = tg_cld ∧ tg2 = tg_par ∧ rr = Child (Strict Immediate)) ∨
  (tg1 = tg_cld ∧ tg2 ≠ tg_par ∧ rr = Child (Strict FurtherAway) ∧ ∃ i, rel_dec tr tg_par tg2 = Child (Strict i)) ∨
  (tg1 = tg_cld ∧ tg2 ≠ tg_par ∧ rr = Foreign Cousin ∧ ∃ f, rel_dec tr tg_par tg2 = Foreign f).
Proof.
  intros Hwf1 Hwf2 Hn1 Hn2 Hin2 Hcc Hreldec Hne2.
  pose (create_new_item tg_cld pk rk cc) as it. pose (insert_child_at tr it (IsTag tg_par)) as trin.
  assert (tg_cld = itag it) as Htgit by done.
  assert (tg_par ≠ tg_cld) as Hnepc by by intros ->.
  destruct (decide (tg1 = tg_cld)) as [->|Hne]; [right|left]; last first.
  { split; first done. rewrite -Hreldec. by eapply create_child_rel_dec. }
  injection Hcc as <-. rename trin into tr'. fold it tr' in Hreldec.
  destruct (decide (tg2 = tg_par)) as [->|Hne']; [left|right].
  { do 2 (split; first done). subst rr. rewrite /rel_dec.
    eassert _ as HA1; last (rewrite decide_True; last exact HA1).
    1: by eapply insert_produces_ParentChild.
    rewrite decide_False. 2: intros [?|HSP]; first done.
    2: eapply strict_parent_self_impossible; last by eapply ParentChild_StrictParentChild.
    2: by eapply insert_preserves_exists.
    rewrite decide_True //.
    by eapply (insert_produces_ImmediateParentChild _ it). }
  rewrite /rel_dec in Hreldec. destruct (decide (ParentChildIn tg2 tg_cld tr')) as [HPC|HPC].
  - left. destruct HPC as [->|HPC]. 1: done. do 2 (split; first done).
    rewrite decide_False in Hreldec; last first.
    { intros [->|HCC]; first done. eapply strict_parent_self_impossible. 2: by eapply StrictParentChild_transitive.
      eapply insert_true_produces_exists; done. }
    rewrite Htgit in HPC. eapply insert_produces_minimal_ParentChild in HPC; [|done..].
    rewrite decide_False in Hreldec; last first.
    { intros Himm. eapply (insert_eqv_strict_rel _ _ it) in HPC. 2-3: done.
      eapply immediate_not_transitive_strong_2. 1-4: eapply Hwf2. 6: exact Himm. 4: exact HPC.
      3: by eapply insert_true_produces_exists. 1: done. 1: by eapply insert_preserves_exists.
      rewrite Htgit. by eapply insert_produces_StrictParentChild. }
    subst rr. split; first done.
    rewrite /rel_dec decide_True. 2: by right.
    rewrite /rel_dec decide_False. 1: by eexists.
    intros [?|HCC]; first done.
    eapply strict_parent_self_impossible. 2: by eapply StrictParentChild_transitive. done.
  - right. eassert (¬ _) as HSPC. 1: intros H; eapply HPC; right; exact H.
    do 2 (split; first done). rewrite decide_False in Hreldec; last first.
    { intros [?|HSPC2]; first done. rewrite Htgit in HSPC2.
      eapply inserted_not_strict_parent. 3: exact HSPC2. 1-2: done. }
    subst rr. split; first done.
    rewrite /rel_dec. rewrite decide_False; first by eexists.
    intros [?|HSPC3]; first done. eapply HSPC. eapply StrictParentChild_transitive.
    2: rewrite Htgit; by eapply insert_produces_StrictParentChild.
    unfold tr'.
    setoid_rewrite <- insert_eqv_strict_rel; first exact HSPC3. all: done.
Qed.

Lemma loc_controlled_create_child_preserved l sc σ σ' blk C tg_par tg_cld pk rk cc tg_lu tk Mcall:
  apply_within_trees (create_child C tg_par tg_cld pk rk cc) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  state_wf σ' →
  l.1 = blk →
  trees_contain tg_par σ.(strs) blk →
  ¬ trees_contain tg_cld σ.(strs) blk →
  tg_lu ≠ tg_cld →
  (tg_par = tg_lu → tk = tk_pub) →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hwf2 Hblk Htgpar Htgcld Htgne Hnotlocal Hlc.
  subst blk.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  assert (strs σ' !! l.1 = Some trnew) as Htrnew.
  { by rewrite -Hstrs lookup_insert. }
  rewrite /loc_controlled. rewrite -Heq_shp.
  pose proof Htgcld as Htgcldtr. rewrite /trees_contain /trees_at_block Htrold in Htgcldtr.
  pose proof Htgpar as Htgpartr. rewrite /trees_contain /trees_at_block Htrold in Htgpartr.
  destruct tk as [|act|] eqn:Heq; simpl.
  - intros (it & Htrlu & Hperm).
    destruct Htrlu as (trnew2 & Htrnew2 & Htrlu).
    assert (trnew2 = trnew) as -> by congruence.
    eapply create_child_tree_lookup in Htrlu as Htrluold; last done. 2: done.
    destruct Hlc as (Hownold & Hscold).
    1: exists it; split; last done; by exists trold.
    split; last done.
    destruct Hownold as (it'&trold'&Hluit'&Htrold'&Hinit&Hpermo&Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (it' = it) as -> by by eapply tree_lookup_unique.
    exists it, trnew. do 4 (split; first done).
    intros it' t' Hit'.
    remember (rel_dec trnew t' tg_lu) as rr eqn:Hreldec. symmetry in Hreldec.
    eapply create_child_rel_dec_new in Hreldec. 7: by eapply Haccess. 2: by eapply Hwf. 2: by eapply Hwf2. 2,3,5: done. 2: by eapply lookup_implies_contains.
    destruct Hreldec as [(Hne&Hreldec)|[(->&->&->)|[(->&Hne&->&ii&Hreldec)|(->&Hne&->&ff&Hreldec)]]].
    { subst rr. eapply Hothers. eapply create_child_tree_lookup; last done. 2: done. done. }
    all: eapply create_child_tree_lookup_new in Hit' as ->; [..|exact Haccess]; [|done..].
    all: rewrite /create_new_item /item_lookup /= lookup_empty /=; by destruct pk.
  - intros (it & Htrlu & Hperm).
    destruct Htrlu as (trnew2 & Htrnew2 & Htrlu).
    assert (trnew2 = trnew) as -> by congruence.
    eapply create_child_tree_lookup in Htrlu as Htrluold; last done. 2: done.
    destruct Hlc as (Hownold & Hscold).
    1: exists it; split; last done; by exists trold.
    split; last done.
    destruct Hownold as (it'&trold'&Hluit'&Htrold'&Hinit&Hpermo&Hothers).
    assert (trold' = trold) as -> by congruence.
    assert (it' = it) as -> by by eapply tree_lookup_unique.
    exists it, trnew. do 3 (split; first done).
    split.
    { rewrite -Heq_scs. eapply Hpermo. }
    intros it' t' Hit'.
    remember (rel_dec trnew t' tg_lu) as rr eqn:Hreldec. symmetry in Hreldec.
    eapply create_child_rel_dec_new in Hreldec. 7: by eapply Haccess. 2: by eapply Hwf. 2: by eapply Hwf2. 2,3,5: done. 2: by eapply lookup_implies_contains.
    destruct Hreldec as [(Hne&Hreldec)|[(->&->&->)|[(->&Hne&->&ii&Hreldec)|(->&Hne&->&ff&Hreldec)]]].
    { subst rr. eapply create_child_tree_lookup in Hit'; last done; last done.
      specialize (Hothers _ _ Hit'). destruct (rel_dec trold t' tg_lu) as [[]|[]] eqn:Hreldec. 1,3,4: eapply Hothers.
      destruct Hothers as [Hini|Hothers]; [left|right]; first done.
      by rewrite -Heq_scs. }
    { by specialize (Hnotlocal eq_refl). }
    { done. }
    { eapply create_child_tree_lookup_new in Hit' as ->; [..|exact Haccess]; [|done..].
      left. by rewrite /item_lookup /= lookup_empty /=. }
  - destruct Hlc as (Hownold & Hscold). 1: done.
    exfalso; ospecialize (Hnotlocal _); last done.
    destruct Hownold as (it'&trold'&Hluit'&Htrold'&Hinit&Hpermo&Hothers).
    assert (trold' = trold) as -> by congruence.
    opose proof* unique_implies_lookup as (itpar&Hlupar).
    { eapply Hwf. 2: exact Htgpartr. done. }
    symmetry. eapply Hothers. done.
Qed.

Lemma loc_controlled_create_child_preserved_outside l sc σ σ' blk C tg_par tg_cld pk rk cc tg_lu tk Mcall:
  apply_within_trees (create_child C tg_par tg_cld pk rk cc) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  state_wf σ' →
  l.1 ≠ blk →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hwf2 Hblk Hlc.
  pose proof Happly as (trold&Htrold&(trnew&Haccess&[= Hstrs])%bind_Some)%bind_Some.
  rewrite /loc_controlled. rewrite -Heq_shp.
  destruct tk.
  - intros (it&Hit&HH).
    rewrite /trees_lookup -Hstrs lookup_insert_ne // in Hit.
    destruct Hlc as (Hown&Hhp). 1: by exists it. split; last done.
    destruct Hit as (tr&Htr&Hit).
    destruct Hown as (it'&tr'&Hit'&Htr'&Hx).
    assert (tr = tr') as <- by (rewrite Htr in Htr'; congruence).
    assert (it = it') as <- by by eapply tree_lookup_unique.
    exists it, tr. rewrite -Hstrs lookup_insert_ne //.
  - intros (it&Hit&HH).
    rewrite /trees_lookup -Hstrs lookup_insert_ne // in Hit.
    destruct Hlc as (Hown&Hhp). 1: by exists it.
    destruct Hit as (tr&Htr&Hit).
    destruct Hown as (it'&tr'&Hit'&Htr'&Hinit&Hrst).
    assert (tr = tr') as <- by (rewrite Htr in Htr'; congruence).
    assert (it = it') as <- by by eapply tree_lookup_unique. split; last done.
    exists it, tr. rewrite -Hstrs lookup_insert_ne //.
    do 3 (split; first done).
    rewrite /bor_state_post_unq -Heq_scs. done.
  - intros _.
    destruct Hlc as (Hown&Hhp). 1: done.
    split; last done.
    destruct Hown as (it&tr&Hit'&Htr'&Hinit&Hown&Hothers).
    exists it, tr. rewrite -Hstrs lookup_insert_ne //.
Qed.

Lemma loc_controlled_create_child_preserved_everywhere l sc σ σ' blk C tg_par tg_cld pk rk cc tg_lu tk Mcall:
  apply_within_trees (create_child C tg_par tg_cld pk rk cc) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  state_wf σ' →
  trees_contain tg_par σ.(strs) blk →
  ¬ trees_contain tg_cld σ.(strs) blk →
  tg_lu ≠ tg_cld →
  (tg_par = tg_lu → tk = tk_pub) →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled Mcall l tg_lu tk sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hwf2 Htgpar Htgcld Htgne Hnotlocal Hlc.
  destruct (decide (l.1 = blk)) as [Hblk|Hne].
  - by eapply loc_controlled_create_child_preserved.
  - by eapply loc_controlled_create_child_preserved_outside.
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
      intros Hini Hdis. eapply Hperm.
      * eapply apply_access_perm_read_initialized; eassumption.
      * eapply apply_access_perm_read_not_disabled; eassumption.
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
      destruct (most_init (initialized (item_lookup itold' l.2)) (requires_init (rel_dec trold tg_acc t'))) as [] eqn:Hmostinit.
      all: repeat (case_match; simpl in Hperm2; simplify_eq; try rewrite <- Hperm2; try (rewrite (Hwitold' eq_refl) /= in Hmostinit); simpl in Hperm2; try done).
  - intros (it & Htrlu & Hndis).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_general_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done.
      intros HH Hdis; eapply apply_access_perm_read_not_disabled in Hdis; last done.
      eapply Hndis; try done; by eapply apply_access_perm_read_initialized.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold2 & Htrold2 & Hluold).
      assert (trold2 = trold) as -> by congruence. clear Htrold2. rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hisinit & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew2 & Htrnew2 & Hlunew).
      assert (trnew2 = trnew) as -> by congruence.
      exists it, trnew. do 2 (split; first done).
      split; first by eapply apply_access_perm_read_initialized.
      assert ((perm (item_lookup it l.2) = Frozen → protector_is_active (iprot it) (scs σ')) → ((perm (item_lookup itold l.2) = Frozen → protector_is_active (iprot itold) (scs σ)))) as HP.
      { intros Hfrzprot Hfrz. rewrite Heq2 Heq_scs. eapply Hfrzprot.
        erewrite apply_access_perm_read_frozen. all: done. }
      assert (lazy_perm_wf (item_lookup itold l.2)) as Hwfitold.
      { eapply item_wf_lookup. pose (state_wf_tree_compat _ Hwf) as Hcompat.
        specialize (Hcompat _ _ Htrold). rewrite /tree_items_compat_nexts every_node_iff_every_lookup in Hcompat.
        1: by eapply Hcompat. eapply wf_tree_tree_item_determined. by eapply Hwf. }
      rewrite /lazy_perm_wf in Hwfitold. rewrite /bor_state_post_unq.
      match goal with |- ((?P -> ?A) ∧ ?B) => assert (P → (A ∧ match trees_rel_dec (strs σ) l.1 tg_acc tg_lu with 
          Foreign (Parent _) => act = tk_res ∨ (b = true) | Foreign _ => act = tk_res | _ => True end)) as Hfpar end.
      { clear Hothers. intros Hfrzprot.
        ospecialize (Hsame _). 1: by eapply HP.
        rewrite -Heq2 -Heq_scs. edestruct maybe_non_children_only_effect_or_nop_strong as [(Heqcc&Hne)|(Heqcc&He1&childkind&He2)]; erewrite Heqcc in Heq3.
        2: { injection Heq3 as <-. rewrite He2. split; first done. by right. }
        pose proof Heq3 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
        rewrite -HH -?Heq_scs /= in Hfrzprot|-*.
        rewrite /apply_access_perm_inner in Hx1.
        assert (perm (item_lookup itold l.2) = Active → most_init (initialized (item_lookup itold l.2)) (requires_init (trees_rel_dec (strs σ) l.1 tg_acc tg_lu)) = PermInit) as HHH.
        { intros H; by rewrite Hwfitold. }
        repeat (case_match; simplify_eq; (try specialize (HHH eq_refl)); (try (destruct Hsame; [ idtac ])); try done; try (split; [done | (try by left); by right ])).
        all: exfalso; eapply bool_decide_eq_false_1; last apply (Hfrzprot eq_refl). all: done.
        }
      split.
      { intros Hfrzprot. by eapply Hfpar. }
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
      2: { injection Hperm2 as <-. rewrite -Hprot2 -Heq_scs.
           destruct (rel_dec trold t' tg_lu) as [[]|]; [done| |done].
           destruct Hothers as [?|Ho]; first by left. right.
           destruct (perm (item_lookup itold' l.2)) as [[]| | |]; try done.
           - destruct Ho as [H|[H|H]]. 1: by left. 1: right; by left. do 2 right. intros HH. eapply H. eapply HP. by rewrite -Heq_scs.
           - destruct Ho as [H|H]. 1: by left. right. intros HH. eapply H. eapply HP. by rewrite -Heq_scs.
           - destruct Ho as [H|H]. 1: by left. right. intros HH. eapply H. eapply HP. by rewrite -Heq_scs. }
      pose proof Hperm2 as (x1&Hx1&(x2&Hx2&[= HH])%bind_Some)%bind_Some.
      rewrite -HH -?Heq_scs /= in |-*.
      rewrite /apply_access_perm_inner in Hx1. clear Heqcc.
      rewrite /trees_rel_dec Htrold in Hfpar HH Hx1 Hne|-*.
      rewrite /trees_contain /trees_at_block Htrold in Htgin.
      rewrite -Hprot2. rewrite /trees_rel_dec /= Htrold in Heq3.
      assert (wf_tree trold) as Hwfold by by eapply Hwf.
      opose proof (rel_dec_concat_foreign _ tg_acc t' tg_lu _ _ _ _) as HtransiF.
      1-4: try done; eapply wf_tree_tree_unique; try done; by eapply lookup_implies_contains.
      simpl in Hothers.
      destruct (rel_dec trold t' tg_lu) as [[]|[[]|]]. 4,5: done.
      2: { assert (x1 = x2). { clear -Hx2. repeat case_match; by simplify_eq. } subst x2.
           destruct (rel_dec trold tg_acc t') as [] eqn:Hreldec_acc_lu.
           - simpl. destruct Hothers as [Hnoinit|Hothers]. 1: left; by rewrite Hnoinit.
             right. destruct (perm (item_lookup itold' l.2)) as [[] []| | |], (bool_decide (protector_is_active (iprot itnew') (scs σ)));
             simplify_eq.
             all: try exact I.
             all: do 2 try (destruct Hothers as [H|Hothers]; [by left | right]); try done.
             all: intros H1; eapply Hothers, HP. all: by rewrite -Heq_scs.
           - rewrite Hreldec_strong in Hreldec. right.
             opose proof* child_of_this_is_foreign_for_cousin as Hcousin; [| | | exact Hreldec | by erewrite Hreldec_acc_lu| ]; [eapply Hwf; first done..|];
               [eapply Hitoldlu'|eapply Hluold|eapply Htgin|].
             rewrite Hcousin in Hfpar. 
             destruct (perm (item_lookup itold' l.2)) as [[]| | |] eqn:Heqold; simplify_eq.
             3: { destruct Hothers as [Ho|?]; last done. by rewrite Hwfitold' in Ho. }
             all: destruct act; first eauto.
             1: right. all: right.
             all: intros HF; destruct Hfpar as (_&[=]). all: by rewrite -Heq_scs. }
      all: clear Hfpar HtransiF.
      all: repeat (case_match; simplify_eq; (try specialize (Hwfitold' eq_refl)); unfold most_init in *;
           simplify_eq; try done).
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold' & Hluold & Htrold' & Hisinit & Hsame & Hnoprot & Hothers).
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
    split; first by rewrite -Hprotold.
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

Lemma protected_priv_loc_does_not_survive_access σ σ' M_tag M_hl M_call off1 sz blk tg_acc tg_lu l acc Mcall P :
  apply_within_trees (memory_access acc σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  call_set_interp P M_call σ →
  M_tag !! tg_acc = Some (tk_pub, ()) →
  priv_loc M_tag M_hl M_call tg_lu l →
  (∀ tg tk sc, M_tag !! tg = Some (tk, ()) → heaplet_lookup M_hl (tg, l) = Some sc → loc_controlled Mcall l tg tk sc σ) →
  False.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hcs Hactually_public Hpl Hlc.
  destruct Hpl as (tk&Htk&(sc&Hsc)&Hpriv).
  eapply trees_contain_trees_lookup_1 in Htgin as (itacc&(tr&Htr&Hitacc)); last apply Hwf.
  specialize (Hlc tg_lu tk sc Htk Hsc).
  destruct Hpriv as [->|(cc&ae&->&Hcc)].
  - destruct Hlc as ((it&tr'&Hit&Htr'&Hactive&Hunq)&_); first done.
    assert (tr' = tr) as -> by congruence.
    enough (tg_lu = tg_acc) as -> by congruence.
    eapply Hunq. done.
  - destruct Hcc as (Mcc&HMcc&Lcc&HLcc&Hlincc).
    destruct Hcs as (Hcs&_).
    specialize (Hcs _ _ HMcc) as (Hccact&Hcs).
    specialize (Hcs _ _ HLcc) as (Htgluvalid&Hcs).
    specialize (Hcs l _ Hlincc) as (itlu&(tr'&Htr'&Hitlu)&Hprot1&HprotSM&Hprot2&Hcs).
    assert (tr' = tr) as -> by congruence.
    destruct Hlc as (Hlc&_).
    { eexists. split; first by eexists. done. }
    destruct Hlc as (itlu'&tr'&Hitlu'&Htr''&Hisinit&Hsame&Hothers).
    assert (tr' = tr) as -> by congruence.
    assert (itlu' = itlu) as -> by by eapply tree_lookup_unique.
    subst blk.
    ospecialize (Hsame _).
    { intros _. by eexists. }
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

Lemma protected_active_loc_does_not_survive_write_access σ σ' (M_tag : gmap nat (tag_kind * ())) M_hl M_call off1 sz blk tg_acc tg_lu l Mcall P :
  apply_within_trees (memory_access AccessWrite σ.(scs) tg_acc (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  (off1 ≤ l.2 < off1 + sz) →
  trees_contain tg_acc σ.(strs) blk →
  call_set_interp P M_call σ →
  M_tag !! tg_acc = Some (tk_pub, ()) →
  (∃ tk, M_tag !! tg_lu = Some (tk, ()) ∧ is_Some (heaplet_lookup M_hl (tg_lu, l)) ∧ ∃ c ae ak, tk = tk_unq ak ∧ call_set_in' M_call c tg_lu l (EnsuringAccess ae)) →
  (∀ tg tk sc, M_tag !! tg = Some (tk, ()) → heaplet_lookup M_hl (tg, l) = Some sc → loc_controlled Mcall l tg tk sc σ) →
  False.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Htgin Hcs Hactually_public Hpl Hlc.
  destruct Hpl as (tk&Htk&(sc&Hsc)&Hpriv).
  eapply trees_contain_trees_lookup_1 in Htgin as (itacc&(tr&Htr&Hitacc)); last apply Hwf.
  specialize (Hlc tg_lu tk sc Htk Hsc).
  destruct Hpriv as (cc&ae&ak&->&Hcc).
  destruct Hcc as (Mcc&HMcc&Lcc&HLcc&Hlincc).
  destruct Hcs as (Hcs&_).
  specialize (Hcs _ _ HMcc) as (Hccact&Hcs).
  specialize (Hcs _ _ HLcc) as (Htgluvalid&Hcs). 
  specialize (Hcs l _ Hlincc) as (itlu&(tr'&Htr'&Hitlu)&Hprot1&HprotSM&Hprot2&Hcs).
  assert (tr' = tr) as -> by congruence.
  destruct Hlc as (Hlc&_).
  { eexists. split; first by eexists. done. }
  destruct Hlc as (itlu'&tr'&Hitlu'&Htr''&Hisinit&Hsame&Hothers).
  assert (tr' = tr) as -> by congruence.
  assert (itlu' = itlu) as -> by by eapply tree_lookup_unique.
  subst blk.
  ospecialize (Hsame _).
  { intros _. by eexists. }
  destruct (rel_dec tr tg_acc tg_lu) as [fk|[ck|]] eqn:Hreldec.
  + assert (trees_lookup σ.(strs) l.1 tg_lu itlu) as Hitluold by by eexists.
    pose Hitluold as HH.
    eapply (apply_trees_access_lookup_general false) in HH; [|eapply Happly|eapply Hwf|done].
    destruct HH as (itlunew&(trnew&Htrnew&Hitlunew)&Hinitplu&Hiprotlu&Hpermlu).
    rewrite /trees_rel_dec Htr in Hpermlu.
    assert (protector_is_active (iprot itlunew) (scs σ)) as Hisprot.
    { exists cc. rewrite -Hiprotlu //. }
    rewrite Hreldec /= /apply_access_perm /apply_access_perm_inner /= in Hpermlu.
    rewrite bool_decide_eq_true_2 // Hisinit /= in Hpermlu.
    by destruct (perm (item_lookup itlu l.2)) as [[]| | |].
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
    done.
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
    intros Hini Hdis. rewrite Hdis in Happlyself. done. } 
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
    exists itp. by rewrite Htrs.
  - split; last done.
    exists it, tr. rewrite -Htrs. rewrite /bor_state_own_on. split_and!; try done. split.
    + clear Hothers. intros HH. ospecialize (Hsame _).
      { setoid_rewrite <- HHscs in HH. 2: by eexists. done. } 
      case_match; try done.
      case_match; try done. destruct Hsame as (->&Hprot&Hcs).
      split_and!; first done.
      * setoid_rewrite <- HHscs; first done.
        by eexists.
      * destruct Hcs as (ls&ps&Hiprot&Hcs'&Hstrong).
        exists ls, ps. split_and!; try done.
        rewrite /= /call_set_in' lookup_insert_ne //.
        specialize (state_wf_tree_compat _ Hwf _ _ Hit) as Hwfcompat.
        setoid_rewrite every_node_iff_every_lookup in Hwfcompat.
        2: by eapply wf_tree_tree_item_determined, Hwf.
        specialize (Hwfcompat _ _ Htr).
        opose proof (item_cid_valid _ _ _ Hwfcompat (ps.(call)) _) as ?. 2: lia.
        rewrite Hiprot. by destruct ps.
    + intros it' t' H. specialize (Hothers it' t' H).
      destruct (rel_dec tr t' tg) as [[]|]. 1,3: eapply Hothers.
      destruct Hothers as [?|Hothers]; first by left. right.
      destruct (perm (item_lookup it' l.2)) as [[]| | |]. 3, 5: done.
      all: do 2 try (destruct Hothers as [Hothers|Hothers]; [left; try done|right]).
      all: intros HP; eapply Hothers; intros; eapply HHscs; first (exists tr; done).
      all: by eapply HP.
Qed.


Lemma loc_controlled_extend_protected l tg tk sc σ σ' Mcall c_ext M_ext tg_ext L_ext:
  shp σ = shp σ' →
  strs σ = strs σ' →
  scs σ = scs σ' →
  state_wf σ →
  Mcall !! c_ext = Some M_ext →
  M_ext !! tg_ext = None →
  loc_controlled Mcall l tg tk sc σ →
  loc_controlled (<[c_ext := <[tg_ext := L_ext]> M_ext]> Mcall) l tg tk sc σ'.
Proof.
  intros Hhp Htrs Hscs Hwf Hold Hfresh Hlc Hpre.
  rewrite -Hhp.
  destruct tk as [|acc|].
  all: rewrite /loc_controlled /bor_state_pre /bor_state_own in Hlc,Hpre|-*.
  1,3: rewrite Htrs in Hlc; apply Hlc, Hpre.
  destruct Hlc as ((it&tr&Htr&Hit&Hinit&Hsame&Hothers)&Hhpc).
  - destruct Hpre as (itp&Hitp&HH).
    exists itp. by rewrite Htrs.
  - split; last done.
    exists it, tr. rewrite -Htrs. rewrite /bor_state_own_on. split_and!; try done.
    split.
    + clear Hothers. 
      intros H3. ospecialize (Hsame _).
      1: rewrite Hscs //.
      case_match; try done.
      case_match; try done. destruct Hsame as (->&Hprot&Hcs).
      split_and!; first done.
      * rewrite <- Hscs; first done.
      * destruct Hcs as (ls&ps&Hiprot&Hcs&Hstrong).
        exists ls, ps. split_and!; try done.
        rewrite /call_set_in'.
        destruct Hcs as (M&HM&HHM). destruct (decide (call ps = c_ext)) as [<-|Hne].
        2: rewrite lookup_insert_ne //; by eexists.
        rewrite lookup_insert. eexists. split; first done.
        rewrite Hold in HM. assert (M_ext = M) as -> by congruence.
        destruct HHM as (L&HL&HHL).
        destruct (decide (tg = tg_ext)) as [->|Hne2].
        2: exists L; rewrite lookup_insert_ne; done.
        exfalso. rewrite Hfresh in HL. done.
    + intros it' t' H. specialize (Hothers it' t' H).
      destruct (rel_dec tr t' tg) as [[]|]. 1,3: eapply Hothers.
      destruct Hothers as [?|Hothers]; first by left. right.
      destruct (perm (item_lookup it' l.2)) as [[]| | |]. all: by rewrite -?Hscs.
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
    rewrite /loc_controlled /bor_state_pre /bor_state_own /bor_state_own_on /bor_state_pre_unq /bor_state_post_unq.
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
  edestruct Hlc2 as (Hpost&HHL). 1: done.
  split; last done.
  destruct tk; [done| |done].
  destruct Hpost as (it&tr&Hit&Htr&Hinit&Hown&Hothers).
  exists it, tr. do 3 (split; first done).
  split.
  - intros Hit3. clear Hothers. ospecialize (Hown _).
    { intros Hperm. destruct (Hit3 Hperm) as (cc&Hcc1&Hcc2).
      exists cc. split; try done. eapply elem_of_difference, Hcc2. }
    repeat (case_match; try done; []).
    destruct Hown as (Ho1&(cc&Hcc1&Hcc2)&Ho3). split; first done.
    destruct (iprot it) as [[p cc2]|]; last done. injection Hcc1 as ->.
    assert (c ≠ cc) as Hne.
    { intros ->. simpl in Ho3. destruct Ho3 as (ls&ps&[= <-]&(M&HM&(X&HX&_))&_). rewrite /= Hcalls in HM. injection HM as <-.
      rewrite lookup_empty in HX. done. }
    split.
    + exists cc. split; first done. simpl. rewrite /call_is_active. eapply elem_of_difference; split; first done. set_solver.
    + destruct Ho3 as (ls&ps&[= <-]&(M&HM&HHM)&Hstrong). eexists ls, _. split_and!; try done. exists M; split; last done.
      rewrite /= lookup_delete_ne; done.
  - intros it' t' H. specialize (Hothers it' t' H).
    destruct (rel_dec tr t' tg_lu) as [[]|]. 1,3: eapply Hothers.
    destruct Hothers as [?|Hothers]; first by left. right.
    destruct (perm (item_lookup it' l.2)) as [[]| | |]. 3, 5: done.
    all: do 2 try (destruct Hothers as [Hothers|Hothers]; [left; try done|right]).
    all: intros HP; eapply Hothers; intros.
    all: destruct HP as (cc&Hcc&HHcc); try done.
    all: exists cc; split; first done. all: eapply elem_of_difference in HHcc; eapply HHcc.
Qed.

Lemma loc_controlled_alloc_creates_local l σ σ' blk Mcall nt sz :
  init_mem (fresh_block (shp σ), 0) sz (shp σ) = shp σ' →
  extend_trees nt blk 0 sz (strs σ) = strs σ' →
  scs σ = scs σ' →
  state_wf σ →
  blk = fresh_block (shp σ) →
  l.1 = blk →
  0 ≤ l.2 < sz →
  loc_controlled Mcall l nt tk_local ☠%S σ'.
Proof.
  intros Heq_shp Hnewtrees Heq_scs Hwf Hblk Hblk2 Hsz _.
  subst blk. destruct l as [blk off]. pose (blk, off) as l. simpl in *. subst blk.
  assert (shp σ' !! l = Some ☠%S) as Hheap.
  { rewrite -Heq_shp /=. eapply init_mem_lookup_fresh_poison. lia. }
  split; last done.
  epose proof (init_perms_lookup Active 0 sz off) as H.
  eexists _, _. rewrite /bor_state_own_on. split_and!.
  2: rewrite -Hnewtrees /= /extend_trees lookup_insert //.
  - by eapply tree_lookup_init_tree.
  - rewrite /item_lookup /=. destruct (init_perms _ _ _ !! off). 2: lia.
    destruct H as [-> _]. done.
  - rewrite /item_lookup /=. destruct (init_perms _ _ _ !! off). 2: lia.
    destruct H as [-> _]. done.
  - done.
  - intros ? t' (Ht'&_). cbv in Ht'. tauto.
Qed.

Lemma bor_state_own_enables_read b range Mcall σ blk tk tg :
  state_wf σ →
  (∀ l, range'_contains range l → bor_state_own Mcall (blk, l) tg tk σ) →
  range.2 ≠ 0%nat →
  trees_contain tg σ.(strs) blk ∧
  ∃ trs', apply_within_trees (memory_access_maybe_nonchildren_only b AccessRead σ.(scs) tg range) blk σ.(strs) = Some trs'.
Proof.
  intros Hwf Hhl Hnn.
  assert (∃ tr, σ.(strs) !! blk = Some tr ∧ tree_contains tg tr) as (tr&Htr&Hcont).
  { ospecialize (Hhl range.1 _).
    1: rewrite /range'_contains; lia.
    destruct Hhl as (it&tr&Hit&Htr&_). eexists. split; first done. eapply Hit. }
  split.
  1: rewrite /trees_contain /trees_at_block Htr //.
  rewrite /apply_within_trees Htr /=. eapply is_Some_ignore_bind.
  rewrite /memory_access_maybe_nonchildren_only. eapply apply_access_success_condition.
  eapply every_node_eqv_universal.
  intros it Hitin%exists_node_to_tree_lookup.
  2: eapply Hwf, Htr.
  rewrite /item_apply_access /permissions_apply_range'. eapply is_Some_ignore_bind.
  eapply mem_apply_range'_success_condition. intros off Hinrange.
  specialize (Hhl off Hinrange) as Hown.
  destruct Hown as (it_tg&tr'&Hittg&Htr'&Hinit&Htk). simpl in *.
  assert (tr = tr') as <- by congruence.
  edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq]; erewrite Heq; clear Heq.
  2: done.
  rewrite rel_dec_flip2.
  assert (tg = itag it → rel_dec tr (itag it) tg = Child This) as Hlocalfalse.
  { intros ->. by rewrite rel_dec_refl. }
  rewrite /apply_access_perm /apply_access_perm_inner.
  change (default _ _) with (item_lookup it off).
  destruct (rel_dec tr (itag it) tg) as [[]|[]] eqn:Hreldec.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) ≠ Disabled) as Hndis.
    { destruct tk; destruct Htk as (Hsame&Hothers). 3: destruct Hothers as (_&Hothers).
      all: specialize (Hothers it _ Hitin). 3: exfalso; by ospecialize (Hlocalfalse _).
      all: rewrite Hreldec // in Hothers. }
    destruct (item_lookup it off) as [ii [| | |]]; try done.
    all: rewrite /= most_init_comm /= if_both_sides_same /= //.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) ≠ Active) as Hnact.
    { destruct tk; destruct Htk as (Hsame&Hothers). 3: destruct Hothers as (_&Hothers).
      all: specialize (Hothers it _ Hitin). 3: exfalso; by ospecialize (Hlocalfalse _).
      all: rewrite Hreldec //= in Hothers.
      intros Hactive. rewrite Hactive in Hothers.
      destruct Hothers as [Hlazy|[]].
      opose proof (state_wf_tree_compat _ Hwf _ _ Htr) as Hnlazy.
      eapply every_node_eqv_universal in Hnlazy.
      2: { eapply tree_lookup_to_exists_node. exact Hitin. }
      rewrite /item_lookup /= in Hactive,Hlazy.
      destruct (iperm it !! off) as [pp|] eqn:Heq; simpl in *.
      - opose proof (item_perms_valid _ _ _ Hnlazy) as Hforall.
        eapply map_Forall_lookup_1 in Hforall. 2: exact Heq. eapply Hforall in Hactive. congruence.
      - by eapply item_default_perm_valid in Hactive. }
    destruct (item_lookup it off) as [ii [im []| | |]] eqn:Heq; simpl.
    1,2,4: destruct ii, bool_decide; simpl in *; done.
    1: done.
    destruct ii, bool_decide eqn:Hprot. all: simpl; try done.
    opose proof (state_wf_tree_not_disabled _ Hwf _ _ Htr (itag it)) as Hndis.
    eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
    2: by eapply Hwf. 2,4: eapply Hwf; first done; eapply Hitin. 2: eapply Hitin. 2: by left.
    eapply every_node_eqv_universal in Hndis.
    2: { eapply tree_lookup_to_exists_node. exact Hitin. }
    eapply bool_decide_eq_true_1 in Hprot.
    ospecialize (Hndis _ off _ _ _).
    1: done. 1,3: by rewrite Heq. 1: done. done.
  - simpl. rewrite /apply_access_perm /apply_access_perm_inner.
    assert (perm (item_lookup it off) ≠ Active) as Hnact.
    { destruct tk; destruct Htk as (Hsame&Hothers). 3: destruct Hothers as (_&Hothers).
      all: specialize (Hothers it _ Hitin) as Ho2. 3: exfalso; by ospecialize (Hlocalfalse _).
      all: rewrite Hreldec //= in Ho2.
      clear Ho2. rewrite /rel_dec in Hreldec.
      destruct (decide (ParentChildIn _ _ tr)) as [HPC|]; last done.
      destruct (decide (ParentChildIn _ _ tr)) as [|HnPC]; first done. clear Hreldec.
      destruct HPC as [?|HSPC]. 1: exfalso; eapply HnPC; by left.
      eapply immediate_sandwich in HSPC as HIPC.
      2: by eapply Hwf. 2: eapply Hwf; first done; eapply Hittg.
      destruct HIPC as (tsw&HIPC&HPC).
      assert (tree_contains tsw tr) as Htswin1.
      { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild. eapply Hittg. }
      assert (tree_unique tsw tr) as Htswin2 by by eapply Hwf.
      eapply unique_implies_lookup in Htswin2 as (itsw&Hitsw).
      specialize (Hothers _ _ Hitsw).
      rewrite /rel_dec decide_True in Hothers.
      2: right; by eapply Immediate_is_StrictParentChild.
      rewrite decide_False in Hothers.
      2: { intros Hc. eapply immediate_parent_not_child. 3: done. 3: done. all: eapply Hwf; first done. 2: done. 1: eapply Hittg. }
      rewrite decide_True // in Hothers.
      intros Hactive.
      opose proof (state_wf_tree_more_active _ Hwf _ _ Htr tsw) as Hndis.
      eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
      2: by eapply Hwf. 2,4: eapply Hwf; first done. 2: done. 2: eapply Hitin. 2: eapply Hitsw. 2: done.
      eapply every_node_eqv_universal in Hndis.
      2: { eapply tree_lookup_to_exists_node. exact Hitin. }
      ospecialize (Hndis _ off _). 1,2: done. by rewrite /= Hndis in Hothers. }
    destruct (item_lookup it off) as [ii [im []| | |]] eqn:Heq; simpl.
    1,2,4: destruct ii, bool_decide; simpl in *; done.
    1: done.
    destruct ii, bool_decide eqn:Hprot. all: simpl; try done.
    opose proof (state_wf_tree_not_disabled _ Hwf _ _ Htr (itag it)) as Hndis.
    eapply every_child_ParentChildIn with (tg' := itag it) in Hndis.
    2: by eapply Hwf. 2,4: eapply Hwf; first done; eapply Hitin. 2: eapply Hitin. 2: by left.
    eapply every_node_eqv_universal in Hndis.
    2: { eapply tree_lookup_to_exists_node. exact Hitin. }
    eapply bool_decide_eq_true_1 in Hprot.
    ospecialize (Hndis _ off _ _ _).
    1: done. 1,3: by rewrite Heq. 1: done. done.
  - rewrite /rel_dec in Hreldec.
    do 2 (edestruct (decide (ParentChildIn _ _ _)); try done).
    assert (tg = itag it) as ->.
    { eapply mutual_parent_child_implies_equal. 3,4: done. 2: eapply Hittg. 1: eapply Hitin. }
    assert (it = it_tg) as <-.
    { eapply tree_lookup_unique; done. }
    rewrite /apply_access_perm /apply_access_perm_inner /=.
    assert (perm (item_lookup it off) ≠ Disabled) as Hndis.
    { destruct tk; destruct Htk as (Hsame&_).
      1, 3: by rewrite Hsame.
      intros Hdis. rewrite !Hdis in Hsame.
      eapply Hsame. by intros [=]. }
    destruct (item_lookup it off) as [ii [| | |]]; try done.
    all: rewrite /= most_init_comm /= if_both_sides_same /= //.
Qed.

Lemma asymmetric_read_prot_pre_from_bor_state_own Mcall σ blk tr acc_tg range it tk :
  state_wf σ →
  σ.(strs) !! blk = Some tr →
  tree_lookup tr acc_tg it →
  (∀ off, range'_contains range off → bor_state_own_on Mcall (blk, off) acc_tg tk σ it tr) →
  tree_equal_asymmetric_read_pre_protected tr range it acc_tg (match tk with tk_pub => false | _ => true end).
Proof.
  intros Hwf Htr Hit Hhl.
  intros off Hoff. specialize (Hhl off Hoff) as (Hini&Hhl).
  simpl. rewrite Hini. split; first done.
  assert (∀ tg' it' pp, tree_lookup tr tg' it' → rel_dec tr tg' acc_tg = Foreign (Parent pp) → initialized (item_lookup it' off) = PermInit) as Hinit.
  { intros tg' it' pp H1 H2. opose proof (state_wf_tree_more_init _ Hwf _ _ Htr tg') as Hpmi.
    rewrite /rel_dec in H2. destruct decide as [HP1|HnP1]; first done. destruct decide as [HP2|HnP2]; last done.
    eapply every_child_ParentChildIn in Hpmi.
    2,3: eapply Hwf; try done. 2,3: eapply H1. 2: eapply Hwf; try done; eapply Hit. 2: done.
    eapply tree_lookup_correct_tag in Hit as Htg; subst acc_tg.
    eapply every_node_eqv_universal in Hpmi.
    2: eapply tree_lookup_to_exists_node, Hit. eapply Hpmi. 1: done. done. }
  destruct tk as [|uk|].
  - destruct Hhl as (Hfrz&Hothers).
    rewrite Hfrz. split; first done.
    intros tg' it' Hit'. specialize (Hothers _ _ Hit'). specialize (Hinit tg' it').
    destruct (rel_dec tr tg' acc_tg) as [[]|[]]; (split; [|split; [done|intros ? [=]]]).
    + split; last done. by eapply Hinit.
    + done.
    + done.
    + done.
    + done.
  - destruct Hhl as (Hnd&Hothers).
    split. { intros Hdis. rewrite /= Hdis in Hnd. by eapply Hnd. }
    intros tg' it' Hit'. specialize (Hothers _ _ Hit'). specialize (Hinit tg' it').
    destruct (rel_dec tr tg' acc_tg) as [[]|[[]|]]; (split; [|intros [=]]).
    + split; last done. by eapply Hinit.
    + intros Hactive. rewrite /= Hactive in Hothers.
      destruct Hothers as [Hothers|[]].
      opose proof (state_wf_tree_compat _ Hwf _ _ Htr) as Hda.
      eapply tree_lookup_correct_tag in Hit' as Htg'; subst tg'.
      eapply every_node_eqv_universal in Hda.
      2: eapply tree_lookup_to_exists_node, Hit'.
      rewrite /item_lookup in Hactive,Hothers. destruct (iperm it' !! off) as [lp|] eqn:Heq; simpl in *.
      * opose proof (item_perms_valid _ _ _ Hda) as Hpwf. eapply map_Forall_lookup_1 in Hpwf. 2: exact Heq.
        rewrite Hpwf // in Hothers.
      * eapply item_default_perm_valid. 1: exact Hda. done.
    + done.
    + done.
    + done.
    + done.
  - destruct Hhl as (Hact&Hnoprot&Hothers).
    rewrite Hact. split; first done.
    intros tg' it' Hit'. specialize (Hothers _ _ Hit'). subst tg'.
    rewrite rel_dec_refl. done.
Qed.

Definition filter_unq_weak lp := match lp with 
    Deallocable => Deallocable
  | EnsuringAccess Strongly => EnsuringAccess Strongly
  | EnsuringAccess WeaklyNoChildren => Deallocable end.

Lemma loc_controlled_filter_unq_weak Mcall c t M L l tg_lu tk sc σ:
  Mcall !! c = Some M → M !! t = Some L →
  loc_controlled Mcall l tg_lu tk sc σ →
  loc_controlled (<[ c := <[ t := filter_unq_weak <$> L ]> M ]> Mcall) l tg_lu tk sc σ.
Proof.
  intros HM HL H1 Hpre. destruct (H1 Hpre) as (Hown&Hhp). split; last done.
  destruct Hown as (it&tr&Hit&Htr&Hinit&Hown).
  exists it, tr. do 3 (split; first done).
  destruct tk; simpl. 1,3: done. destruct Hown as (Hself&Hothers).
  split. 2: done.
  intros Hfrz. specialize (Hself Hfrz).
  do 2 (case_match; try done).
  destruct Hself as (Hs1&Hs2&Hs3). split_and!. 1-2: done.
  destruct Hs3 as (lp&pp&Hpp&(M'&HM'&L'&HL'&Hlp)&Hstrong).
  destruct (decide (call pp = c)) as [<-|Hnecc].
  2: { exists lp, pp. split; first done. split; last done.
       exists M'. rewrite lookup_insert_ne. 2: done. repeat first [split; first done | eexists | done]. }
  assert (M = M') as -> by congruence.
  destruct (decide (tg_lu = t)) as [<-|Hnet].
  2: { exists lp, pp. split_and!; try done.
       eexists. rewrite lookup_insert. split; first done. exists L'. rewrite lookup_insert_ne; done. }
  assert (L = L') as -> by congruence.
  exists (filter_unq_weak lp), pp. split; first done. split.
  - eexists. rewrite lookup_insert. split; first done.
    eexists. rewrite lookup_insert. split; first done.
    rewrite lookup_fmap Hlp /=. done.
  - intros Hstr. specialize (Hstrong Hstr). subst lp. simpl. done.
Qed.






