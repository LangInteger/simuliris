(** Abstraction layer for trees.
    The goal of this file is that lemmas that appear here expose as few internal details
    as possible. In particular they should all refer to [trees] in their signature (NOT [tree]). *)
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs class_instances.
From simuliris.tree_borrows Require Import steps_progress steps_retag steps_inv.
From simuliris.tree_borrows Require Import logical_state inv_accessors.
From iris.prelude Require Import options.

(***** not part of the API *****)
Lemma trees_at_block_projection trs tr blk P :
  trees_at_block P trs blk ->
  trs !! blk = Some tr ->
  P tr.
Proof.
  rewrite /trees_contain /trees_at_block.
  destruct (trs !! blk); [|tauto].
  intros Ex Eq. injection Eq; intros; subst. assumption.
Qed.
(***** not part of the API *****)

Lemma trees_contain_trees_lookup_1 trs blk tg :
  wf_trees trs →
  trees_contain tg trs blk → ∃ it, trees_lookup trs blk tg it.
Proof.
  intros (wf&_).
  rewrite /trees_contain /trees_lookup /trees_at_block.
  specialize (wf blk).
  destruct (trs !! blk) as [tr|]; [|tauto].
  intros Ex.
  specialize (wf tr ltac:(reflexivity) tg Ex) as Unq.
  destruct (unique_lookup _ _ Unq) as (it & Det).
  exists it, tr. done.
Qed.

Lemma trees_contain_trees_lookup_2 it trs blk tg :
  trees_lookup trs blk tg it → trees_contain tg trs blk.
Proof.
  rewrite /trees_lookup /trees_contain /trees_at_block.
  destruct (trs !! blk); [|intro H; destruct H as [?[??]]; discriminate].
  intro H. destruct H as [?[Eqt Lookup]].
  injection Eqt; intros; subst.
  apply Lookup.
Qed.

Definition trees_rel_dec (trs : trees) blk tg tg' :=
  match trs !! blk with
  | None => Child This
  | Some tr => rel_dec tr tg tg'
  end.

Lemma trees_rel_dec_refl trs blk tg :
  trees_rel_dec trs blk tg tg = Child This.
Proof.
  rewrite /trees_rel_dec.
  destruct (trs !! blk); [|reflexivity].
  rewrite /rel_dec.
  rewrite decide_True; [|left; reflexivity].
  rewrite decide_True; [|left; reflexivity].
  reflexivity.
Qed.

Lemma trees_equal_allows_same_access C tr1 tr2 blk kind acc_tg range :
  (* _even_ nicer preconditions would be nice, but these are already somewhat eeh "optimistic" *)
  trees_equal C tr1 tr2 →
  wf_trees tr1 →
  wf_trees tr2 →
  is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr1) → 
  is_Some (apply_within_trees (memory_access kind C acc_tg range) blk tr2).
Admitted.

Lemma wf_tree_tree_unique tr :
  wf_tree tr →
  ∀ tg,
  tree_contains tg tr →
  tree_unique tg tr.
Proof.
  intros Hwf tg Hcont.
  by apply (Hwf tg Hcont).
Qed.

Lemma trees_equal_preserved_by_access
  {C blk tr1 tr2 tr1' tr2' kind acc_tg range}
  :
  wf_trees tr1 →
  wf_trees tr2 →
  trees_equal C tr1 tr2 ->
  trees_contain acc_tg tr1 blk ->
  apply_within_trees (memory_access kind C acc_tg range) blk tr1 = Some tr1' ->
  apply_within_trees (memory_access kind C acc_tg range) blk tr2 = Some tr2' ->
  trees_equal C tr1' tr2'.
Proof.
  intros (Hwf1&_) (Hwf2&_) Heq Hcont.
  intros ((tr1blk & tr1blk' & Hlutr1 & Hlutr1' & Hacc1) & Htr1nblk)%apply_within_trees_lookup.
  intros ((tr2blk & tr2blk' & Hlutr2 & Hlutr2' & Hacc2) & Htr2nblk)%apply_within_trees_lookup.
  intros blk'. destruct (decide (blk = blk')) as [<- | Hne];
    last rewrite -Htr1nblk // -Htr2nblk //.
  rewrite Hlutr1' Hlutr2'. econstructor.
  specialize (Heq blk).
  rewrite Hlutr1 Hlutr2 in Heq.
  inversion Heq as [x1 x2 Heq1|]; subst x1 x2. (* yikes *)
  eapply tree_equal_preserved_by_access.
  3, 5, 6: done.
  3: rewrite /trees_contain /trees_at_block Hlutr1 // in Hcont.
  all: eapply wf_tree_tree_unique; 
    (match goal with [ H : each_tree_wf _ |- _] => by eapply H end).
Qed.

Lemma apply_trees_access_lookup_general offi cids trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs blk lu_tg itold →
  ∃       itnew, trees_lookup trs' blk lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App (wf&_) InBounds Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [it' [itAcc [Ex' Det']]].
  exists it'.
  split; [|split; [|split]].
  - exists tr'. split; [apply lookup_insert|]. split; assumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - eapply item_apply_access_preserves_metadata.
    symmetry. eassumption.
  - rewrite /item_apply_access in itAcc.
    symmetry in itAcc. rewrite bind_Some in itAcc.
    destruct itAcc as [perms' [perms'Spec Same]].
    injection Same; intros; subst; clear Same.
    pose proof (mem_apply_range'_spec _ _ offi _ _ perms'Spec) as ThisLocation.
    destruct (decide _); [|unfold range'_contains in *; simpl in *; lia].
    destruct ThisLocation as [perm [permSome permAcc]].
    simpl.
    rewrite /trees_rel_dec trSome.
    assert (itag itold = lu_tg). { eapply tree_determined_specifies_tag; [|eassumption]; assumption. }
    subst.
    rewrite permAcc.
    rewrite /item_lookup /= permSome //=.
Qed.

Lemma apply_trees_access_lookup_outside blki offi cids trs kind blk off1 sz acc_tg lu_tg trs' itold :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs blki lu_tg itold →
  ∃       itnew, trees_lookup trs' blki lu_tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App (wf&_) OutOfBounds Lookup.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  destruct (decide (blk = blki)) as [->|Hne]; last first.
  { destruct Lookup as (it & Hit1 & Hit2). exists itold. split_and!; try done.
    exists it; split; last done.
    by rewrite lookup_insert_ne. }
  assert (tree_contains lu_tg tr) as Ex. {
    eapply trees_at_block_projection; [|eassumption].
    eapply trees_contain_trees_lookup_2.
    eassumption.
  }
  assert (tree_item_determined lu_tg itold tr) as Det. {
    destruct Lookup as [trbis [trsLookup trLookup]].
    assert (trbis = tr) by congruence. subst.
    apply trLookup.
  }
  destruct (apply_access_spec_per_node Ex Det Acc) as [itnew [itAcc [Ex' Det']]].
  rewrite /item_apply_access in itAcc. symmetry in itAcc.
  apply bind_Some in itAcc as (permsnew&Hpermsnew&[= Hitnew]).
  exists itnew. split.
  { exists tr'. split; first by rewrite lookup_insert. done. }
  subst itnew. simpl. split_and!; try done.
  rewrite /item_lookup; simpl. f_equal.
  eapply (mem_apply_range'_spec _ _ offi) in Hpermsnew.
  destruct (decide (range'_contains _ _)) as [Hinrange|_]; last done.
  exfalso. eapply OutOfBounds. split; first done. apply Hinrange.
Qed.


Lemma apply_trees_access_lookup_same_tag cids trs kind blk off1 sz offi tg trs':
  apply_within_trees (memory_access kind cids tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs  →
  off1 ≤ offi < off1 + sz →
  trees_contain tg trs blk →
  ∃ itold itnew, trees_lookup trs blk tg itold ∧ trees_lookup trs' blk tg itnew ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind (Child This) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App wf InRange Ex.
  destruct (trees_contain_trees_lookup_1 _ _ _ wf Ex) as [itold Lookup].
  destruct (apply_trees_access_lookup_general _ _ _ _ _ _ _ _ _ _ _ App wf InRange Lookup) as [itnew newSpec].
  exists itold, itnew.
  rewrite trees_rel_dec_refl in newSpec.
  split; first assumption.
  apply newSpec.
Qed.

Lemma tree_lookup_IsTag tr tg it : tree_lookup tr tg it → IsTag tg it.
Proof.
  intros (H1 & H2).
  eapply exists_node_eqv_existential in H1 as (it2 & Hit2 & Histag).
  eapply every_node_eqv_universal in H2; last done.
  by rewrite -H2.
Qed.

Lemma tree_lookup_unique tr tg it1 it2 : tree_lookup tr tg it1 → tree_lookup tr tg it2 → it1 = it2.
Proof.
  intros Hlu (H1 & H2).
  eapply every_node_eqv_universal in H2; first apply H2.
  1: by eapply tree_lookup_IsTag.
  eapply exists_determined_exists; first done.
  apply Hlu.
Qed.

Lemma apply_trees_access_lookup_general_rev offi cids trs kind blk off1 sz acc_tg lu_tg trs' itnew :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  off1 ≤ offi < off1 + sz →
  trees_lookup trs' blk lu_tg itnew →
  ∃       itold, trees_lookup trs blk lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 apply_access_perm kind (trees_rel_dec trs blk acc_tg lu_tg) (bool_decide (protector_is_active itnew.(iprot) cids)) permold = Some permnew.
Proof.
  intros App WFold InBounds Lookup.
  assert (wf_trees trs') as WFnew.
  { eapply apply_within_trees_wf; try done. eapply memory_access_tag_count. }
  pose proof App as (trold&Htrold&(trnew&Htrnew&[= <-])%bind_Some)%bind_Some.
  destruct Lookup as (tr'&Htr'&Hlookup).
  rewrite lookup_insert in Htr'. injection Htr' as <-.
  pose proof Hlookup as (Hunq&_).
  eapply wf_tree_tree_unique in Hunq; last eapply WFnew, lookup_insert.
  rewrite /tree_unique in Hunq. erewrite <-memory_access_tag_count in Hunq; last done.
  pose proof (unique_exists Hunq) as Hcont.
  apply unique_lookup in Hunq as (itold&Hdet).
  eapply (apply_trees_access_lookup_general offi) in App.
  2: done. 3: by eexists. 2: lia.
  destruct App as (itnew' & (trnew' & Htrnew' & Hitnew') & Hperms).
  assert (trnew' = trnew) as ->.
  { rewrite lookup_insert in Htrnew'. congruence. }
  assert (itnew' = itnew) as -> by by eapply tree_lookup_unique.
  exists itold. split; last done.
  by exists trold.
Qed.

Lemma apply_trees_access_lookup_outside_rev blki offi cids trs kind blk off1 sz acc_tg lu_tg trs' itnew :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk trs = Some trs' →
  wf_trees trs →
  ¬ (blki = blk ∧ off1 ≤ offi < off1 + sz) →
  trees_lookup trs' blki lu_tg itnew →
  ∃       itold, trees_lookup trs blki lu_tg itold ∧
                 let permold := item_lookup itold offi in let permnew := item_lookup itnew offi in
                 initp itold = initp itnew ∧
                 iprot itold = iprot itnew ∧
                 permold = permnew.
Proof.
  intros App wf OutOfBounds Lookup.
  assert (wf_trees trs') as wf'.
  { eapply apply_within_trees_wf; try done.
    intros ????. by eapply memory_access_tag_count. }
  pose proof App as App2.
  rewrite /apply_within_trees in App.
  rewrite bind_Some in App.
  destruct App as [tr [trSome Acc]].
  rewrite bind_Some in Acc.
  destruct Acc as [tr' [Acc Out]].
  injection Out; intros; subst; clear Out.
  destruct (decide (blk = blki)) as [->|Hne]; last first.
  { destruct Lookup as (it & Hit1 & Hit2). exists itnew. split_and!; try done.
    exists it; split; last done.
    by rewrite lookup_insert_ne in Hit1. }
  assert (tree_contains lu_tg tr') as Ex. {
    eapply trees_at_block_projection.
    1: eapply trees_contain_trees_lookup_2; eassumption.
    by eapply lookup_insert.
  }
  assert (tree_item_determined lu_tg itnew tr') as NewDet. {
    destruct Lookup as (? & Heq & Hlu). rewrite lookup_insert in Heq.
    injection Heq as <-. apply Hlu.
  }
  assert (tree_unique lu_tg tr) as UnqPre.
  { eapply wf_tree_tree_unique in Ex. 2: eapply wf', lookup_insert.
    rewrite /tree_unique. erewrite tree_apply_access_same_count.
    1: apply Ex.
    apply Acc. }
  pose proof UnqPre as (itold & Hdetold)%unique_lookup.
  assert (trees_lookup trs blki lu_tg itold) as Hluold.
  { exists tr; split; first done. split; last done. by eapply unique_exists. }
  pose proof Hluold as Hluold2.
  eapply apply_trees_access_lookup_outside in Hluold as (itnew' & Hlu2 & HH2).
  2: apply App2.
  - exists itold; split; first done.
    enough (itnew' = itnew) as <- by eapply HH2.
    eapply (tree_lookup_unique tr' lu_tg).
    + destruct Hlu2 as (? & Hx & Hy).
      rewrite lookup_insert in Hx. congruence.
    + destruct Lookup as (? & Hx & Hy).
      rewrite lookup_insert in Hx. congruence.
  - done.
  - apply OutOfBounds.
Qed.

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_access tg_acc tg_prs l C c trs trs' acc blk off sz :
  wf_trees trs →
  apply_within_trees (memory_access acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs  l tg_prs →
  tag_protected_for c trs' l tg_prs.
Proof.
  intros Hwf Hwithin Hcall (it & Hlu & Hprot & Hinit). 
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - eapply apply_trees_access_lookup_general in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done.
    split; first by rewrite -Heqprot.
    intros Hperminit.
    assert (protector_is_active (iprot itnew) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite -Heqperm /= in Hperminit |- *.
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    rewrite /apply_access_perm_inner in Hacc.
    destruct (initialized (item_lookup it l.2));
      [ specialize (Hinit eq_refl) | injection Htrigger as -> ].
    all: destruct trees_rel_dec eqn:Hreldec; destruct acc; destruct (perm (item_lookup it l.2)) as [[] []| | |] eqn:Hpermold; simplify_eq; try done;
         repeat (simplify_eq; try done; (try simpl in Htrigger); simplify_eq; try done).
  - eapply apply_trees_access_lookup_outside in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done.
    split; first by rewrite -Heqprot.
    by rewrite -Hacc.
Qed.

Lemma loc_controlled_access_outside l tk sc cids σ σ' kind blk off1 sz acc_tg lu_tg :
  apply_within_trees (memory_access kind cids acc_tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  shp σ !! l = shp σ' !! l →
  scs σ = scs σ' →
  state_wf σ →
  ¬ (l.1 = blk ∧ off1 ≤ l.2 < off1 + sz) →
  loc_controlled l lu_tg tk sc σ →
  loc_controlled l lu_tg tk sc σ'.
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
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hsame & Hothers).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
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
      rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - intros (it & Htrlu & Hperm).
    pose proof Htrlu as Htrlu2.
    eapply apply_trees_access_lookup_outside_rev in Htrlu2; [|eapply Happly|eapply Hwf|done].
    destruct Htrlu2 as (itold & Hluold & Heq1 & Heq2 & Heq3).
    destruct Hlc as (Hownold & Hscold).
    + exists itold. split; first done. by rewrite Heq3 Heq2 Heq_scs.
    + split; last by rewrite -Heq_shp.
      destruct Hluold as (trold & Htrold & Hluold). rewrite /bor_state_own /= in Hownold.
      destruct Hownold as (itold2 & trold2 & Hluold2 & Hluold2' & Hstuff).
      assert (trold2 = trold) as -> by congruence.
      assert (itold2 = itold) as -> by by eapply tree_lookup_unique.
      destruct Htrlu as (trnew & Htrnew & Hlunew).
      exists it, trnew. do 2 (split; first done).
      destruct act; destruct Hstuff as (Hsame & Hothers).
      * split; first by rewrite -Heq3 -Heq2 -Heq_scs.
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
        rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
      * split; first rewrite -Heq3 -Heq2 -Heq_scs //.
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
        rewrite Hreldec. destruct HHHH as (Hinit2 & Hprot2 & Hperm2). rewrite -Hperm2. apply Hothers.
  - destruct Hlc as (Hownold & Hscold); first done.
    split; last by rewrite -Heq_shp.
    destruct Hownold as (itold & trold & Hluold & Htrold & Hsame & Hothers).
    assert (trees_lookup σ.(strs) l.1 lu_tg itold) as Hsluold by by exists trold.
    eapply apply_trees_access_lookup_outside in Hsluold; [|eapply Happly|eapply Hwf|done].
    destruct Hsluold as (itnew & (trnew & Htrnew & Hlunew) & (Hinitold & Hprotold & Hpermold)).
    exists itnew, trnew. do 2 (split; first done).
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

Lemma loc_controlled_write_becomes_active l sc cids σ σ' blk off1 sz tg vls scold tkkold:
  apply_within_trees (memory_access AccessWrite cids tg (off1, sz)) blk σ.(strs) = Some σ'.(strs) →
  (write_mem (blk, off1) vls (shp σ)) = shp σ' →
  scs σ = scs σ' →
  state_wf σ →
  l.1 = blk →
  length vls = sz →
  list_to_heaplet vls off1 !! l.2 = Some sc →
  loc_controlled l tg (tk_unq tkkold) scold σ →
  loc_controlled l tg (tk_unq tk_act) sc σ'.
Proof.
  intros Happly Heq_shp Heq_scs Hwf Hblk Hsz Hsc Hold Hpre.
  split; last first.
  { rewrite -Heq_shp /=.
    destruct (write_mem_lookup_case (blk, off1) vls (shp σ) l) as [(i&Hil&->&->)|(Hwrong&_)].
    2: { eapply list_to_heaplet_lookup_Some in Hsc. exfalso.
         eapply (Hwrong (Z.to_nat (l.2 - off1))); first lia.
         eapply injective_projections; first done.
         simpl. lia. }
    rewrite list_to_heaplet_nth // in Hsc. }
  assert (wf_trees σ.(strs)) as Hwf_pre by eapply Hwf.
  assert (wf_trees σ'.(strs)) as Hwf_post.
  { eapply apply_within_trees_wf; try done.
    eapply memory_access_tag_count. }
  destruct Hpre as (itnew & (trnew & Htr' & Hlunew) & Hndis & Hiffrozen).
  pose proof Happly as Happlys.
  eapply bind_Some in Happly as (trold & Htrold & (q&Haccess&[= Hstrs])%bind_Some).
  pose proof Htr' as Htrnew.
  rewrite -Hstrs Hblk lookup_insert in Htr'. injection Htr' as ->.
  assert (off1 ≤ l.2 < off1 + sz) as Hinbound.
  { subst sz. by eapply list_to_heaplet_lookup_Some. }
  exists itnew, trnew.
  do 2 (split; first done).
  assert (perm (item_lookup itnew l.2) = Active ∧ bor_state_pre l tg (tk_unq tkkold) σ) as (Hsolv&Hpre2).
  { eapply apply_trees_access_lookup_general_rev in Happlys.
    2: done. 3: { exists trnew; split; try done. by rewrite -Hblk. } 2: eassumption.
    destruct Happlys as (itold & Hluold & _ & _ & Happlys).
    pose (ppn := item_lookup itnew l.2). fold ppn in Happlys|-*.
    pose (ppo := item_lookup itold l.2). fold ppo.
    enough (perm ppn = Active ∧ perm (ppo) ≠ Disabled ∧ (perm ppo = Frozen→ protector_is_active (iprot itold) (scs σ))) as (H1&H2).
    { split; first done. simpl. rewrite /bor_state_pre_unq.
      eexists; split; first by rewrite Hblk. done. }
    rewrite trees_rel_dec_refl /= /apply_access_perm /= /apply_access_perm_inner in Happlys.
    eapply bind_Some in Happlys as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
    rewrite /= in Hperm1,Hperm2|-*.
    subst ppo.
    destruct (perm (item_lookup itold l.2)) as  [[] []| | |], (initialized _) as [];
      repeat (simplify_eq; try done; try simpl in Hperm2; destruct bool_decide).
  }
  split; first by rewrite Hsolv.
  destruct (Hold Hpre2) as ((it'&tr'&Htr'&Hlu'&_&Holdothers)&_).
  assert (tr' = trold) as ->.
  { rewrite Hblk Htrold in Hlu'. congruence. }
  intros itmod tmod Hlumod.
  eapply apply_trees_access_lookup_general_rev in Happlys.
  2: done. 2: eassumption. 2: { exists trnew; split; first by rewrite -Hblk. apply Hlumod. }
  destruct Happlys as (itold & (tr'&Htr''&Hluold) & _ & _ & Hperm).
  assert (tr' = trold) as ->.
  { rewrite Htrold in Htr''. congruence. }
  specialize (Holdothers _ _ Hluold).
  rewrite /trees_rel_dec Htrold /= /apply_access_perm /= /apply_access_perm_inner in Hperm.
  erewrite <-access_same_rel_dec; last done.
  (* TODO looks like the access relation stuff is the wrong way around in logical_state *)
  (* At least, the lemma only works when it's switched there *)
  assert (rel_dec trold tg tmod = rel_dec trold tmod tg) as Hfalse by admit;
  rewrite Hfalse in Hperm; clear Hfalse; rewrite rel_dec_flip2 in Hperm.
  eapply bind_Some in Hperm as (prm&Hperm1&(pv&Hperm2&[= <-])%bind_Some).
  rewrite /= in Hperm1,Hperm2|-*.
  destruct rel_dec as [[]|[]] eqn:Heq, (perm (item_lookup itold l.2)) as [[] []| | |] eqn:Heqp, (initialized _) as [] eqn:Heqi;
    repeat (simpl; try simpl in Hperm1; simplify_eq; try done; try simpl in Hperm2; destruct bool_decide).
Admitted.







