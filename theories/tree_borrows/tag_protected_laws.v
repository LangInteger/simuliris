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

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_access_strong tg_acc tg_prs l C c trs trs' acc blk off sz b :
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs  l tg_prs ProtStrong →
  tag_protected_for c trs' l tg_prs ProtStrong.
Proof.
  intros Hwf Hwithin Hcall (it & Hlu & Hprot & Hstrong & Hinit).
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - eapply apply_trees_access_lookup_general in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done. rewrite /item_protected_for -Heqprot.
    do 2 (split; first done).
    intros Hperminit.
    assert (protector_is_active (iprot itnew) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
    2: { erewrite Heq in Hacc. injection Hacc as Hacc. rewrite -Hacc.
         eapply Hinit. rewrite Hacc. done. }
    rewrite Heq in Hacc.
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite -Heqperm /= in Hperminit |- *.
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    rewrite /apply_access_perm_inner in Hacc.
    destruct (initialized (item_lookup it l.2));
      [ specialize (Hinit eq_refl) | injection Htrigger as -> ].
    all: destruct trees_rel_dec eqn:Hreldec; destruct acc; destruct (perm (item_lookup it l.2)) as [[] []| | |] eqn:Hpermold; simplify_eq; try done;
         repeat (simplify_eq; try done; (try simpl in Htrigger); simplify_eq; try done).
  - eapply apply_trees_access_lookup_outside in Hlu as (itnew & Hlunew & Heqinit & Heqprot & Hacc); [|done..].
    exists itnew. split; first done. rewrite /item_protected_for -Heqprot.
    do 2 (split; first done).
    by rewrite -Hacc.
Qed.
Lemma tag_protected_preserved_by_access_weak tg_acc tg_prs l C c trs trs' acc blk off sz b :
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs  l tg_prs ProtWeak →
  tag_protected_for c trs' l tg_prs ProtWeak.
Proof.
  intros Hwf Hwithin Hcall Hold it Hlu.
  destruct (decide (l.1 = blk ∧ (off ≤ l.2 < off + sz))%Z) as [(<- & Hin)|Hout].
  - eapply apply_trees_access_lookup_general_rev in Hlu as (itold & Hluold & Heqinit & Heqprot & Hacc); [|done..].
    specialize (Hold itold Hluold) as (Hprot & Hstrong & Hinit).
    rewrite /item_protected_for -Heqprot.
    do 2 (split; first done).
    intros Hperminit.
    assert (protector_is_active (iprot it) C) as Hactive.
    { exists c. rewrite -Heqprot. done. }
    edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
    2: { erewrite Heq in Hacc. injection Hacc as Hacc. rewrite -Hacc.
         eapply Hinit. rewrite Hacc. done. }
    rewrite Heq in Hacc.
    apply bind_Some in Hacc as (perm1 & Hacc & (perm2 & Htrigger & [= Heqperm])%bind_Some).
    rewrite -Heqperm /= in Hperminit |- *.
    rewrite (bool_decide_eq_true_2 _ Hactive) /= in Hacc, Htrigger.
    intros ->.
    destruct (initialized (item_lookup itold l.2)) eqn:Holdinit.
    1: by destruct perm1.
    injection Htrigger as ->.
    rewrite /= /most_init in Heqperm Hperminit.
    rewrite /apply_access_perm_inner in Hacc.
    destruct trees_rel_dec eqn:Hreldec; first done.
    destruct (perm (item_lookup itold l.2)) as [[][]| | |], acc;  done.
  - eapply apply_trees_access_lookup_outside_rev in Hlu as (itold & Hluold & Heqinit & Heqprot & Hacc); [|done..].
    specialize (Hold itold Hluold) as (Hprot & Hstrong & Hinit).
    rewrite /item_protected_for -Heqprot.
    do 2 (split; first done).
    by rewrite -Hacc.
Qed.
Lemma tag_protected_preserved_by_access tg_acc tg_prs l C c trs trs' acc blk off sz b ps:
  wf_trees trs →
  apply_within_trees (memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs  l tg_prs ps →
  tag_protected_for c trs' l tg_prs ps.
Proof.
  destruct ps.
  - eapply tag_protected_preserved_by_access_strong.
  - eapply tag_protected_preserved_by_access_weak.
Qed.

(* TODO move somewhere else *)
Lemma tag_protected_preserved_by_delete tg_acc tg_prs l C c trs trs' blk off sz ps :
  wf_trees trs →
  apply_within_trees (memory_deallocate C tg_acc (off, sz)) blk trs = Some trs' →
  call_is_active c C →
  tag_protected_for c trs l tg_prs ps →
  tag_protected_for c (delete blk trs') l tg_prs ps.
Proof.
  intros Hwf Hwithin Hcall Hpreprot.
  rewrite apply_within_trees_bind in Hwithin.
  pose proof Hwithin as (postread&Hread&Hdealloc)%bind_Some.
  eapply tag_protected_preserved_by_access in Hread as HH. 2-4: done.
  destruct (decide (l.1 = blk)) as [<-|Hout], ps.
  - exfalso. destruct HH as (it & (tr & Htr & Hlu) & Hprot & Hstrong & Hinit).
    rewrite /apply_within_trees Htr /= in Hdealloc.
    pose proof Hdealloc as (okcheck&Hcheck%mk_is_Some&[= <-])%bind_Some. clear Hdealloc.
    rewrite join_success_condition every_node_map every_node_eqv_universal /= in Hcheck.
    pose proof (tree_lookup_correct_tag Hlu) as <-.
    ospecialize (Hcheck it _); first by eapply tree_lookup_to_exists_node.
    eapply is_Some_if_neg in Hcheck. ospecialize (Hstrong _); first done.
    rewrite (bool_decide_eq_true_2 _ Hstrong) /=bool_decide_eq_false in Hcheck.
    eapply Hcheck.
    exists c. done.
  - clear HH. intros it (tr&Htr&Hit). by rewrite lookup_delete in Htr.
  - destruct HH as (it & (tr & Htr & Hlu) & Hprot & Hstrong & Hinit).
    exists it. split; last done. exists tr. split; last done.
    rewrite lookup_delete_ne //.
    pose proof Hdealloc as (?&_&(?&_&[= <-])%bind_Some)%bind_Some.
    by rewrite lookup_insert_ne.
  - intros it (tr&(Hne&Hin)%lookup_delete_Some&Hit).
    eapply HH. exists tr. split; last done.
    eapply bind_Some in Hdealloc as (tr1&Htr1&(tr2&Htr2&[= Heq])%bind_Some).
    rewrite -Heq lookup_insert_ne // in Hin.
Qed.





Definition tag_protected_for_tree c tr off t (ps : prot_strong) := match ps with
    ProtStrong => ∃ it, tree_lookup tr t it ∧ item_protected_for c it off ps
  | ProtWeak   => ∀ it, tree_lookup tr t it → item_protected_for c it off ps end.

Lemma tag_protected_for_tree_spec trs tr blk c off t ps :
  trs !! blk = Some tr →
  tag_protected_for_tree c tr off t ps ↔ tag_protected_for c trs (blk, off) t ps.
Proof.
  intros H.
  destruct ps; split.
  - intros (it&H1&HH). exists it. split; last done. eexists. simpl. done.
  - intros (it&(tr'&H1&H2)&HH). exists it; split; last done. rewrite /= H in H1. by injection H1 as ->.
  - intros HH it (tr'&Htr&Hit). eapply HH. rewrite /= H in Htr. congruence.
  - intros HH it Hit. eapply HH. exists tr. simpl. done.
Qed.

Lemma tag_protected_preserved_by_access_tree tg_acc tg_prs loff C c tr tr' acc off sz b ps :
  wf_tree tr →
  memory_access_maybe_nonchildren_only b acc C tg_acc (off, sz) tr = Some tr' →
  call_is_active c C →
  tag_protected_for_tree c tr loff tg_prs ps →
  tag_protected_for_tree c tr' loff tg_prs ps.
Proof.
  intros H1 H2 H3 H4.
  eapply wf_tree_wf_singleton in H1.
  eassert ({[1%positive := tr]} !! _ = Some tr) as Hlu by eapply lookup_singleton.
  eassert ({[1%positive := tr']} !! _ = Some tr') as Hlu' by eapply lookup_singleton.
  setoid_rewrite tag_protected_for_tree_spec; last done.
  eapply tag_protected_preserved_by_access. 1: done. 2: done.
  - rewrite /apply_within_trees /=. setoid_rewrite Hlu. rewrite /=. erewrite H2.
    rewrite /= insert_singleton //.
  - eapply tag_protected_for_tree_spec; done.
Qed.

Lemma tree_read_many_preserve_tag_protected_for_2 C tg_acc (L : list Z) tr1 trL c offp tg_prs ps
  (Hwf1 : wf_tree tr1) :
  call_is_active c C →
  let fn := (λ L tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg_acc (l, 1%nat)) (Some tr) L) in
  fn L tr1 = Some trL →
  tag_protected_for_tree c tr1 offp tg_prs ps →
  tag_protected_for_tree c trL offp tg_prs ps.
Proof.
  intros Hact fn.
  induction L as [|off L IH] in trL|-*; simpl.
  { intros [= ->]. done. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply Hoff. }
  intros Hprot. eapply tag_protected_preserved_by_access_tree.
  3: exact Hact. 2: exact HL. 1: done.
  by eapply IH.
Qed.

Lemma tree_read_many_preserve_tag_protected_for_1 C (L : list (tag * gset Z)) tr1 trL c offp tg_prs ps
  (Hwf1 : wf_tree tr1) :
  call_is_active c C →
  let fn := (λ E tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr1) (elements L)) (Some tr) E) in
  fn L tr1 = Some trL →
  tag_protected_for_tree c tr1 offp tg_prs ps →
  tag_protected_for_tree c trL offp tg_prs ps.
Proof.
  intros Hact fn.
  induction L as [|(tg_acc&S) L IH] in trL|-*; simpl.
  { intros [= ->]. done. }
  intros (tr2&Hoff&HL)%bind_Some.
  specialize (IH _ Hoff).
  assert (wf_tree tr2) as Hwf2.
  { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_1. 1: exact Hwf1. 1: apply Hoff. }
  intros Hprot. eapply tree_read_many_preserve_tag_protected_for_2.
  2: exact Hact. 2: exact HL. 1: done.
  by eapply IH.
Qed.

Lemma tree_read_many_preserve_tag_protected_for C cid tr1 trL c offp tg_prs ps
  (Hwf1 : wf_tree tr1) :
  call_is_active c C →
  tree_read_all_protected_initialized C cid tr1 = Some trL →
  tag_protected_for_tree c tr1 offp tg_prs ps →
  tag_protected_for_tree c trL offp tg_prs ps.
Proof.
  rewrite /tree_read_all_protected_initialized.
  rewrite /set_fold /=. eapply tree_read_many_preserve_tag_protected_for_1. done.
Qed.

Lemma trees_read_many_preserve_tag_protected_for C cid trs1 trsL c l tg_prs ps
  (Hwf1 : wf_trees trs1) :
  call_is_active c C →
  trees_read_all_protected_initialized C cid trs1 = Some trsL →
  tag_protected_for c trs1 l tg_prs ps →
  tag_protected_for c trsL l tg_prs ps.
Proof.
  intros H1 H2 H3. destruct l as [blk offl], ps.
  - assert (∃ tr, trs1 !! blk = Some tr) as (tr&Htr).
    { destruct H3 as (x&(tr&Htr&_)&_). by eexists. }
    eapply trees_read_all_protected_initialized_pointwise_1 in H2 as (H2&_).
    specialize (H2 _ Htr) as (tr'&Htr'&Hread).
    eapply tag_protected_for_tree_spec. 1: done.
    eapply tree_read_many_preserve_tag_protected_for. 1: by eapply Hwf1. 1: done. 1: done.
    eapply tag_protected_for_tree_spec. all: done.
  - intros itL (trL&HtrL&HitL). simpl in HtrL.
    assert (∃ tr, trs1 !! blk = Some tr) as (tr&Htr).
    { eapply trees_read_all_protected_initialized_pointwise_1 in H2 as (_&H2B).
      destruct (trs1 !! blk) eqn:Heq; first by eexists.
      specialize (H2B Heq). congruence. }
    eapply trees_read_all_protected_initialized_pointwise_1 in H2 as (H2&_).
    specialize (H2 _ Htr) as (tr'&Htr'&Hread). assert (trL = tr') as -> by congruence. simpl.
    eapply tree_read_many_preserve_tag_protected_for in Hread; first last. 3: by eapply Hwf1. 2: done.
    1: by eapply tag_protected_for_tree_spec.
    eapply Hread. done.
Qed.

Lemma call_set_interp_remove c M σ σ' :
  snc σ = snc σ' →
  snp σ = snp σ' →
  scs σ ∖ {[c]} = scs σ' →
  shp σ = shp σ' →
  state_wf σ →
  trees_read_all_protected_initialized (scs σ) c (strs σ) = Some (strs σ') →
  call_set_interp M σ →
  call_set_interp (delete c M) σ'.
Proof.
  intros Heq1 Heq2 Heq3 Heq4 Heq5 Hwf Hinterp c' M' Hsome. destruct (decide (c' = c)) as [-> | Hneq].
  { rewrite lookup_delete in Hsome. done. }
  rewrite lookup_delete_ne in Hsome; last done.
  apply Hinterp in Hsome as (Hin & Hpid).
  split.
  { rewrite -Heq3. set_solver. }
  intros t S HS.
  apply Hpid in HS as (Ht & Hlookup). split; first by rewrite -Heq2.
  intros l b Hl.
  eapply trees_read_many_preserve_tag_protected_for.
  3: done. 3: by eapply Hlookup. 1: by eapply state_wf_tree_unq.
  by eapply Hin.
Qed.