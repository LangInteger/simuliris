(** This file has been adapted from the Stacked Borrows development, available at 
https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.tree_borrows Require Import helpers.
From simuliris.tree_borrows Require Export defs steps_foreach steps_access steps_preserve bor_lemmas.
From iris.prelude Require Import options.

Lemma wf_init_state : state_wf init_state.
Proof.
  constructor; simpl; try (intros ?; set_solver).
  intros blk l Absurd; inversion Absurd as [? H]; inversion H.
Qed.

(** Steps preserve wellformedness *)
Lemma wf_tree_item_mono trs :
  Proper ((≤)%nat==> (≤)%nat ==> impl) (wf_trees trs).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF Hf.
  move => ? /Hf TG1.
  move: TG1. rewrite /item_wf.
  intros [it [Unq [TgLe ProtLe]]].
  exists it; repeat split.
  - assumption.
  - intros tg tgit. specialize (TgLe tg tgit). lia.
  - intros cid protit. specialize (ProtLe cid protit). lia.
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof.
  move => ??? WF ?? tg Access.
  destruct tg as [tg].
  specialize (WF _ _ (Tag tg) Access); simpl in WF.
  lia.
Qed.

Definition preserve_tree_wf (fn:app (tree item)) nxtp nxtp' nxtc nxtc' :=
  forall tr tr', wf_tree tr nxtp nxtc -> fn tr = Some tr' -> wf_tree tr' nxtp' nxtc'.

Definition preserve_tree_nonempty (fn:app (tree item)) :=
  forall tr tr', ~tr = empty -> fn tr = Some tr' -> ~tr' = empty.

(* Any function that operates only on permissions (which is all transitions steps)
   leaves the tag and protector unchanged which means that most of the preservation lemmas
   are trivial once we get to the level of items *)
Definition preserve_item_metadata (fn:app item) :=
  forall it it', fn it = Some it' -> it.(iprot) = it'.(iprot) /\ it.(initp) = it'.(initp) /\ it.(itag) = it'.(itag).

(* Since there are a lot of layers to the model (trees -> tree -> item -> perms)
   that we mostly don't really need to reason about (e.g. tree_item_included is per-item
   and we don't need tree-wide reasoning) we start with some lemmas to turn the per-trees
   wf preservation to per-item wf preservation *)

Lemma apply_within_trees_wf trs trs' nxtp nxtp' nxtc nxtc' blk fn:
  apply_within_trees fn blk trs = Some trs' ->
  (forall tr, wf_tree tr nxtp nxtc -> wf_tree tr nxtp' nxtc') ->
  preserve_tree_wf fn nxtp nxtp' nxtc nxtc' ->
  wf_trees trs nxtp nxtc -> wf_trees trs' nxtp' nxtc'.
Proof.
  intros App WFtrans WFfn WF.
  unfold apply_within_trees in App; destruct (trs !! blk) as [t|] eqn:Lookup; inversion App as [App0]; clear App.
  destruct (fn t) eqn:Map; inversion App0 as [E]; clear App0.
  intro blk'; destruct (decide (blk = blk')); intros tr Lookup'.
  all: inversion E; simplify_eq.
  (* Handle the insertion/deletion *)
  1: rewrite lookup_insert in Lookup'.
  2: rewrite lookup_insert_ne in Lookup'; [|done].
  all: simplify_eq.
  (* WF impl *)
  - apply (WFfn t); [|done]; apply (WF blk' _ Lookup).
  - apply (WFtrans tr); apply (WF blk' _ Lookup').
Qed.

Lemma apply_within_trees_preserve_nonempty trs trs' blk fn :
  wf_non_empty trs ->
  preserve_tree_nonempty fn ->
  apply_within_trees fn blk trs = Some trs' ->
  wf_non_empty trs'.
Proof.
  intros WF Preserve ApplySome blk' tr'' Lookup.
  destruct (apply_within_trees_lookup _ _ _ _ ApplySome) as [LookupEq LookupNeq].
  destruct (decide (blk' = blk)).
  - subst.
    destruct LookupEq as [tr [tr' [Eqtr [Eqtr' Eqtrfn]]]].
    rewrite Eqtr' in Lookup; injection Lookup; intro; subst.
    apply (Preserve tr tr'').
    * apply (WF blk).
      unfold apply_within_trees in ApplySome.
      exact Eqtr.
    * auto.
  - apply (WF blk').
    rewrite LookupNeq; [auto|lia].
Qed.

Lemma apply_within_trees_same_dom trs trs' blk fn :
  apply_within_trees fn blk trs = Some trs' ->
  forall blk', is_Some (trs !! blk') <-> is_Some (trs' !! blk').
Proof.
  unfold apply_within_trees.
  destruct (trs !! blk) as [t|] eqn:Lookup; simpl; [|intro H; inversion H].
  destruct (fn t); simpl; [|intro H; inversion H].
  intro H; injection H; intro; subst.
  intro blk'.
  destruct (decide (blk = blk')) as [e|].
  - rewrite e. rewrite lookup_insert.
    split.
    * intro. econstructor; reflexivity.
    * intro. rewrite <- e; rewrite Lookup; econstructor; reflexivity.
  - rewrite lookup_insert_ne; [|done]. tauto.
Qed.

Lemma extend_trees_wf trs tr blk nxtp nxtc :
  wf_trees trs nxtp nxtc ->
  wf_tree tr nxtp nxtc ->
  wf_trees (<[blk := tr]> trs) nxtp nxtc.
Proof.
  intros WFs WF.
  intros blk' tr'.
  destruct (decide (blk = blk')).
  - simplify_eq; rewrite lookup_insert; intro H; injection H; intro; subst; done.
  - rewrite lookup_insert_ne; [|done]; apply (WFs blk').
Qed.

(* Now we get from per-tree to per-item *)
Lemma tree_joinmap_preserve_prop tr tr' (fn:item -> option item) (P:item -> Prop) :
  (forall it it', fn it = Some it' -> P it -> P it') ->
  every_node P tr ->
  join_nodes (map_nodes fn tr) = Some tr' ->
  every_node P tr'.
Proof.
  intros Preserve All Join.
  pose (proj1 (join_success_condition _) (mk_is_Some _ _ Join)) as AllSome.
  generalize dependent tr'.
  induction tr as [|data ? IHtr1 ? IHtr2]; intros tr' JoinSome AllSome; simpl in *; [injection JoinSome; intros; simplify_eq; auto|].
  destruct AllSome as [[data' Some0] [Some1 Some2]].
  rewrite Some0 in JoinSome; simpl in JoinSome.
  destruct (proj2 (join_success_condition _) Some1) as [tr1' Some1'].
  destruct (proj2 (join_success_condition _) Some2) as [tr2' Some2'].
  rewrite Some1' in JoinSome; rewrite Some2' in JoinSome; simpl in JoinSome.
  injection JoinSome; intros; subst.
  destruct All as [All0 [All1 All2]].
  try repeat split.
  - apply (Preserve data _ Some0 All0).
  - apply (IHtr1 All1); apply Some1'.
  - apply (IHtr2 All2); apply Some2'.
Qed.

Lemma item_apply_access_preserves_metadata kind strong :
  app_preserves_metadata (item_apply_access kind strong).
Proof.
  intros it cids rel range it'.
  unfold item_apply_access.
  destruct (permissions_apply_range' _); simpl; [|intro H; inversion H].
  intro H; injection H; intro; subst; simpl.
  tauto.
Qed.

Lemma joinmap_preserve_nonempty fn :
  preserve_tree_nonempty (fun tr => join_nodes (map_nodes fn tr)).
Proof.
  intro tr; induction tr as [|data ????]; intros tr' Nonempty JoinMap; [contradiction|].
  simpl in JoinMap.
  destruct (fn data); [|inversion JoinMap]; simpl in *.
  destruct (join_nodes _); [|inversion JoinMap]; simpl in *.
  destruct (join_nodes _); [|inversion JoinMap]; simpl in *.
  injection JoinMap; intro; subst.
  intro H; inversion H.
Qed.

Lemma deallocate_preserve_nonempty cids tg range :
  preserve_tree_nonempty (memory_deallocate cids tg range).
Proof.
  intros tr tr' Nonempty Dealloc.
  eapply joinmap_preserve_nonempty.
  1: exact Nonempty.
  apply Dealloc.
Qed.

Lemma memory_read_preserve_nonempty kind strong cids tg range :
  preserve_tree_nonempty (memory_access kind strong cids tg range).
Proof.
  intros tr tr' Nonempty Read.
  eapply joinmap_preserve_nonempty.
  1: exact Nonempty.
  apply Read.
Qed.

Lemma create_child_preserve_nonempty cids oldtg newtg newp :
  preserve_tree_nonempty (create_child cids oldtg newtg newp).
Proof.
  intros tr tr' Nonempty Create.
  unfold create_child in Create.
  injection Create; intros; subst; clear Create.
  (* No need to do an induction, we can prove it's nonempty with just the root *)
  destruct tr as [|data].
  1: contradiction.
  simpl. destruct (decide (IsTag oldtg data)); intro H; inversion H.
Qed.

Lemma tree_apply_access_wf fn tr tr' cids tg range nxtp nxtc :
  app_preserves_metadata fn ->
  wf_tree tr nxtp nxtc ->
  tree_apply_access fn cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  rewrite /wf_tree /tree_item_included.
  intros Preserve WF Access.
  intros tg' Ex'.
  pose proof (proj2 (access_preserves_tags Preserve Access) Ex') as Ex.
  destruct (WF tg' Ex) as  [it [Unqit Wfit]].
  destruct (apply_access_spec_per_node Ex Unqit Preserve Access) as [post [PostSpec [_ Unqpost]]].
  exists post; split; [assumption|].
  rewrite /item_wf in Wfit |- *.
  symmetry in PostSpec.
  destruct (Preserve _ _ _ _ _ PostSpec) as [Same1 [Same2 Same3]].
  simpl. rewrite /IsTag /protector_is_for_call. rewrite <- Same1, <- Same2.
  auto.
Qed.

Lemma deallocate_trees_wf tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  memory_deallocate cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  apply (tree_apply_access_wf _ _ _ _ _ _ _ _ (item_apply_access_preserves_metadata _ _) WF Dealloc).
Qed.

Lemma memory_read_wf tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  memory_access AccessRead ProtStrong cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  apply (tree_apply_access_wf _ _ _ _ _ _ _ _ (item_apply_access_preserves_metadata _ _) WF Dealloc).
Qed.

Lemma memory_write_wf tr tr' cids tg range nxtp nxtc :
  wf_tree tr nxtp nxtc ->
  memory_access AccessWrite ProtStrong cids tg range tr = Some tr' ->
  wf_tree tr' nxtp nxtc.
Proof.
  intros WF Dealloc.
  apply (tree_apply_access_wf _ _ _ _ _ _ _ _ (item_apply_access_preserves_metadata _ _) WF Dealloc).
Qed.

Lemma init_mem_singleton_dom blk blk' n n' sz :
  (blk, n) ∈ dom (init_mem (blk', n') sz ∅) -> blk = blk'.
Proof.
  rewrite elem_of_dom.
  intro Dom.
  destruct (init_mem_lookup_case _ _ _ _ _ (is_Some_proj_extract _ Dom _ ltac:(reflexivity))) as [[Contra ?]|[i [? E]]].
  + inversion Contra.
  + inversion E. reflexivity.
Qed.

Lemma alloc_step_wf (σ σ': state) e e' l bor ptr efs:
  mem_expr_step σ.(shp) e (AllocEvt l bor ptr) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (AllocEvt l bor ptr)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  inversion IS as [x| | | | | | |]; clear IS. destruct x; simpl in *; simplify_eq. constructor; simpl.
  - intros blk l Found.
    apply elem_of_dom; apply elem_of_dom in Found.
    rewrite init_mem_dom in Found; rewrite dom_insert.
    rewrite elem_of_union in Found; rewrite elem_of_union.
    destruct Found as [FoundL|FoundR].
    * right. rewrite elem_of_dom; rewrite elem_of_dom in FoundL. apply (WF.(state_wf_dom _) blk l); simpl; done.
    * left.
      rewrite (init_mem_singleton_dom _ _ _ _ _ FoundR).
      apply elem_of_singleton. reflexivity.
  - apply extend_trees_wf.
    * pose proof (wf_tree_item_mono _ nxtp (S nxtp) ltac:(simpl; eauto) _ _ ltac:(simpl; eauto) (WF.(state_wf_tree_item _))) as WF'.
      simpl in WF'. assumption.
    * unfold wf_tree; unfold tree_item_included.
      intros tg Ex. inversion Ex as [isTag|[Contra|Contra]].
      -- simpl in isTag; inversion isTag as [isRootTag]. simpl in isRootTag. eexists; simpl.
         rewrite /IsTag in isTag |- *; simpl in *. split.
         ** tauto.
         ** rewrite /item_wf. simpl. split.
            ++ intros tg' Tag. inversion Tag. subst. lia.
            ++ intros cid' Prot. inversion Prot.
      -- inversion Contra.
      -- inversion Contra.
  - intros blk.
    destruct (decide (blk = fresh_block h)).
    * simplify_eq.
      intros tr IsSome.
      rewrite /extend_trees in IsSome.
      rewrite lookup_insert in IsSome.
      injection IsSome.
      rewrite /init_tree. intro isbranch. rewrite <- isbranch. auto.
    * intros tr.
      rewrite /extend_trees.
      rewrite lookup_insert_ne.
      + apply WF.(state_wf_non_empty _).
      + congruence.
  - apply (WF.(state_wf_cid_agree _)).
Qed.

(*
(** Dealloc *)
Lemma dealloc_step_wf σ σ' e e' l bor ptr efs :
  mem_expr_step σ.(shp) e (DeallocEvt l bor ptr) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (DeallocEvt l bor ptr)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  inversion IS; clear IS; simplify_eq.
  Check (mk_is_Some _ _ ACC).
  destruct (trees_deallocate_isSome _ _ _ _ _ _ (mk_is_Some _ _ ACC)) as [x [Lookup Update]].
  constructor; simpl.
  - intros blk' l'. rewrite <- (elem_of_dom (free_mem _ _ _) _).
    intro OldDom.
    pose (free_mem_dom _ _ _ _ OldDom) as DomCase. destruct DomCase as [DomH [NeqFi FreeLookup]].
    unfold apply_within_trees in ACC; rewrite Lookup in ACC; simpl in ACC.
    destruct Update as [tr' Lookup']. rewrite Lookup' in ACC; simpl in ACC.
    injection ACC; intros; simplify_eq.
    rewrite <- (elem_of_dom (<[_:=_]>trs) _). rewrite dom_insert; rewrite elem_of_union; right.
    rewrite elem_of_dom.
    eapply (WF.(state_wf_dom _) _); simpl; erewrite <- (elem_of_dom h _); exact DomH.
  - apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply deallocate_trees_wf.
    * apply (WF.(state_wf_tree_item _)).
  - apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (deallocate_preserve_nonempty _ _ _) ACC).
  - apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma mem_app_lookup l lkp vlp h h' val :
  mem_app l lkp vlp h = Some (val, h') ->
  (∀ (i: nat), (i < length vlp)%nat → exists sclp scal pol oldlk newlk,
    vlp !! i = Some sclp
    /\ h !! (l +ₗ i) = Some (oldlk, scal)
    /\ apply_policy sclp scal = pol
    /\ lkp oldlk = Some newlk
    /\ val !! i = Some pol.(sread)
    /\ h' !! (l +ₗ i) = Some (newlk, pol.(swrite)))
  ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vlp)%nat → l' ≠ l +ₗ i) →
    h' !! l' = h !! l').
Proof.
  revert l h h' val. induction vlp as [|sclp vlp IH]; move => l h h' val Success; simpl in *.
  - injection Success; intros; subst.
    split; intros i Hyp.
    * exfalso; destruct i; lia.
    * reflexivity.
  - destruct (h !! l) eqn:Lookup; simpl in Success; [|inversion Success].
    destruct p.
    destruct (lkp l0) eqn:EqLkp; simpl in Success; [|inversion Success].
    destruct (apply_policy _ _) eqn:EqAppLkp.
    destruct (mem_app _ _ _ _) eqn:EqMemApp; simpl in Success; [|inversion Success].
    destruct p.
    injection Success; intros; subst.
    pose (h'' := <[l:=(l1, swrite)]> h).
    specialize IH with (l := l +ₗ 1) (h := h'') (h' := h') (val := v).
    destruct (IH EqMemApp) as [IH' IH'']; clear IH; clear EqMemApp.
    split.
    * intros i Bound.
      destruct i.
      + exists sclp; exists s; exists (apply_policy sclp s); exists l0; exists l1.
        try repeat split; subst; try rewrite EqAppLkp; try rewrite shift_loc_0; simpl; auto.
        rewrite IH''. ++ rewrite lookup_insert; reflexivity. ++ intros i Bound'. rewrite shift_loc_assoc.
        intro Absurd; destruct l; unfold shift_loc in Absurd; simpl in Absurd; injection Absurd; lia.
      + assert ((i < length vlp)%nat) by lia.
        specialize IH' with i.
        destruct IH' as [sclp' [scal [pol [oldlk [newlk [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]]; [done|].
        exists sclp'; exists scal; exists (apply_policy sclp' scal); exists oldlk; exists newlk.
        replace (l +ₗ S i) with (l +ₗ 1 +ₗ i).
        1: try repeat split; subst; simpl; auto.
        1: erewrite <- (lookup_insert_ne h l _ (l1, swrite)); [exact H2|].
        all: destruct l; unfold shift_loc; simpl. ++ intro Loc; injection Loc; lia. ++ f_equal; lia.
    * intros l' Range.
      rewrite IH''.
      1: rewrite (lookup_insert_ne _ _ _ _); [reflexivity|].
      + replace l with (l +ₗ 0); [|unfold shift_loc; destruct l; simpl; f_equal; lia].
        intro H; symmetry in H; move: H. apply (Range (Z.to_nat 0)); lia.
      + intros i Bound'. rewrite shift_loc_assoc.
        replace (l +ₗ (1 + i)) with (l +ₗ (S i)).
        ++ apply Range; lia.
        ++ unfold shift_loc; f_equal; lia.
Qed.

Lemma mem_app_local l lkp vlp h1 h2 val h1' :
  mem_app l lkp vlp h1 = Some (val, h1') ->
  (forall i:nat, (i < length vlp) -> h1 !! (l +ₗ i) = h2 !! (l +ₗ i)) ->
  exists h2', (
    mem_app l lkp vlp h2 = Some (val, h2')
    /\ forall i:nat, (i < length vlp) -> h1' !!  (l +ₗ i) = h2' !! (l +ₗ i)
  ).
Proof.
  revert l h1 h1' h2 val. induction vlp as [|sclp vlp IH]; move => l h1 h1' h2 val Success Coincide.
  - simpl in Success; injection Success; intros; subst.
    exists h2. simpl. split; auto.
  - simpl in *; destruct (h1 !! l) eqn:Lookup; [|inversion Success]; simpl in *.
    rewrite <- (shift_loc_0_nat l); rewrite <- (Coincide O); [|lia]; rewrite (shift_loc_0_nat); rewrite Lookup; simpl.
    destruct p as [lk scal].
    destruct (lkp lk) as [lk'|]; [|inversion Success]; simpl in *.
    destruct (apply_policy _ _).
    destruct (mem_app _ _ _ _) as [[val'' h1'']|] eqn:EqApplied; [|inversion Success]; simpl in *.
    injection Success; intros; subst.
    destruct (IH (l +ₗ 1%nat) (<[l:=(lk',swrite)]> h1) h1' (<[l:=(lk',swrite)]> h2) val'' EqApplied) as [h2' [Success2 Range2]]. {
      intros i Bound. repeat rewrite lookup_insert_ne. {
        rewrite shift_loc_assoc_nat. apply Coincide. lia.
      }
      all: unfold shift_loc; destruct l; simpl; intro H; injection H; lia.
    }
    rewrite Success2; simpl.
    exists h2'.
    split.
    * reflexivity.
    * intros i Bound. destruct i.
      + rewrite shift_loc_0_nat.
        rewrite (proj2 (mem_app_lookup _ _ _ _ _ _ Success2) l); [|intros i _; unfold shift_loc; destruct l; simpl; intro H; injection H; lia].
        rewrite (proj2 (mem_app_lookup _ _ _ _ _ _ EqApplied) l); [|intros i _; unfold shift_loc; destruct l; simpl; intro H; injection H; lia].
        repeat rewrite lookup_insert; reflexivity.
      + specialize Range2 with i. rewrite shift_loc_assoc_nat in Range2. apply Range2; lia.
Qed.

(* mem_app preserves the domain
   The key argument is an extraction of the assignment from (mem_app (l+1) _ (<[l:=v]> h)) to (<[l:=v]> (mem_app (l+1) _ h))
   obtained by noninterference of <[l:=v]> with (mem_app (l+1))
*)
Lemma mem_app_dom l vl lkp vlp h h'
  (DEFINED: ∀ i : nat, (i < strings.length vlp)%nat → (l +ₗ i) ∈ dom h)
  (LOCKS: mem_app l lkp vlp h = Some (vl, h')) :
  dom h' ≡ dom h.
Proof.
  revert l h h' vl DEFINED LOCKS. induction vlp as [|sclp vlp IH]; intros l h h' vl DEFINED LOCKS; [inversion LOCKS; auto|].
  simpl in LOCKS; destruct (h !! l); simpl in LOCKS; [|inversion LOCKS].
  destruct p; destruct (lkp l0) eqn:EqLkp; simpl in LOCKS; [|inversion LOCKS].
  destruct (apply_policy _ _) eqn:EqAppLkp.
  destruct (mem_app _ _ _ _) eqn:EqMemApp; simpl in LOCKS; [|inversion LOCKS].
  destruct p; injection LOCKS; intros; subst.
  rewrite <- (dom_map_insert_is_Some h l (l1, swrite)).
  2: { apply elem_of_dom. rewrite <- (shift_loc_0_nat l). apply DEFINED; simpl; lia. }
  rewrite <- (IH (l +ₗ 1%nat) (<[l:=(l1, swrite)]>h) h' v); simpl in LOCKS.
  - reflexivity.
  - intros i Bound; rewrite (dom_map_insert_is_Some _ _ _).
    * rewrite shift_loc_assoc_nat. apply DEFINED. simpl; lia.
    * rewrite <- elem_of_dom; rewrite <- (shift_loc_0_nat l).
      apply DEFINED; simpl; lia.
  - exact EqMemApp.
Qed.

Lemma read_success_implies_defined h h' l vl lkp vlp :
  mem_app l lkp vlp h = Some (vl, h') ->
  (forall i:nat, (i < length vlp)%nat -> (l +ₗ i) ∈ dom h).
Proof.
  revert h h' l vl.
  induction vlp; simpl; intros h h' l vl.
  - intros _ i Absurd; lia.
  - destruct (h !! l) eqn:EqLookup; simpl; [|intro H; inversion H].
    destruct p.
    destruct (lkp l0) eqn:EqLkPol; simpl; [|intro H; inversion H].
    destruct (apply_policy _ _) eqn:EqAppPol.
    destruct (mem_app (l +ₗ 1) _ _ _) eqn:EqMemApp; simpl; [|intro H; inversion H].
    destruct p.
    intro H; injection H; intros; subst.
    destruct i.
    * rewrite elem_of_dom. apply (mk_is_Some _ (l0, s)). rewrite shift_loc_0_nat. exact EqLookup.
    * rewrite <- (dom_map_insert_is_Some h).
      2: { apply (mk_is_Some _ (l0, s)). exact EqLookup. }
      rewrite <- Nat.add_1_l. rewrite <- shift_loc_assoc_nat.
      apply (IHvlp _ _ _ _ EqMemApp i); lia.
Qed.

Lemma read_step_wf σ σ' e e' atm l bor ptr vl efs :
  mem_expr_step σ.(shp) e (ReadEvt atm l bor ptr vl) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (ReadEvt atm l bor ptr vl)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  all: inversion IS; clear IS; simplify_eq.
  all: constructor; simpl.
  - (* Atomic, dom *)
    intros blk' l'; rewrite <- (apply_within_trees_same_dom trs _ _ _ ACC).
    rewrite <- (elem_of_dom h').
    rewrite (mem_app_dom _ _ _ _ h h' _ READ).
    1: { rewrite elem_of_dom. apply (WF.(state_wf_dom _) blk' l'). }
    unfold policy_read. rewrite repeat_length; intros i Bound.
    apply (read_success_implies_defined _ _ _ _ _ _ READ). unfold policy_read. rewrite repeat_length; done.
  - (* Atomic, wf *)
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_read_wf.
    * apply (WF.(state_wf_tree_item _)).
  - (* Atomic, nonempty *)
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (memory_read_preserve_nonempty _ _ _) ACC).
  - (* Atomic, cids *) apply (WF.(state_wf_cid_agree _)).
  - (* NaStart, dom *)
    intros blk' l'. rewrite <- (elem_of_dom h'). rewrite (mem_app_dom _ _ _ _ h h' _ READ).
    * rewrite elem_of_dom. apply (WF.(state_wf_dom _)).
    * rewrite repeat_length; intros i Bound. apply (read_success_implies_defined _ _ _ _ _ _ READ).
      rewrite repeat_length; done.
  - (* NaStart, wf *) apply WF.(state_wf_tree_item _).
  - (* NaStart, nonempty *) apply WF.(state_wf_non_empty _).
  - (* NaStart, cids *) apply WF.(state_wf_cid_agree _).
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* NaEnd, dom *)
    intros blk' l'; rewrite <- (apply_within_trees_same_dom trs _ _ _ ACC).
    rewrite <- (elem_of_dom h').
    rewrite (mem_app_dom _ _ _ _ h h' _ READ).
    1: { rewrite elem_of_dom. apply (WF.(state_wf_dom _) blk' l'). }
    unfold policy_read. rewrite repeat_length; intros i Bound.
    apply (read_success_implies_defined _ _ _ _ _ _ READ). unfold policy_read. rewrite repeat_length; done.
  - (* NaEnd, wf *)
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_read_wf.
    * apply WF.(state_wf_tree_item _).
  - (* NaEnd, nonempty *)
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (memory_read_preserve_nonempty _ _ _) ACC).
  - (* NaEnd, cids *) apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma write_step_wf σ σ' e e' atm l bor ptr vl efs :
  mem_expr_step σ.(shp) e (WriteEvt atm l bor ptr vl) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (WriteEvt atm l bor ptr vl)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq.
  all: inversion IS; clear IS; simplify_eq.
  all: constructor; simpl.
  - (* Atomic, dom *)
    intros blk' l'; rewrite <- (apply_within_trees_same_dom trs _ _ _ ACC).
    rewrite <- (elem_of_dom h').
    rewrite (mem_app_dom _ _ _ _ h h' _ WRITE).
    1: { rewrite elem_of_dom. apply (WF.(state_wf_dom _) blk' l'). }
    unfold policy_read. rewrite map_length; intros i Bound.
    apply (read_success_implies_defined _ _ _ _ _ _ WRITE). unfold policy_write. rewrite map_length; done.
  - (* Atomic, wf *)
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_write_wf.
    * apply (WF.(state_wf_tree_item _)).
  - (* Atomic, nonempty *)
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (memory_write_preserve_nonempty _ _ _) ACC).
  - (* Atomic, cids *) apply (WF.(state_wf_cid_agree _)).
  - (* NaStart, dom *)
    intros blk' l'. rewrite <- (elem_of_dom h'). rewrite (mem_app_dom _ _ _ _ h h' _ WRITE).
    * rewrite elem_of_dom. apply (WF.(state_wf_dom _)).
    * rewrite repeat_length; intros i Bound. apply (read_success_implies_defined _ _ _ _ _ _ WRITE).
      rewrite repeat_length; done.
  - (* NaStart, wf *) apply WF.(state_wf_tree_item _).
  - (* NaStart, nonempty *) apply WF.(state_wf_non_empty _).
  - (* NaStart, cids *) apply WF.(state_wf_cid_agree _).
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* Atomicity mismatch *) destruct ATOMICITY as [H|H]; inversion H.
  - (* NaEnd, dom *)
    intros blk' l'; rewrite <- (apply_within_trees_same_dom trs _ _ _ ACC).
    rewrite <- (elem_of_dom h').
    rewrite (mem_app_dom _ _ _ _ h h' _ WRITE).
    1: { rewrite elem_of_dom. apply (WF.(state_wf_dom _) blk' l'). }
    unfold policy_read. rewrite map_length; intros i Bound.
    apply (read_success_implies_defined _ _ _ _ _ _ WRITE). unfold policy_write. rewrite map_length; done.
  - (* NaEnd, wf *)
    apply (apply_within_trees_wf _ _ nxtp' nxtp' nxtc' nxtc' _ _ ACC).
    * tauto.
    * intros tr tr'. apply memory_write_wf.
    * apply WF.(state_wf_tree_item _).
  - (* NaEnd, nonempty *)
    apply (apply_within_trees_preserve_nonempty _ _ _ _ (WF.(state_wf_non_empty _)) (memory_write_preserve_nonempty _ _ _) ACC).
  - (* NaEnd, cids *) apply (WF.(state_wf_cid_agree _)).
Qed.

Lemma initcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (InitCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (InitCallEvt n)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [try apply WF..|].
  - apply (wf_trees_increasing _ nxtp' n nxtp' (S n)); [lia|lia|apply WF].
  - intros c. rewrite elem_of_union.
    move => [|/(state_wf_cid_agree _ WF)]; [intros ->%elem_of_singleton_1; by left|by right].
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' n efs :
  mem_expr_step σ.(shp) e (EndCallEvt n) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (EndCallEvt n)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|].
  - intros c IN. apply WF.
    apply elem_of_difference in IN. apply IN.
Qed.

(** Retag *)
Lemma insert_Exists_split {X} (tr:tree X) (ins:X) prop search
  {search_dec:forall x, Decision (search x)} :
  tree_Exists prop (insert_child_at tr ins search) ->
  tree_Exists prop tr \/ (tree_Exists search tr /\ prop ins).
Proof.
  induction tr; simpl; auto; intro Ex.
  destruct (decide (search data)).
  - destruct Ex as [Ex0 | [Ex1 | Ex2]]; auto.
    * destruct (IHtr1 Ex1) as [Ex0' | [Ex1' Ex2']]; auto.
    * destruct Ex2 as [Ex0' | [Ex1' | Ex2']]; auto.
      + destruct (IHtr2 Ex1') as [Ex0'' | [Ex1'' Ex2'']]; auto.
      + inversion Ex2'.
  - destruct Ex as [Ex0 | [Ex1 | Ex2]]; auto.
    * destruct (IHtr1 Ex1) as [Ex0' | [Ex1' Ex2']]; auto.
    * destruct (IHtr2 Ex2) as [Ex0' | [Ex1' Ex2']]; auto.
Qed.

Lemma insert_child_wf cids ot range nxtp newp nxtc :
  (match newp.(new_protector) with None => True | Some {| call:=c |} => (c < nxtc)%nat end) ->
  preserve_tree_wf (create_child cids ot range (Tag nxtp) newp) nxtp (S nxtp) nxtc nxtc.
Proof.
  intros NewpBound tr tr' WF CREATE.
  unfold create_child in CREATE.
  destruct (memory_read _ _ _ _) eqn:MemRead; simpl in CREATE; [injection CREATE; intros; subst; clear CREATE|inversion CREATE].
  unfold wf_tree; unfold tree_item_included. rewrite <- tree_Forall_forall.
  apply insert_True_preserves_Forall.
  - unfold item_included. destruct newp; simpl in *.
    destruct new_protector as [p|]; simpl in *.
    * destruct p; split; lia.
    * lia.
  - rewrite tree_Forall_forall. apply (wf_tree_increasing _ nxtp nxtc (S nxtp) nxtc); [lia|lia|].
    eapply memory_read_wf; [exact WF|exact MemRead].
Qed.

Lemma retag_step_wf σ σ' e e' l ot nt ptr kind c efs :
  mem_expr_step σ.(shp) e (RetagEvt l ot nt ptr kind c) σ'.(shp) e' efs →
  bor_step σ.(strs) σ.(scs) σ.(snp) σ.(snc)
           (RetagEvt l ot nt ptr kind c)
           σ'.(strs) σ'.(scs) σ'.(snp) σ'.(snc) →
  state_wf σ → state_wf σ'.
Proof.
  destruct σ as [h trs cids nxtp nxtc].
  destruct σ' as [h' trs' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - intros blk' l'. rewrite <- (apply_within_trees_same_dom _ _ _ _ RETAG_EFFECT). apply WF.
  - apply (apply_within_trees_wf _ _ nxtp (S nxtp) nxtc' nxtc' _ _ RETAG_EFFECT).
    * intro tr. apply wf_tree_increasing; lia.
    * intros tr tr'.
      apply insert_child_wf.
      destruct (kindof ptr); destruct kind; simpl in NEW_PERM.
      (* NEW_PERM can be a lot of things, so there are many possible injections/inversions *)
      all: unfold newperm_from_box in NEW_PERM; unfold newperm_from_ref in NEW_PERM.
      all: try destruct mut; try destruct pin; try destruct frz.
      all: try (inversion NEW_PERM; done).
      all: injection NEW_PERM; intros; subst; clear NEW_PERM; simpl.
      all: apply WF.(state_wf_cid_agree _); simpl; exact EL.
    * apply WF.
  - apply (apply_within_trees_preserve_nonempty _ _ _ _ WF.(state_wf_non_empty _) (create_child_preserve_nonempty _ _ _ _ _) RETAG_EFFECT).
  - apply WF.
Qed.

Lemma base_step P σ σ' e e' efs :
  base_step P e σ e' σ' efs → state_wf σ → state_wf σ'.
Proof.
  intros HS WF. inversion HS; [by subst|]. simplify_eq.
  rename select event into ev. destruct ev.
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply read_step_wf; eauto.
  - eapply write_step_wf; eauto.
  - eapply initcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - rename select (mem_expr_step _ _ _ _ _ _) into Hstep. inversion Hstep.
Qed.
*)
