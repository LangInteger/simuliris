(** This file provides the basic heap and ghost state support for the BorIngLang program logic. *)
From iris.proofmode Require Export proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From simuliris.base_logic Require Export gen_sim_prog.
From simuliris.simulation Require Export slsls gen_log_rel.
From simuliris.simulation Require Import lifting.
From simuliris.tree_borrows Require Import tkmap_view.
From simuliris.tree_borrows Require Export defs.
From simuliris.tree_borrows Require Export steps_wf.
From simuliris.tree_borrows Require Import steps_progress.
From iris.prelude Require Import options.


(* TODO cleanup *)
Section utils.

  Definition tree_lookup (tr : tree item) (tg : tag) (it : item) := tree_contains tg tr ∧ tree_item_determined tg it tr.

  Definition trees_lookup (trs : trees) blk tg it :=
    exists tr,
      trs !! blk = Some tr
      /\ tree_lookup tr tg it.

  Lemma lookup_implies_contains
    {tr tg it} :
    tree_lookup tr tg it -> tree_contains tg tr.
  Proof. intro H. apply H. Qed.

  Lemma unique_implies_lookup {tr tg} :
    tree_unique tr tg -> ∃ it, tree_lookup tg tr it.
  Proof.
    intros Hunq.
    pose proof Hunq as (it&Hdet)%unique_lookup.
    exists it; split; last done.
    by eapply unique_exists.
  Qed.

  Lemma tree_lookup_correct_tag {tr tg it} :
    tree_lookup tr tg it ->
    it.(itag) = tg.
  Proof. intros [? ?]. eapply tree_determined_specifies_tag; eassumption. Qed.

  Lemma trees_lookup_correct_tag {trs blk tg it} :
    trees_lookup trs blk tg it ->
    it.(itag) = tg.
  Proof. intros [?[??]]. eapply tree_lookup_correct_tag; eassumption. Qed.

  Lemma item_wf_lookup it l ev1 ev2 :
    item_wf it ev1 ev2 →
    lazy_perm_wf (item_lookup it l).
  Proof.
    intros [H1 H2 H3 H4].
    rewrite /item_lookup. edestruct (iperm it !! l) as [pp|] eqn:H5.
    - simpl. eapply map_Forall_lookup_1 in H4; done.
    - simpl. intros Hne. exfalso. apply H3, Hne.
Qed.

  Definition tag_valid (upper : tag) (n : tag) : Prop := (n < upper)%nat.

  Lemma tag_valid_mono upper1 upper2 n1 n2 :
    tag_valid upper1 n1 →
    (upper1 ≤ upper2)%nat →
    (n2 ≤ n1)%nat →
    tag_valid upper2 n2.
  Proof.
    rewrite /tag_valid. lia.
  Qed.

  Context (C : gset call_id).

  Inductive pseudo_conflicted (tr : tree item) (tg : tag) (l : Z)
    : res_conflicted → Prop :=
    | pseudo_conflicted_conflicted :
        (* a Conflicted marker makes the permission literally conflicted *)
        pseudo_conflicted tr tg l ResConflicted
    | pseudo_conflicted_cousin_init tg_cous it_cous :
        (* If it's not actually conflicted, it can be pseudo conflicted if there is *)
        (* A cousin that is protected *)
        rel_dec tr tg tg_cous = Foreign Cousin ->
        tree_lookup tr tg_cous it_cous ->
        protector_is_active it_cous.(iprot) C ->
        (* and who on this location is initalized not disabled *)
        (item_lookup it_cous l).(perm) ≠ Disabled ->
        (item_lookup it_cous l).(initialized) = PermInit ->
        pseudo_conflicted tr tg l ResActivable
    .

  Inductive disabled_in_practice (tr : tree item) (tg : tag) (witness : tag) (l : Z)
    : Prop :=
    | disabled_parent it_witness inclusive :
      (* Doesn't have to be immediate, just any parent is Disabled *)
      rel_dec tr tg witness = Child inclusive ->
      tree_lookup tr witness it_witness ->
      (item_lookup it_witness l).(perm) = Disabled ->
      (* FIXME: is the hypothesis of not being protected necessary here ?
           We certainly need it somewhere, but does it have to be here or can we
           deduce it from some other invariant ? *)
      ~protector_is_active it_witness.(iprot) C ->
      disabled_in_practice tr tg witness l
    (* FIXME: consider relaxing this to include true Disabled *)
    .

  Inductive perm_eq_up_to_C (tr1 tr2 : tree item) (tg : tag) (l : Z) cid
    : lazy_permission -> lazy_permission -> Prop :=
    | perm_eq_up_to_C_refl p :
        (* Usually the permissions will be equal *)
        perm_eq_up_to_C tr1 tr2 tg l cid p p
    | perm_eq_up_to_C_pseudo ini im confl1 confl2 :
        (* But if they are protected *)
        protector_is_active cid C ->
        (* And both pseudo-conflicted *)
        pseudo_conflicted tr1 tg l confl1 ->
        pseudo_conflicted tr2 tg l confl2 ->
        (* then we can allow a small difference *)
        perm_eq_up_to_C tr1 tr2 tg l cid
          {| initialized := ini; perm := Reserved im confl1 |}
          {| initialized := ini; perm := Reserved im confl2 |}
    | perm_eq_up_to_C_pseudo_post_prot ini im confl1 confl2 :
        (* But if they are not protected *)
        ¬ protector_is_active cid C ->
        (* then we can allow a small difference *)
        perm_eq_up_to_C tr1 tr2 tg l cid
          {| initialized := ini; perm := Reserved im confl1 |}
          {| initialized := ini; perm := Reserved im confl2 |}
    | perm_eq_up_to_C_disabled_parent witness_tg p p' :
        (* Finally if they have a Disabled parent we allow anything (unprotected) since
           nothing is possible through this tag anyway *)
        disabled_in_practice tr1 tg witness_tg l ->
        disabled_in_practice tr2 tg witness_tg l ->
        (* Added initialization requirement to help with the lemma [perm_eq_up_to_C_same_init] *)
        (initialized p = initialized p') ->
        ~protector_is_active cid C ->
        perm_eq_up_to_C tr1 tr2 tg l cid p p'
    .

  Definition loc_eq_up_to_C (tr1 tr2 : tree item) (tg : tag) (it1 it2 : item) (l : Z) :=
    it1.(iprot) = it2.(iprot)
    /\ perm_eq_up_to_C tr1 tr2 tg l it1.(iprot) (item_lookup it1 l) (item_lookup it2 l).

  Definition item_eq_up_to_C (tr1 tr2 : tree item) (tg : tag) (it1 it2 : item) :=
    forall l, loc_eq_up_to_C tr1 tr2 tg it1 it2 l.

  Definition tree_equal (tr1 tr2 : tree item) :=
    (* To be equal trees must have exactly the same tags *)
    (forall tg, tree_contains tg tr1 <-> tree_contains tg tr2)
    (* and define all the same relationships between those tags *)
    /\ (forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (* and have their permissions be equal up to C on all locations *)
    (* FIXME: maybe think about reformulating ∧ (∀ t it1 it2, tree_lookup t it1 tr1 -> tree_lookup t it2 tr2 -> it_rel it1 it2) *)
    /\ (forall tg, tree_contains tg tr1 ->
          exists it1 it2,
            tree_lookup tr1 tg it1
            /\ tree_lookup tr2 tg it2
            /\ item_eq_up_to_C tr1 tr2 tg it1 it2
       ).

  Definition trees_equal (t1 t2 : trees) :=
    ∀ blk, option_Forall2 tree_equal (t1 !! blk) (t2 !! blk).


  Lemma loc_eq_up_to_C_reflexive
    {tr1 tr2 tg it l}
    : loc_eq_up_to_C tr1 tr2 tg it it l.
  Proof.
    split.
    + reflexivity.
    + apply perm_eq_up_to_C_refl.
  Qed.

  Lemma item_eq_up_to_C_reflexive
    {tr1 tr2 tg it}
    : item_eq_up_to_C tr1 tr2 tg it it.
  Proof.
    intro l.
    apply loc_eq_up_to_C_reflexive.
  Qed.

  Lemma tree_equal_reflexive tr
    (AllUnique : forall tg, tree_contains tg tr -> exists it, tree_item_determined tg it tr)
    : tree_equal tr tr.
  Proof.
    try repeat split.
    - tauto.
    - tauto.
    - intros tg Ex.
      destruct (AllUnique tg Ex).
      eexists. eexists.
      try repeat split.
      + assumption.
      + eassumption.
      + assumption.
      + eassumption.
      + apply item_eq_up_to_C_reflexive.
  Qed.


  Lemma trees_equal_reflexive trs
    (AllUnique : forall blk tr tg,
      trs !! blk = Some tr ->
      tree_contains tg tr ->
      exists it, tree_item_determined tg it tr)
    : trees_equal trs trs.
  Proof.
    intros blk.
    specialize (AllUnique blk).
    remember (trs !! blk) as at_blk.
    destruct at_blk.
    - apply Some_Forall2.
      apply tree_equal_reflexive.
      intro tg.
      eapply AllUnique.
      reflexivity.
    - apply None_Forall2.
  Qed.


  Lemma trees_equal_same_tags (trs1 trs2 : trees) (tg : tag) (blk : block) :
    trees_equal trs1 trs2 ->
    trees_contain tg trs1 blk <-> trees_contain tg trs2 blk.
  Proof.
    intro Equals.
    rewrite /trees_equal in Equals.
    specialize (Equals blk).
    rewrite /trees_contain /trees_at_block.
    destruct (trs1 !! blk) as [tr1|];
      destruct (trs2 !! blk) as [tr2|];
      inversion Equals as [?? Equal|].
    2: tauto.
    subst.
    destruct Equal as [SameTags _].
    apply SameTags.
  Qed.

  Lemma trees_equal_empty : trees_equal ∅ ∅.
  Proof.
    apply trees_equal_reflexive.
    intros blk tr tg LookupEmp.
    inversion LookupEmp.
  Qed.

  Lemma perm_eq_up_to_C_sym
    {tr1 tr2 tg l cid perm1 perm2}
    : perm_eq_up_to_C tr1 tr2 tg l cid perm1 perm2
      -> perm_eq_up_to_C tr2 tr1 tg l cid perm2 perm1.
  Proof.
    intro EqC.
    inversion EqC.
    + econstructor.
    + econstructor; eassumption.
    + econstructor; eassumption.
    + econstructor; try eassumption.
      done.
  Qed.

  Lemma loc_eq_up_to_C_sym
    {tr1 tr2 tg it1 it2 l}
    : loc_eq_up_to_C tr1 tr2 tg it1 it2 l
      -> loc_eq_up_to_C tr2 tr1 tg it2 it1 l.
  Proof.
    intros [SameProt EqC].
    split.
    + auto.
    + apply perm_eq_up_to_C_sym.
      rewrite <- SameProt.
      assumption.
  Qed.

  Lemma item_eq_up_to_C_sym
    {tr1 tr2 tg it1 it2}
    : item_eq_up_to_C tr1 tr2 tg it1 it2
      -> item_eq_up_to_C tr2 tr1 tg it2 it1.
  Proof.
    intros EqC l.
    apply loc_eq_up_to_C_sym.
    auto.
  Qed.

  Lemma tree_equal_sym : Symmetric tree_equal.
  Proof.
    rewrite /tree_equal.
    intros tr1 tr2 [SameTg [SameRel EqC]].
    split; [|split].
    + intro tg. rewrite SameTg. tauto.
    + intros tg tg'. rewrite SameRel. tauto.
    + intros tg Ex.
      rewrite <- SameTg in Ex.
      destruct (EqC tg Ex) as [it1 [it2 [Lookup1 [Lookup2 EqCsub]]]].
      exists it2, it1.
      split; [|split].
      * assumption.
      * assumption.
      * apply item_eq_up_to_C_sym.
        assumption.
  Qed.

  Lemma trees_equal_sym : Symmetric trees_equal.
  Proof.
    rewrite /trees_equal.
    intros trs1 trs2 Equals blk.
    eapply (option_Forall2_sym tree_equal); [|auto].
    apply tree_equal_sym.
  Qed.

  Lemma every_node_iff_every_lookup
    {tr prop}
    (GloballyUnique : forall tg, tree_contains tg tr -> exists it, tree_item_determined tg it tr)
    : every_node prop tr <-> forall tg it, tree_lookup tr tg it -> prop it.
  Proof.
    rewrite every_node_eqv_universal.
    split.
    - intros Every tg it [Ex Unq].
      apply Every.
      eapply exists_node_increasing; [eassumption|].
      eapply every_node_increasing; [eassumption|].
      erewrite every_node_eqv_universal.
      intros. symmetry. auto.
    - intros Lookup it Exists.
      apply (Lookup (itag it)).
      assert (tree_contains it.(itag) tr) as Ex. {
        eapply exists_node_increasing; [eassumption|].
        erewrite every_node_eqv_universal.
        intros. subst. auto.
      }
      destruct (GloballyUnique _ Ex) as [it' Unq'].
      assert (it = it') as Eq. {
        apply (proj1 (every_node_eqv_universal _ _) Unq' it Exists).
        auto.
      }
      rewrite -Eq in Unq'.
      split; assumption.
  Qed.

  Lemma tree_equal_implies_globally_unique_1
    {tr1 tr2} :
    tree_equal tr1 tr2 ->
    forall tg, tree_contains tg tr1 -> exists it, tree_item_determined tg it tr1.
  Proof.
    intros [ExIff [SameRel Lookup]] tg Ex.
    destruct (Lookup _ Ex) as [it1 [it2 [Lookup1 [Lookup2 EqC]]]].
    exists it1.
    apply Lookup1.
  Qed.

  Lemma tree_equal_implies_globally_unique_2
    {tr1 tr2} :
    tree_equal tr1 tr2 ->
    forall tg, tree_contains tg tr2 -> exists it, tree_item_determined tg it tr2.
  Proof.
    intro Eq.
    pose proof (tree_equal_sym _ _ Eq) as Eq'.
    revert Eq'.
    apply tree_equal_implies_globally_unique_1.
  Qed.


  Lemma tree_equal_transfer_lookup_1
    {tr1 tr2 tg it1} :
    tree_equal tr1 tr2 ->
    tree_lookup tr1 tg it1 ->
    exists it2,
      tree_lookup tr2 tg it2
      /\ item_eq_up_to_C tr1 tr2 tg it1 it2.
  Proof.
    intros [SameTg [SameRel MkLookup]] [Ex1 Unq1].
    destruct (MkLookup _ Ex1) as [it1' [it2 [Lookup1' [Lookup2 EqC']]]].
    assert (it1 = it1') by (eapply tree_determined_unify; [eassumption|apply Unq1|apply Lookup1']).
    subst it1'.
    exists it2.
    split; assumption.
  Qed.

  Lemma tree_equal_transfer_lookup_2
    {tr1 tr2 tg it2} :
    tree_equal tr1 tr2 ->
    tree_lookup tr2 tg it2 ->
    exists it1,
      tree_lookup tr1 tg it1
      /\ item_eq_up_to_C tr1 tr2 tg it1 it2.
  Proof.
    intros Eq Lookup2.
    pose proof (tree_equal_sym _ _ Eq) as Eq'.
    destruct (tree_equal_transfer_lookup_1 Eq' Lookup2) as [it1 [Lookup1 EqC']].
    exists it1; split; [assumption|].
    apply item_eq_up_to_C_sym.
    assumption.
  Qed.

  Lemma is_Some_ignore_bind
    {X Y} {o : option X} {g : X -> Y} :
    is_Some (o ≫= fun x => Some (g x)) <-> is_Some o.
  Proof.
    destruct o; simpl; split; intro H.
    - auto.
    - auto.
    - inversion H; discriminate.
    - inversion H; discriminate.
  Qed.

  Lemma mutual_parent_child_both_or_neither
    {tg tg' tr} :
    StrictParentChildIn tg tg' tr ->
    StrictParentChildIn tg' tg tr ->
    forall br,
      exists_subtree (eq br) tr ->
      (tree_contains tg (of_branch br) <-> tree_contains tg' (of_branch br)).
  Proof.
    intros Rel Rel' br ExBr.
    destruct (decide (tree_contains tg (of_branch br))) as [Ex|nEx].
    all: destruct (decide (tree_contains tg' (of_branch br))) as [Ex'|nEx'].
    all: try tauto.
    all: exfalso.
    - enough (tree_contains tg' (of_branch br)) by contradiction.
      rewrite /StrictParentChildIn every_subtree_eqv_universal in Rel.
      pose proof (proj1 (exists_node_iff_exists_root _ _) Ex) as WitnessSubtree.
      rewrite exists_subtree_eqv_existential in WitnessSubtree.
      destruct WitnessSubtree as [br' [ExBr' TgRoot]].
      assert (exists_subtree (eq br') tr) as ExBr'' by (eapply exists_subtree_transitive; eauto).
      specialize (Rel br' ExBr'' TgRoot).
      eapply exists_node_transitive.
      + eassumption.
      + simpl in TgRoot.
        destruct br' as [[]]; simpl in *.
        right; right; assumption.
    - enough (tree_contains tg (of_branch br)) by contradiction.
      rewrite /StrictParentChildIn every_subtree_eqv_universal in Rel'.
      pose proof (proj1 (exists_node_iff_exists_root _ _) Ex') as WitnessSubtree.
      rewrite exists_subtree_eqv_existential in WitnessSubtree.
      destruct WitnessSubtree as [br' [ExBr' TgRoot]].
      assert (exists_subtree (eq br') tr) as ExBr'' by (eapply exists_subtree_transitive; eauto).
      specialize (Rel' br' ExBr'' TgRoot).
      eapply exists_node_transitive.
      + eassumption.
      + simpl in TgRoot.
        destruct br' as [[]]; simpl in *.
        right; right; assumption.
  Qed.

  Lemma involution_of_branch
    {X} {data : X} {tr1 tr2}
    : branch data tr1 tr2 = of_branch (data, tr1, tr2).
  Proof. reflexivity. Qed.

  Lemma strict_parent_self_impossible
    {tg tr} :
    tree_contains tg tr ->
    StrictParentChildIn tg tg tr ->
    False.
  Proof.
    intros Ex Strict.
    induction tr as [|? ? IHtr1 ? IHtr2]; [inversion Ex|].
    inversion Strict as [Strict0 [Strict1 Strict2]].
    inversion Ex as [Ex0 | [Ex1 | Ex2]].
    - apply IHtr2.
      + apply Strict0. assumption.
      + assumption.
    - apply IHtr1; assumption.
    - apply IHtr2; assumption.
  Qed.

  Lemma mutual_strict_parent_child_impossible
    {tg tg' tr} :
    tree_contains tg tr ->
    tree_contains tg' tr ->
    StrictParentChildIn tg tg' tr ->
    StrictParentChildIn tg' tg tr ->
    False.
  Proof.
    intros Ex Ex' Rel Rel'.
    enough (StrictParentChildIn tg tg tr).
    + eapply strict_parent_self_impossible.
      * exact Ex.
      * assumption.
    + eapply StrictParentChild_transitive; eassumption.
  Qed.

  Lemma mutual_parent_child_implies_equal
    {tg tg' tr} :
    tree_contains tg tr ->
    tree_contains tg' tr ->
    ParentChildIn tg tg' tr ->
    ParentChildIn tg' tg tr ->
    tg' = tg.
  Proof.
    rewrite /ParentChildIn.
    intros Ex Ex'.
    intros [|StrictRel]; [auto|].
    intros [|StrictRel']; [auto|].
    exfalso.
    eapply mutual_strict_parent_child_impossible.
    + exact Ex.
    + exact Ex'.
    + assumption.
    + assumption.
  Qed.

  Lemma rel_this_antisym
    {tr tg tg'} :
    tree_contains tg tr ->
    tree_contains tg' tr ->
    rel_dec tr tg tg' = Child This -> tg = tg'.
  Proof.
    rewrite /rel_dec.
    remember (decide (ParentChildIn tg tg' tr)) as Rel.
    remember (decide (ParentChildIn tg' tg tr)) as Rel'.
    destruct Rel; destruct Rel'.
    all: try (intro; discriminate).
    intros Ex Ex' _.
    eapply mutual_parent_child_implies_equal; eauto.
  Qed.

  Lemma rel_dec_refl tr tg :
    rel_dec tr tg tg = Child This.
  Proof.
    rewrite /rel_dec.
    rewrite decide_True; [|left; reflexivity].
    rewrite decide_True; [|left; reflexivity].
    reflexivity.
  Qed.

  Lemma child_of_this_is_foreign_for_cousin
    {tr tg_this tg_cous tg_child} :
    tree_unique tg_this tr ->
    tree_unique tg_cous tr ->
    tree_unique tg_child tr ->
    rel_dec tr tg_this tg_cous = Foreign Cousin ->
    (if rel_dec tr tg_child tg_this is Child _ then True else False) ->
    rel_dec tr tg_child tg_cous = Foreign Cousin.
  Proof.
    intros Ex_this Ex_cous Ex_child.
    intros Rel_this_cous Rel_child_this_Foreign.
    destruct (rel_dec _ tg_child _) as [|pos] eqn:Rel_child_this; [contradiction|].
    destruct pos.
    + rewrite /rel_dec in Rel_this_cous, Rel_child_this |- *.
      repeat destruct (decide (ParentChildIn _ _ _)); try discriminate.
      - enough (ParentChildIn tg_this tg_cous tr) by contradiction.
        eapply ParentChild_transitive; eassumption.
      - exfalso.
        eapply cousins_have_disjoint_children with (tg1 := tg_this) (tg2 := tg_cous).
        * eassumption.
        * assumption.
        * assumption.
        * rewrite /rel_dec.
          rewrite decide_False; [|eassumption].
          rewrite decide_False; [|eassumption].
          reflexivity.
        * eassumption.
        * eassumption.
      - enough (ParentChildIn tg_this tg_cous tr) by contradiction.
        eapply ParentChild_transitive; eassumption.
      - reflexivity.
    + rewrite (rel_this_antisym _ _ Rel_child_this); first assumption.
      all: apply unique_exists; assumption.
  Qed.

  Lemma cousin_write_for_initialized_protected_nondisabled_is_ub
    {it l acc_tg tr range tg b}
    (Lookup : tree_lookup tr tg it)
    (Protected : protector_is_active (iprot it) C)
    (NonDis : perm (item_lookup it l) ≠ Disabled)
    (IsInit : initialized (item_lookup it l) = PermInit)
    (IsCousin : rel_dec tr acc_tg tg = Foreign Cousin)
    (InRange : range'_contains range l)
    : ~ is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm AccessWrite)) C acc_tg range tr).
  Proof.
    intro Absurd.
    rewrite -apply_access_success_condition in Absurd.
    rewrite every_node_eqv_universal in Absurd.
    specialize (Absurd it).
    assert (itag it = tg) as Tg. { eapply tree_determined_specifies_tag; apply Lookup. }
    rewrite Tg in Absurd.
    rewrite IsCousin in Absurd.
    rewrite /item_apply_access /permissions_apply_range' in Absurd.
    rewrite is_Some_ignore_bind in Absurd.
    rewrite -mem_apply_range'_success_condition in Absurd.
    rewrite bool_decide_eq_true_2 in Absurd; [|auto].
    enough (is_Some (apply_access_perm AccessWrite (Foreign Cousin) true (item_lookup it l))) as Absurd'.
    - rewrite /apply_access_perm in Absurd'.
      destruct (item_lookup _ _) as [[] [[][]| | |]], b; simpl in Absurd'.
      all: try inversion Absurd'; discriminate.
    - rewrite /item_lookup. setoid_rewrite maybe_non_children_only_no_effect in Absurd; last done.
      apply Absurd; [|done].
      eapply exists_determined_exists; apply Lookup.
  Qed.

  Lemma pseudo_conflicted_allows_same_access
    {tr1 tr2 tg l confl1 confl2 kind rel isprot ini im acc_tg range it1 b}
    (* Main hypotheses *)
    (Confl1 : pseudo_conflicted tr1 tg l confl1)
    (Confl2 : pseudo_conflicted tr2 tg l confl2)
    (AccEx : tree_unique acc_tg tr1)
    (TgEx : tree_unique tg tr1)
    (* Auxiliary stuff to bind the local access to the global success for the pseudo conflicted case *)
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (ProtSpec : isprot = bool_decide (protector_is_active (iprot it1) C))
    (RelSpec : rel = rel_dec tr1 acc_tg tg)
    (PermSpec : item_lookup it1 l = {| initialized := ini; perm := Reserved im confl1 |})
    (InRange : range'_contains range l)
    : is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved im confl1 |})
    -> is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved im confl2 |}).
  Proof.
    rewrite /apply_access_perm /apply_access_perm_inner; simpl.
    (* Most cases are by reflexivity. *)
    destruct kind, rel; simpl.
    all: destruct ini, isprot; simpl; try auto.
    all: inversion Confl1 as [|?? RelCous LookupCous].
    all: inversion Confl2.
    all: destruct im.
    all: subst; simpl; try auto.
    (* Once we get reflexivity out of the way we are left with the accesses
       where there is UB in the target because of the conflicted.
       We now need to prove that actually there is also UB in the source,
       just not _here_, instead it occured at the cousin that creates the conflict. *)
    all: exfalso.
    (* FIXME: here we need a lemma that shows
       1. a Child/This access for tg is Foreign for tg_cous who is Cousin of tg
       2. a Foreign access for such tg_cous is UB globally.
       We can indeed check that in all of the following cases we have
       rel = This or rel = Child and kind = AccessWrite. *)
    all: eapply cousin_write_for_initialized_protected_nondisabled_is_ub.
    all: try exact GlobalSuccess.
    all: try eassumption.
    all: eapply child_of_this_is_foreign_for_cousin.
    all: try apply RelCous.
    all: try assumption.
    all: try rewrite -RelSpec; auto.
    all: apply GloballyUnique1; apply LookupCous.
  Qed.

  Lemma pseudo_conflicted_post_prot_allows_same_access
    {tr1 tg l confl1 confl2 kind rel isprot ini im acc_tg range it1 b}
    (* Main hypotheses *)
    (AccEx : tree_unique acc_tg tr1)
    (TgEx : tree_unique tg tr1)
    (* Auxiliary stuff to bind the local access to the global success for the pseudo conflicted case *)
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (NoProp : ¬ protector_is_active (iprot it1) C)
    (ProtSpec : isprot = bool_decide (protector_is_active (iprot it1) C))
    (RelSpec : rel = rel_dec tr1 acc_tg tg)
    (PermSpec : item_lookup it1 l = {| initialized := ini; perm := Reserved im confl1 |})
    (InRange : range'_contains range l)
    : is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved im confl1 |})
    -> is_Some
         (apply_access_perm kind rel isprot
            {| initialized := ini; perm := Reserved im confl2 |}).
  Proof.
    rewrite /apply_access_perm /apply_access_perm_inner; simpl.
    rewrite bool_decide_false in ProtSpec; last done. subst isprot.
    (* Most cases are by reflexivity. *)
    destruct kind, rel; simpl.
    all: destruct ini; simpl; try auto.
    all: destruct im.
    all: subst; simpl; try auto.
    all: destruct confl1, confl2.
    all: subst; simpl; try auto.
  Qed.

  (* FIXME: move this elsewhere *)
  Lemma if_fun_absorb_args {X Y} {b : bool} {x : X} {f g : X -> Y} :
    (if b then f else g) x = if b then f x else g x.
  Proof. destruct b; reflexivity. Qed.

  Lemma loc_eq_up_to_C_allows_same_access
    {tr1 tr2 tg it1 it2 l kind acc_tg range b}
    (Tg1 : itag it1 = tg)
    (Tg2 : itag it2 = tg)
    (UnqAcc : tree_unique acc_tg tr1)
    (Ex1 : tree_unique tg tr1)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (InRange : range'_contains range l)
    :
    loc_eq_up_to_C tr1 tr2 tg it1 it2 l ->
    is_Some (maybe_non_children_only b (apply_access_perm kind) (rel_dec tr1 acc_tg (itag it1))
            (bool_decide (protector_is_active (iprot it1) C))
            (item_lookup it1 l))
    ->
    is_Some (maybe_non_children_only b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))
     (bool_decide (protector_is_active (iprot it2) C))
     (item_lookup it2 l)).
  Proof.
    intros EqC Acc1.
    inversion EqC as [EqProt EqCLookup].
    inversion EqCLookup as
      [perm Lookup EqLookup
      |???? Prot Confl1 Confl2 Lookup1 Lookup2
      |???? Prot Lookup1 Lookup2
      |witness_tg ?? Dis1 Dis2 Lookup1 Lookup2
    ].
    - rewrite Tg2 -Tg1.
      rewrite -SameRel.
      rewrite -EqProt.
      apply Acc1.
    - rewrite Lookup2.
      rewrite -Lookup1 in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq.
      rewrite Heq. rewrite -Lookup2.
      eapply (pseudo_conflicted_allows_same_access Confl1 Confl2 UnqAcc Ex1 GloballyUnique1 GlobalSuccess).
      + rewrite -EqProt; reflexivity.
      + rewrite SameRel -Tg2 //=.
      + rewrite /item_lookup Lookup1 //=.
      + exact InRange.
      + rewrite Tg1 -Tg2 SameRel EqProt Heq // in Acc1.
    - rewrite Lookup2.
      rewrite -Lookup1 in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq.
      rewrite Heq. rewrite -Lookup2.
      eapply (pseudo_conflicted_post_prot_allows_same_access UnqAcc Ex1 GloballyUnique1 GlobalSuccess).
      + done.
      + rewrite -EqProt; reflexivity.
      + rewrite SameRel -Tg2 //=.
      + symmetry. apply Lookup1.
      + exact InRange.
      + rewrite Tg1 -Tg2 SameRel EqProt Heq // in Acc1.
    - (* This has to be a foreign access *)
      destruct (rel_dec tr1 acc_tg (itag it1)) eqn:AccRel.
      + rewrite <- EqProt.
        rewrite bool_decide_eq_false_2; last assumption.
        rewrite Tg2 -Tg1 -SameRel AccRel.
        rewrite /maybe_non_children_only /nonchildren_only.
        repeat rewrite if_fun_absorb_args.
        repeat case_match; first done.
        all: rewrite /apply_access_perm /apply_access_perm_inner //=.
        all: repeat case_match; done.
      + (* If it's a child access we then it's also a child access for the Disabled parent. *)
        inversion Dis1 as [it_witness ? RelWitness LookupWitness DisWitness UnprotWitness].
        rewrite <- apply_access_success_condition in GlobalSuccess.
        rewrite every_node_iff_every_lookup in GlobalSuccess. 2: {
          intros tg0 Ex0. apply unique_lookup. apply GloballyUnique1. assumption.
        }
        specialize (GlobalSuccess _ _ LookupWitness).
        pose proof (tree_determined_specifies_tag _ _ _ (proj1 LookupWitness) (proj2 LookupWitness))
          as WitnessTg.
        subst witness_tg.
        subst tg.
        assert (match rel_dec tr1 acc_tg (itag it_witness) with
          | Child _ => True
          | Foreign _ => False
          end
        ). {
          unfold rel_dec in RelWitness.
          destruct (decide _); last discriminate.
          unfold rel_dec in AccRel.
          destruct (decide _); last discriminate.
          unfold rel_dec.
          destruct (decide (ParentChildIn (itag it_witness) acc_tg tr1)) as [|WitnessAccRel]; first done.
          apply WitnessAccRel.
          eapply ParentChild_transitive.
          + eassumption.
          + eassumption.
        }
        destruct (rel_dec _ acc_tg (itag it_witness)); first contradiction.
        (* Finally we have all the ingredients of the contradiction *)
        rewrite /item_apply_access in GlobalSuccess.
        destruct GlobalSuccess as [? GlobalSuccess].
        rewrite bind_Some in GlobalSuccess.
        destruct GlobalSuccess as [tmp_perms [PermissionsApply Wrapper]].
        injection Wrapper; clear Wrapper; intros; subst.
        rewrite /permissions_apply_range' in PermissionsApply.
        pose proof (proj2 (mem_apply_range'_success_condition _ _ _) (mk_is_Some _ _ PermissionsApply))
          as PermissionApply.
        specialize (PermissionApply l InRange).
        unfold item_lookup in DisWitness.
        rewrite /maybe_non_children_only in PermissionApply.
        rewrite /nonchildren_only /= in PermissionApply.
        repeat rewrite if_fun_absorb_args in PermissionApply.
        rewrite Tauto.if_same in PermissionApply.
        rewrite /apply_access_perm /= in PermissionApply.
        destruct PermissionApply as [tmp_lazy PermissionApply].
        rewrite bind_Some in PermissionApply.
        destruct PermissionApply as [tmp_perm [ApplyAccessInner ValidateProt]].
        rewrite DisWitness in ApplyAccessInner.
        rewrite /apply_access_perm_inner in ApplyAccessInner.
        case_match; discriminate.
  Qed.

  Lemma item_eq_up_to_C_allows_same_access (b:bool)
    {tr1 tr2 tg it1 it2 kind acc_tg range}
    (Tg1 : itag it1 = tg)
    (Tg2 : itag it2 = tg)
    (UnqAcc : tree_unique acc_tg tr1)
    (Ex1 : tree_unique tg tr1)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    :
    item_eq_up_to_C tr1 tr2 tg it1 it2 ->
    is_Some (item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1) ->
    is_Some (item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2).
  Proof.
    rewrite /item_apply_access /permissions_apply_range'.
    rewrite is_Some_ignore_bind.
    rewrite is_Some_ignore_bind.
    intros EqC.
    intro App1.
    rewrite -mem_apply_range'_success_condition in App1.
    rewrite -mem_apply_range'_success_condition.
    intros l InRange.
    specialize (App1 l InRange).
    specialize (EqC l).
    eapply (loc_eq_up_to_C_allows_same_access Tg1 Tg2 UnqAcc Ex1); try done.
  Qed.

  Lemma tree_equal_allows_same_access_maybe_nonchildren_only (b:bool)
    {tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1) ->
    is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2).
  Proof.
    intros Eq UnqAcc Acc1.
    apply apply_access_success_condition.
    pose proof (proj2 (apply_access_success_condition _ _ _ _ _) Acc1) as Every1.
    (* Get it into a more usable form *)
    rewrite every_node_iff_every_lookup in Every1.
    2: eapply tree_equal_implies_globally_unique_1; eassumption.
    rewrite every_node_iff_every_lookup.
    2: eapply tree_equal_implies_globally_unique_2; eassumption.
    (* And now we can unfold the definitions more *)
    intros tg it Lookup2.
    pose proof Eq as EqCopy.
    destruct EqCopy as [ExIff [SameRel Lookup]].
    destruct (tree_equal_transfer_lookup_2 Eq Lookup2) as [it1 [Lookup1 EqC]].
    eapply (item_eq_up_to_C_allows_same_access b); [| | | | | | |eauto|].
    - erewrite tree_determined_specifies_tag. 2,3: eapply Lookup1. reflexivity.
    - erewrite tree_determined_specifies_tag. 2,3: eapply Lookup2. reflexivity.
    - apply UnqAcc.
    - apply GloballyUnique1. apply Lookup1.
    - eassumption.
    - apply Acc1.
    - exact GloballyUnique1.
    - eapply Every1; eassumption.
  Qed.

  Lemma tree_equal_allows_same_access
    {tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_access kind C acc_tg range tr1) ->
    is_Some (memory_access kind C acc_tg range tr2).
  Proof.
    by eapply (tree_equal_allows_same_access_maybe_nonchildren_only false).
  Qed. 

  Lemma tree_equal_allows_same_access_nonchildren_only
    {tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_access_nonchildren_only kind C acc_tg range tr1) ->
    is_Some (memory_access_nonchildren_only kind C acc_tg range tr2).
  Proof.
    by eapply (tree_equal_allows_same_access_maybe_nonchildren_only true).
  Qed.

  Lemma access_same_rel_dec
    {tr tr' fn cids acc_tg range}
    : tree_apply_access fn cids acc_tg range tr = Some tr' ->
    forall tg tg', rel_dec tr tg tg' = rel_dec tr' tg tg'.
  Proof.
    intros Acc tg tg'.
    rewrite /rel_dec.
    pose proof (@access_eqv_rel tg tg' _ _ _ _ _ _ Acc).
    pose proof (@access_eqv_rel tg' tg _ _ _ _ _ _ Acc).
    pose proof (@access_eqv_immediate_rel tg tg' _ _ _ _ _ _ Acc).
    pose proof (@access_eqv_immediate_rel tg' tg _ _ _ _ _ _ Acc).
    repeat destruct (decide _).
    all: try tauto.
  Qed.

  Lemma memory_access_same_rel_dec
    {tr tr' acc cids acc_tg range} b
    : memory_access_maybe_nonchildren_only b acc cids acc_tg range tr = Some tr' ->
    forall tg tg', rel_dec tr tg tg' = rel_dec tr' tg tg'.
  Proof. eapply access_same_rel_dec. Qed.

  Lemma access_preserves_pseudo_conflicted_activable (b:bool)
    {tr tg l kind acc_tg range tr'} :
    pseudo_conflicted tr tg l ResActivable ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr' ->
    pseudo_conflicted tr' tg l ResActivable.
  Proof.
    intros PseudoC Acc.
    inversion PseudoC as [|tg_cous it_cous cous_rel [cous_ex cous_det] cous_prot cous_nondis cous_init].
    destruct (apply_access_spec_per_node cous_ex cous_det Acc)
          as (cous' & cous'_spec & cous'_ex & cous'_det).
    symmetry in cous'_spec.
    rewrite bind_Some in cous'_spec.
    destruct cous'_spec as (perms' & perms'_spec & cous'_build).
    injection cous'_build; intros; subst; clear cous'_build.
    pose proof (mem_apply_range'_spec _ _ l _ _ perms'_spec) as effect_at_l.
    destruct (decide _).
    + (* within range. Big case analysis incoming. *)
      destruct effect_at_l as (perm' & perm'_lookup & perm'_spec).
      edestruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr acc_tg (itag it_cous))) as [Heff|Heff].
      all: rewrite Heff in perm'_spec.
      1: rewrite bind_Some in perm'_spec;
         destruct perm'_spec as (perm & perm_apply_inner & perm'_spec);
         rewrite bind_Some in perm'_spec;
         destruct perm'_spec as (perm_validated & perm_check_prot & perm'_spec).
      all: pose proof perm'_spec as [= <-].
      all: (econstructor; [ 
         erewrite <- access_same_rel_dec; eassumption
       | done
       | done
       | .. ]).
      * rewrite /item_lookup /= perm'_lookup /=.
        rewrite /item_lookup in cous_init.
        destruct (iperm it_cous !! l) eqn:it_cous_defined.
        all: rewrite it_cous_defined !cous_init in perm_check_prot.
        all: rewrite bool_decide_eq_true_2 in perm_check_prot; last assumption.
        all: destruct perm; try discriminate.
        all: injection perm_check_prot; intros; subst; congruence.
      * rewrite /item_lookup /= perm'_lookup /=.
        rewrite /item_lookup in cous_init.
        destruct (iperm it_cous !! l) eqn:it_cous_defined;
        rewrite it_cous_defined cous_init //=.
      * rewrite /item_lookup /= perm'_lookup //.
      * rewrite /item_lookup /= perm'_lookup //.
    + (* out of range is a lot easier *)
      econstructor.
      * erewrite <- access_same_rel_dec; eassumption.
      * split; eassumption.
      * eassumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
  Qed.

  Lemma access_preserves_pseudo_conflicted (b:bool)
    {tr tg l kind acc_tg range conf tr'} :
    pseudo_conflicted tr tg l conf ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr' ->
    pseudo_conflicted tr' tg l conf.
  Proof.
    intros Hpc Haccess. destruct conf.
    2: by eapply access_preserves_pseudo_conflicted_activable.
    inversion Hpc; by econstructor.
  Qed.

  Lemma tree_apply_access_preserves_protector
    {tr tr' tg acc_tg kind range b it it'}
    (Lookup : tree_lookup tr tg it)
    (Lookup' : tree_lookup tr' tg it')
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : iprot it' = iprot it.
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it'' [Spec'' [Ex'' Det'']]].
    symmetry in Spec''.
    destruct (item_apply_access_preserves_metadata it it'' Spec'') as [?[]].
    rewrite (tree_determined_unify (proj1 Lookup') (proj2 Lookup') Det'').
    done.
  Qed.

  Lemma disabled_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Dis : perm (item_lookup it loc) = Disabled)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ perm (item_lookup it' loc) = Disabled.
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    destruct (decide _).
    + destruct LocSpec as [val [LookupVal SpecVal]].
      rewrite /item_lookup LookupVal /=.
      rewrite /maybe_non_children_only /nonchildren_only in SpecVal.
      repeat case_match.
      1: { injection SpecVal; intros; subst; done. }
      all: rewrite /apply_access_perm /apply_access_perm_inner /= in SpecVal.
      all: rewrite Dis /= in SpecVal.
      all: repeat case_match; simpl in *; try congruence.
      all: injection SpecVal; intros; subst; simpl; done.
    + rewrite /item_lookup /= LocSpec Dis //.
  Qed.

  Lemma disabled_create_child_irreversible
    {tr tr' tg tg_old tg_new loc it pk rk cid}
    (Lookup : tree_lookup tr tg it)
    (Dis : perm (item_lookup it loc) = Disabled)
    (Ins : create_child C tg_old tg_new pk rk cid tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ perm (item_lookup it' loc) = Disabled.
  Proof.
    unfold create_child in Ins.
    injection Ins; clear Ins; intro Ins.
    subst tr'.
    exists it.
    destruct Lookup as [Ex Det].
    split; [split|].
    - apply insert_preserves_exists; assumption.
    - apply insert_true_preserves_every; last assumption.
      admit. (* Need wf of tags *)
    - assumption.
  Admitted.

  Lemma disabled_in_practice_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range witness loc b}
    (Dis : disabled_in_practice tr tg witness loc)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : disabled_in_practice tr' tg witness loc.
  Proof.
    inversion Dis as [?? Rel Lookup Perm NoProt].
    destruct (disabled_tree_apply_access_irreversible Lookup Perm Acc) as [it' [Lookup' Perm']].
    econstructor.
    + erewrite <- access_same_rel_dec; eassumption.
    + apply Lookup'.
    + apply Perm'.
    + erewrite tree_apply_access_preserves_protector; first eassumption.
      all: eassumption.
  Qed.

  Lemma if_same_guard_equal
    {P Q : Prop} {T} {x y x' y' : T} `{Decision P} `{Decision Q}
    (Iff : P <-> Q)
    (Ex : x = x')
    (Ey : y = y')
    : (if decide P then x else y) = (if decide Q then x' else y').
  Proof.
    repeat destruct (decide _); tauto.
  Qed.

  (* FIXME: move this lemma elsewhere *)
  Lemma create_child_same_rel_dec
    {tr tr' tg tg' tg_old tg_new pk rk cid}
    (Ne : tg_new ≠ tg)
    (Ne' : tg_new ≠ tg')
    (Ins : create_child C tg_old tg_new pk rk cid tr = Some tr')
    : rel_dec tr tg tg' = rel_dec tr' tg tg'.
  Proof.
    injection Ins; intro New.
    unfold rel_dec.
    apply if_same_guard_equal.
    - erewrite insert_eqv_rel; first (erewrite New; reflexivity); assumption.
    - f_equal.
      apply if_same_guard_equal.
      + erewrite insert_eqv_rel; first (erewrite New; reflexivity); assumption.
      + reflexivity.
      + f_equal.
        apply if_same_guard_equal.
        * erewrite insert_eqv_imm_rel; first (erewrite New; reflexivity); assumption.
        * reflexivity.
        * reflexivity.
    - f_equal.
      apply if_same_guard_equal.
      + erewrite insert_eqv_rel; first (erewrite New; reflexivity); assumption.
      + f_equal.
        apply if_same_guard_equal.
        * erewrite insert_eqv_imm_rel; first (erewrite New; reflexivity); assumption.
        * reflexivity.
        * reflexivity.
      + reflexivity.
  Qed.

  Lemma disabled_in_practice_create_child_irreversible
    {tr tr' tg tg_old tg_new pk rk cid witness loc}
    (Ne : tg_new ≠ tg)
    (Ne' : tg_new ≠ witness)
    (Dis : disabled_in_practice tr tg witness loc)
    (Ins : create_child C tg_old tg_new pk rk cid tr = Some tr')
    : disabled_in_practice tr' tg witness loc.
  Proof.
    inversion Dis as [it_witness ? Rel Lookup Perm NoProt].
    destruct (disabled_create_child_irreversible Lookup Perm Ins) as [it' [Lookup' Perm']].
    econstructor.
    + erewrite <- create_child_same_rel_dec; first eassumption.
      - eassumption.
      - eassumption.
      - eassumption.
    + apply Lookup'.
    + apply Perm'.
    + assert (it' = it_witness); last (subst; assumption).
      eapply tree_determined_unify.
      - eapply Lookup'.
      - eapply Lookup'.
      - eapply create_child_preserves_determined.
        * symmetry. eassumption.
        * eapply Lookup.
        * eassumption.
  Qed.

  Lemma most_init_comm {i i'} :
    most_init i i' = most_init i' i.
  Proof.
    unfold most_init.
    repeat case_match; reflexivity.
  Qed.

  Lemma most_init_noop {i} :
    most_init i PermLazy = i.
  Proof.
    unfold most_init.
    case_match; reflexivity.
  Qed.

  Lemma most_init_absorb {i} :
    most_init i PermInit = PermInit.
  Proof.
    unfold most_init.
    case_match; reflexivity.
  Qed.

  Lemma item_apply_access_effect_on_initialized
    {it it' l b kind rel range}
    (Acc : item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C rel range it = Some it')
    : initialized (item_lookup it' l)
    = if decide (range'_contains range l)
      then most_init (initialized (item_lookup it l)) (requires_init rel) 
      else initialized (item_lookup it l).
  Proof.
    unfold item_apply_access, permissions_apply_range' in Acc.
    rewrite bind_Some in Acc; destruct Acc as [iperm' [iperm'Spec Inj]].
    injection Inj; clear Inj; intros; subst.
    pose proof (mem_apply_range'_spec _ _ l _ _ iperm'Spec) as LocalSpec.
    case_match.
    2: { rewrite /item_lookup /=. f_equal. f_equal. assumption. }
    destruct LocalSpec as [val [valSpec MaybeApply]].
    unfold item_lookup; simpl.
    rewrite valSpec; clear valSpec; simpl.
    (* Now it's time to actually unfold [maybe_non_children_only] and [apply_access_perm] where
       [initialized] *might* be modified. *)
    unfold maybe_non_children_only in MaybeApply. rewrite most_init_comm. case_match.
    - unfold nonchildren_only in MaybeApply. case_match.
      + simpl. case_match.
        * injection MaybeApply; intros; subst; reflexivity.
        * unfold apply_access_perm in MaybeApply.
          destruct (apply_access_perm_inner _ _ _ _); simpl in *; last congruence.
          destruct (if most_init _ _ then _ else _); simpl in MaybeApply; last congruence.
          injection MaybeApply; clear MaybeApply; intros; subst.
          simpl. rewrite most_init_noop. reflexivity.
      + unfold apply_access_perm in MaybeApply.
        destruct (apply_access_perm_inner _ _ _ _); simpl in *; last congruence.
        destruct (if most_init _ _ then _ else _); simpl in MaybeApply; last congruence.
        injection MaybeApply; clear MaybeApply; intros; subst.
        simpl. rewrite most_init_absorb. reflexivity.
    - unfold apply_access_perm in MaybeApply.
      destruct (apply_access_perm_inner _ _ _ _); simpl in *; last congruence.
      destruct (if most_init _ _ then _ else _); simpl in MaybeApply; last congruence.
      injection MaybeApply; clear MaybeApply; intros; subst.
      simpl. rewrite most_init_comm. reflexivity.
  Qed.

  Lemma perm_eq_up_to_C_preserved_by_access (b:bool)
    {tr1 tr1' tr2 tr2' it1 it1' it2 it2' tg l acc_tg kind range}
    (SameProt : iprot it1 = iprot it2)
    (SameTg : itag it1 = itag it2) (* note: redundant *)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    :
    perm_eq_up_to_C tr1 tr2 tg l (iprot it1) (item_lookup it1 l) (item_lookup it2 l) ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_lookup tr1 tg it1 ->
    tree_lookup tr1' tg it1' ->
    tree_lookup tr2 tg it2 ->
    tree_lookup tr2' tg it2' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1 = Some it1' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2 = Some it2' ->
    perm_eq_up_to_C tr1' tr2' tg l (iprot it1') (item_lookup it1' l) (item_lookup it2' l).
  Proof.
    intros EqC Acc1 Acc2 Lookup1 Lookup1' Lookup2 Lookup2' ItAcc1 ItAcc2.
    inversion EqC as [p pSpec Equal|ini im confl1 confl2 Prot Confl1 Confl2 itLookup1 itLookup2|ini im confl1 confl2 NoProt itLookup1 itLookup2|????? SameInit].
    - (* reflexive case *)
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [PermsAcc1 it1'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [PermsAcc2 it2'Spec]].
      injection it2'Spec; intros; subst; clear it2'Spec.
      simpl.
      pose proof (mem_apply_range'_spec _ _ l _ _ PermsAcc1) as Perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ PermsAcc2) as Perms2'Spec.
      destruct (decide _).
      + (* within range *)
        destruct Perms1'Spec as [p1 [LookupSome1' PermAcc1]].
        destruct Perms2'Spec as [p2 [LookupSome2' PermAcc2]].
        rewrite /item_lookup LookupSome1' LookupSome2' /=.
        rewrite /item_lookup in Equal.
        rewrite Equal SameRel SameProt SameTg in PermAcc1.
        rewrite PermAcc1 in PermAcc2.
        injection PermAcc2; intros; subst. constructor.
      + (* outside range *)
        rewrite /item_lookup in Equal.
        rewrite /item_lookup /= Perms1'Spec Perms2'Spec Equal.
        constructor.
    - (* The permissions are pseudo-conflicted, this restricts the possible accesses. *)
      rewrite SameRel SameTg in ItAcc1.
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [perms1'Spec it1'Spec]].
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [perms2'Spec it2'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      injection it2'Spec; intros; subst; clear it2'Spec.
      rewrite /item_lookup /=.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms1'Spec) as perm1'Spec; clear perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms2'Spec) as perm2'Spec; clear perms2'Spec.
      (* Now we do the case analysis of the access that occured *)
      (* First off, if we're out of range then we can take the exact same witness. *)
      destruct (decide (range'_contains range l)).
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor.
        + assumption.
        + inversion Confl1; subst.
          * constructor.
          * eapply access_preserves_pseudo_conflicted_activable; eassumption.
        + inversion Confl2; subst.
          * constructor.
          * eapply access_preserves_pseudo_conflicted_activable; eassumption.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite bool_decide_eq_true_2 in perm1'Spec; [|assumption].
      rewrite bool_decide_eq_true_2 in perm2'Spec; [|rewrite -SameProt; assumption].
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      destruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec.
      2: { simplify_eq. econstructor; first done. all: by eapply access_preserves_pseudo_conflicted. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [tmp1 [tmp1Spec perm1'Spec]].
      injection perm1'Spec; simpl; intros; subst; clear perm1'Spec.
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [tmp2 [tmp2Spec perm2'Spec]].
      injection perm2'Spec; simpl; intros; subst; clear perm2'Spec.
      simpl in *.
      (* We can finally start the big case analysis at the level of the state machine *)
      destruct (most_init _), perm1, perm2; try congruence.
      all: injection tmp1Spec; intros; subst; clear tmp1Spec.
      all: injection tmp2Spec; intros; subst; clear tmp2Spec.
      all: destruct kind, (rel_dec _ _ _) eqn:relation, im, confl1; simpl in *; try discriminate.
      all: destruct confl2; simpl in *; try discriminate.
      all: try (injection perm1Spec; intros; subst); clear perm1Spec.
      all: try (injection perm2Spec; intros; subst); clear perm2Spec.
      all: try constructor; auto.
      all: try constructor.
      (* Now they are all ResActivable and we need to show that the cousin is still a witness.
         See the above lemma for exactly that. *)
      all: eapply access_preserves_pseudo_conflicted_activable; eassumption.
    - (* The permissions are formerly pseudo-conflicted, but the difference should no longer matter now. *)
      rewrite SameRel SameTg in ItAcc1.
      rewrite bind_Some in ItAcc1; destruct ItAcc1 as [perms1' [perms1'Spec it1'Spec]].
      rewrite bind_Some in ItAcc2; destruct ItAcc2 as [perms2' [perms2'Spec it2'Spec]].
      injection it1'Spec; intros; subst; clear it1'Spec.
      injection it2'Spec; intros; subst; clear it2'Spec.
      rewrite /item_lookup /=.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms1'Spec) as perm1'Spec; clear perms1'Spec.
      pose proof (mem_apply_range'_spec _ _ l _ _ perms2'Spec) as perm2'Spec; clear perms2'Spec.
      (* Now we do the case analysis of the access that occured *)
      (* First off, if we're out of range then we can take the exact same witness. *)
      destruct (decide (range'_contains range l)).
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor 3.
        assumption.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite bool_decide_eq_false_2 in perm1'Spec; [|assumption].
      rewrite bool_decide_eq_false_2 in perm2'Spec; [|rewrite -SameProt; assumption].
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      destruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec.
      2: { simplify_eq. econstructor; first done. all: by eapply access_preserves_pseudo_conflicted. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [tmp1 [tmp1Spec perm1'Spec]].
      injection perm1'Spec; simpl; intros; subst; clear perm1'Spec.
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [tmp2 [tmp2Spec perm2'Spec]].
      injection perm2'Spec; simpl; intros; subst; clear perm2'Spec.
      simpl in *.
      (* We can finally start the big case analysis at the level of the state machine *)
      edestruct (most_init ini _), perm1, perm2; try congruence.
      all: injection tmp1Spec; intros; subst; clear tmp1Spec.
      all: injection tmp2Spec; intros; subst; clear tmp2Spec.
      all: destruct kind, (rel_dec _ _ _) eqn:relation, im, confl1; simpl in *; try discriminate.
      all: destruct confl2; simpl in *; try discriminate.
      all: try (injection perm1Spec; intros; subst); clear perm1Spec.
      all: try (injection perm2Spec; intros; subst); clear perm2Spec.
      all: try by econstructor 1.
      all: try by econstructor 3.
    - econstructor.
      + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption.
        eassumption.
      + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption.
        eassumption.
      + rewrite (item_apply_access_effect_on_initialized ItAcc1).
        rewrite (item_apply_access_effect_on_initialized ItAcc2).
        rewrite SameInit.
        case_match; last reflexivity.
        f_equal. f_equal. rewrite SameTg. apply SameRel.
      + erewrite tree_apply_access_preserves_protector; first eassumption; eassumption.
  Qed.

  Lemma item_eq_up_to_C_preserved_by_access (b : bool)
    {tr1 tr1' tr2 tr2' it1 it1' it2 it2' tg acc_tg kind range}
    (SameTg : itag it1 = itag it2)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    :
    item_eq_up_to_C tr1 tr2 tg it1 it2 ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_lookup tr1 tg it1 ->
    tree_lookup tr1' tg it1' ->
    tree_lookup tr2 tg it2 ->
    tree_lookup tr2' tg it2' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1 = Some it1' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2 = Some it2' ->
    item_eq_up_to_C tr1' tr2' tg it1' it2'.
  Proof.
    intros EqC Acc1 Acc2 Lookup1 Lookup1' Lookup2 Lookup2' ItAcc1 ItAcc2.
    econstructor.
    - rewrite <- (proj1 (proj2 (item_apply_access_preserves_metadata _ _ ItAcc1))).
      rewrite <- (proj1 (proj2 (item_apply_access_preserves_metadata _ _ ItAcc2))).
      apply EqC. assumption.
    - eapply perm_eq_up_to_C_preserved_by_access.
      + apply EqC. assumption.
      + apply SameTg.
      + apply SameRel.
      + apply EqC.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
  Qed.

  Lemma tree_equal_preserved_by_access_maybe_nonchildren_only (b : bool)
    {tr1 tr2 tr1' tr2' kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    tree_equal tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_equal tr1' tr2'.
  Proof.
    intros [SameTg [SameRel EqC]] ExAcc Acc1 Acc2.
    split; [|split].
    - intros tg.
      rewrite <- (access_preserves_tags Acc1).
      rewrite <- (access_preserves_tags Acc2).
      apply SameTg.
    - intros tg tg'.
      rewrite <- (access_same_rel_dec Acc1).
      rewrite <- (access_same_rel_dec Acc2).
      apply SameRel.
    - intros tg Ex1'.
      pose proof (proj2 (access_preserves_tags Acc1) Ex1') as Ex1.
      pose proof (proj1 (SameTg _) Ex1) as Ex2.
      pose proof (proj1 (access_preserves_tags Acc2) Ex2) as Ex2'.
      destruct (EqC tg Ex1) as [it1 [it2 [Lookup1 [Lookup2 EqC12]]]].
      destruct (apply_access_spec_per_node Ex1 (proj2 Lookup1) Acc1) as [it1' [it1'Spec [_ Lookup1']]].
      destruct (apply_access_spec_per_node Ex2 (proj2 Lookup2) Acc2) as [it2' [it2'Spec [_ Lookup2']]].
      exists it1'. exists it2'.
      split; [|split].
      + split; assumption.
      + split; assumption.
      + eapply item_eq_up_to_C_preserved_by_access.
        * erewrite tree_lookup_correct_tag; [|exact Lookup1].
          erewrite tree_lookup_correct_tag; [|exact Lookup2].
          reflexivity.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * split; eassumption.
        * eassumption.
        * split; eassumption.
        * symmetry; assumption.
        * symmetry; assumption.
  Qed.

  Lemma tree_equal_preserved_by_memory_access
    {tr1 tr2 tr1' tr2' kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    tree_equal tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    memory_access kind C acc_tg range tr1 = Some tr1' ->
    memory_access kind C acc_tg range tr2 = Some tr2' ->
    tree_equal tr1' tr2'.
  Proof.
    by eapply (tree_equal_preserved_by_access_maybe_nonchildren_only false).
  Qed.

  Lemma tree_equal_preserved_by_memory_access_nonchildren_only
    {tr1 tr2 tr1' tr2' kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    tree_equal tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    memory_access_nonchildren_only kind C acc_tg range tr1 = Some tr1' ->
    memory_access_nonchildren_only kind C acc_tg range tr2 = Some tr2' ->
    tree_equal tr1' tr2'.
  Proof.
    by eapply (tree_equal_preserved_by_access_maybe_nonchildren_only true).
  Qed.

  Lemma tree_equal_memory_deallocate
    {tr1 tr2 tr1' tr2' acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    :
    tree_equal tr1 tr2 ->
    tree_contains acc_tg tr1 ->
    memory_deallocate C acc_tg range tr1 = Some tr1' ->
    memory_deallocate C acc_tg range tr2 = Some tr2' ->
    tree_equal tr1' tr2'.
  Proof.
    intros Heq Hcontains (pw1&Hacc1&<-%join_map_id_is_Some_identical)%bind_Some
                         (pw2&Hacc2&<-%join_map_id_is_Some_identical)%bind_Some.
    by eapply (@tree_equal_preserved_by_memory_access tr1 tr2).
  Qed.

  Lemma exists_node_to_tree_lookup tr itm
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr) :
    exists_node (eq itm) tr →
    tree_lookup tr (itag itm) itm.
  Proof.
    intros Hexi. assert (tree_contains (itag itm) tr) as Hcontain.
    - eapply exists_node_increasing; first done.
      eapply every_node_eqv_universal; intros ? _ <-. done.
    - split; first done.
      eapply GloballyUnique, unique_lookup in Hcontain as (it2 & Hit2).
      enough (itm = it2) by by subst itm.
      eapply every_node_eqv_universal in Hit2; first eapply Hit2.
      all: done.
  Qed.

  Lemma tree_lookup_to_exists_node tr itm :
    tree_lookup tr (itag itm) itm →
    exists_node (eq itm) tr.
  Proof.
    intros (Hcont&Hitm). by eapply exists_determined_exists.
  Qed.

  Lemma is_Some_if {A} (P : bool) (s:A) : is_Some (if P then Some s else None) → P.
  Proof.
    destruct P; first done.
    intros (x&[=]).
  Qed.

  Lemma is_Some_if_neg {A} (P : bool) (s:A) : is_Some (if P then None else Some s) → P = false.
  Proof.
    destruct P; last done.
    intros (x&[=]).
  Qed.

  Lemma tree_equal_allows_same_deallocation
    {tr1 tr2 acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_deallocate C acc_tg range tr1) ->
    is_Some (memory_deallocate C acc_tg range tr2).
  Proof.
    intros Heq Hunq (tr1'&(pw1&Hpw1&Htrr%mk_is_Some)%bind_Some).
    pose proof Hpw1 as HH.
    eapply mk_is_Some, tree_equal_allows_same_access in HH as (pw2&Hpw2). 2-4: done.
    opose proof (tree_equal_preserved_by_memory_access _ _ _ _ Hpw1 Hpw2) as Heqpw.
    1-3: done. 1: by eapply unique_exists.
    rewrite /memory_deallocate Hpw2 /option_bind //.
    eapply join_success_condition, every_node_map, every_node_eqv_universal.
    intros itm2 Hitm2%exists_node_to_tree_lookup.
    2: { intros ttg Hcont.
         eapply access_preserves_tags, GloballyUnique2 in Hcont.
         2: apply Hpw2. setoid_rewrite <- tree_apply_access_preserve_unique; last apply Hpw2.
         done. }
    assert (tree_contains (itag itm2) pw2) as Hcont by apply Hitm2.
    destruct Heqpw as (Hsame&_&Hacc). setoid_rewrite <- Hsame in Hcont.
    apply Hacc in Hcont as (itm1&itm2'&Hlu1&Hlu2&Hiteq).
    assert (itm2' = itm2) as ->.
    1: eapply tree_determined_unify. 1,3: eapply Hitm2. 1: eapply Hlu2.
    assert (itag itm1 = itag itm2) as Htageq.
    1: eapply tree_lookup_correct_tag, Hlu1.
    eapply join_success_condition in Htrr.
    setoid_rewrite every_node_map in Htrr.
    eapply every_node_eqv_universal in Htrr.
    2: { eapply tree_lookup_to_exists_node. rewrite -Htageq in Hlu1. done. }
    simpl in Htrr. eapply is_Some_if_neg in Htrr.
    destruct (Hiteq 0) as (Hloceq&_). simpl.
    rewrite -!Hloceq Htrr. done.
  Qed.

  Lemma trees_equal_insert tr1 tr2 ttr1 ttr2 blk :
    trees_equal tr1 tr2 →
    tree_equal ttr1 ttr2 →
    trees_equal (<[blk := ttr1]> tr1) (<[blk := ttr2]> tr2).
  Proof.
    intros Htr Httr blk'.
    destruct (decide (blk = blk')) as [Heq|Hne].
    - rewrite -!Heq !lookup_insert. by econstructor.
    - rewrite !lookup_insert_ne //.
  Qed.

  Lemma apply_within_trees_equal fn blk tr1 tr1' tr2 :
    (∀ ttr1 ttr1' ttr2, fn ttr1 = Some ttr1' → tree_equal ttr1 ttr2 →
       tr1 !! blk = Some ttr1 → tr1' !! blk = Some ttr1' → tr2 !! blk = Some ttr2 →
     ∃ ttr2', fn ttr2 = Some ttr2' ∧ tree_equal ttr1' ttr2') →
    apply_within_trees fn blk tr1 = Some tr1' →
    trees_equal tr1 tr2 →
    ∃ tr2', apply_within_trees fn blk tr2 = Some tr2' ∧
       trees_equal tr1' tr2'.
  Proof.
    intros Hfn Happly Heq.
    rewrite /apply_within_trees in Happly|-*.
    specialize (Heq blk) as Heqblk.
    inversion Heqblk as [ttr1 ttr2 Hteq Htr1 Htr2|HN1 HN2]; last rewrite -HN1 // in Happly.
    rewrite -Htr1 -?Htr2 /= in Happly|-*.
    destruct (fn ttr1) as [ttr1'|] eqn:Hfnttr1; last done.
    rewrite /= in Happly. injection Happly as <-.
    destruct (Hfn ttr1 ttr1' ttr2) as (ttr2' & Hfnttr2 & Heq'); try done.
    1: by rewrite lookup_insert.
    rewrite Hfnttr2 /=. eexists; split; first done.
    by apply trees_equal_insert.
  Qed.

  Lemma trees_equal_delete tr1 tr2 blk :
    trees_equal tr1 tr2 →
    trees_equal (delete blk tr1) (delete blk tr2).
  Proof.
    intros Htr blk'.
    destruct (decide (blk = blk')) as [Heq|Hne].
    - rewrite -!Heq !lookup_delete. by econstructor.
    - rewrite !lookup_delete_ne //.
  Qed.

  Lemma trees_equal_init_trees ts tt tg bl off sz :
    trees_equal ts tt →
    trees_equal (extend_trees tg bl off sz ts) (extend_trees tg bl off sz tt).
  Proof.
    intros Htrs. apply trees_equal_insert; first done.
    eapply tree_equal_reflexive.
    eapply wf_tree_tree_item_determined.
    eapply wf_init_tree.
  Qed.

  Lemma tree_all_protected_initialized_elem_of cid tr tg lst
    (AllUnique : forall tg, tree_contains tg tr -> tree_unique tg tr) :
    (tg, lst) ∈ tree_get_all_protected_tags_initialized_locs cid tr ↔
    ∃ it, tree_lookup tr tg it ∧ protector_is_for_call cid it.(iprot) ∧
    ∀ z, z ∈ lst ↔ initialized (item_lookup it z) = PermInit.
  Proof.
    setoid_rewrite tree_all_protected_initialized_exists_node.
    split.
    - intros (it&Hexit%exists_node_to_tree_lookup&Htg&Hprot&Hinit)%exists_node_eqv_existential. 2: done.
      rewrite Htg in Hexit. by eexists.
    - intros (it&Hit&Hprops). assert (itag it = tg) as <- by by eapply tree_lookup_correct_tag.
      eapply exists_node_eqv_existential. eexists; split; last done.
      by eapply tree_lookup_to_exists_node.
  Qed.

  Lemma item_eq_up_to_C_same_iprot tr1 tr2 tg it1 it2 : 
    item_eq_up_to_C tr1 tr2 tg it1 it2 →
    it1.(iprot) = it2.(iprot).
  Proof.
    intros H. specialize (H 0). inversion H. done.
  Qed.

  Lemma perm_eq_up_to_C_same_init tr1 tr2 tg off prot lp1 lp2 : 
    perm_eq_up_to_C tr1 tr2 tg off prot lp1 lp2 →
    initialized lp1 = initialized lp2.
  Proof.
    (* FIXME: fails because the equality does not hold in the case [disabled_parent]. *)
    intros H. try by inversion H.
  Qed.

  Lemma tree_equals_protected_initialized tr1 tr2 cid
    (AllUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (AllUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2) :
    tree_equal tr1 tr2 →
    tree_get_all_protected_tags_initialized_locs cid tr1 =
    tree_get_all_protected_tags_initialized_locs cid tr2.
  Proof.
    intros Heq. eapply gset_leibniz. intros (tg&lst).
    split; intros (it&Hlu&Hprot&Hinit)%tree_all_protected_initialized_elem_of; try done.
    all: eapply tree_all_protected_initialized_elem_of; first done.
    - edestruct (tree_equal_transfer_lookup_1 Heq Hlu) as (it'&Hit'&Heqit').
      exists it'. split; first done.
      split; first by erewrite <- item_eq_up_to_C_same_iprot.
      intros z. specialize (Hinit z). destruct (Heqit' z) as (_&Heqlu).
      by erewrite <- perm_eq_up_to_C_same_init.
    - edestruct (tree_equal_transfer_lookup_2 Heq Hlu) as (it'&Hit'&Heqit').
      exists it'. split; first done.
      split; first by erewrite item_eq_up_to_C_same_iprot.
      intros z. specialize (Hinit z). destruct (Heqit' z) as (_&Heqlu).
      by erewrite perm_eq_up_to_C_same_init.
  Qed.

  Lemma tree_equals_read_many_helper_2 tg (L : list Z) tr1 tr1' tr2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2) :
    tree_equal tr1 tr2 →
    tree_unique tg tr1 →
    let fn := (λ tr, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr) L) in
    fn tr1 = Some tr1' →
    ∃ tr2', fn tr2 = Some tr2' ∧  tree_equal tr1' tr2'.
  Proof.
    intros Heq Hunq''.
    induction L as [|off E IH] in tr1',Hunq''|-*.
    { simpl. intros [= ->]; by eexists. }
    simpl. intros (tr1'''&H1&H2)%bind_Some.
    specialize (IH _ Hunq'' H1) as (tr2'''&Htr2&HHtr2p). rewrite Htr2 /=.
    assert (tree_unique tg tr1''') as Hunq'''.
    { rewrite /tree_unique. erewrite <- tree_read_many_helper_2. 1: exact Hunq''. exact H1. }
    assert (wf_tree tr1''') as Hwf1'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf1. 1: apply H1. }
    assert (wf_tree tr2''') as Hwf2'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_2. 1: exact Hwf2. 1: apply Htr2. }
    opose proof (tree_equal_allows_same_access_nonchildren_only _ HHtr2p Hunq''' _) as (trr&Htrr).
    1: by apply wf_tree_tree_unique. 1: by eapply mk_is_Some.
    exists trr; split; first done.
    eapply tree_equal_preserved_by_memory_access_nonchildren_only.
    5-6: done. 3: done. 3: by eapply unique_exists.
    1-2: by eapply wf_tree_tree_unique.
  Qed.

  Lemma tree_equals_read_many_helper_1 (E : list (tag * gset Z)) tr1 tr1' tr2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2) :
    tree_equal tr1 tr2 →
    (∀ tg L, (tg, L) ∈ E → tree_unique tg tr1)→
    let fn := (λ tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, foldr (λ l tr2, tr2 ≫= memory_access_nonchildren_only AccessRead C tg (l, 1%nat)) (Some tr1) (elements L)) (Some tr) E) in
    fn tr1 = Some tr1' →
    ∃ tr2', fn tr2 = Some tr2' ∧ tree_equal tr1' tr2'.
  Proof.
    intros Heq Hunq.
    induction E as [|(tg&init_locs) S IH] in tr1',Hunq|-*.
    { simpl. intros [= ->]; by eexists. }
    simpl. intros (tr1''&H1&H2)%bind_Some.
    opose proof (IH _ _ H1) as (tr2''&Htr2&HHtr2); clear IH.
    { intros ???. eapply Hunq. by right. }
    rewrite Htr2 /=.
    ospecialize (Hunq tg init_locs _). 1: by left. revert H2.
    eapply tree_equals_read_many_helper_2.
    { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_1. 1: exact Hwf1. 1: apply H1. }
    { eapply preserve_tag_count_wf. 1: eapply tree_read_many_helper_1. 1: exact Hwf2. 1: exact Htr2. }
    { done. }
    { rewrite /tree_unique. erewrite <- tree_read_many_helper_1. 1: exact Hunq. exact H1. }
  Qed.

  Lemma tree_equals_read_all_protected_initialized' tr1 tr1' tr2 cid
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2) :
    tree_equal tr1 tr2 →
    tree_read_all_protected_initialized C cid tr1 = Some tr1' →
    ∃ tr2', tree_read_all_protected_initialized C cid tr2 = Some tr2' ∧
      tree_equal tr1' tr2'.
  Proof.
    intros Heq.
    rewrite /tree_read_all_protected_initialized.
    erewrite <- (tree_equals_protected_initialized tr1 tr2); last done.
    2-3: by eapply wf_tree_tree_unique.
    eapply tree_equals_read_many_helper_1. 1-3: done.
    {intros tg E. setoid_rewrite elem_of_elements.
      intros (it&Hit&_)%tree_all_protected_initialized_elem_of. all: eapply wf_tree_tree_unique; try apply Hwf1.
      by eapply lookup_implies_contains. }
  Qed.

  (* Remember that the entire reason we have [trees_equal] in the first place
     is to enable spurious reads. This is the lemma that verifies that after we
     do a spurious read we get a [tree_equal]. A companion lemma (stating
     that under certain circumstances the spurious read will succeed) will be proved
     separately.

     The hypotheses are guided by the optimizations that we want to prove.
     We can't (and don't plan to) do spurious reads anywhere, only on protected
     tags. For now we require that the tag also doesn't have Reserved or Active
     children. Both of these can be relaxed slightly, but a more general version
     of this lemma will come only if actually required.

     Because we have nice properties of transitivity and reflexivity of [tree_equal]
     already, the proof can be simplified by only considering the case where
     before the asymetric read the trees are identical. In other words we're going
     to check that a tree is [tree_equal] to itself after a read. *)
  Lemma tree_equal_asymetric_read
    {tr tr' acc_tg range it}
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    :
    (* Accessed tag must be in the tree and protected*)
    tree_lookup tr acc_tg it ->
    protector_is_active it.(iprot) C ->
    (* A bunch of extra conditions on the structure.
       There are various sources to these properties:
       - no reserved children is a property obtained by local analysis known only at optimization time
       - no active cousins is in wf of the tree
       - tag is not Disabled comes from the success of the access
       - tag is initialized is from local analysis
       - parents are initialized comes from the above + wf
       They are put in the same clause to simplify this theorem, but we will want
       a higher-level lemma that derives these assumptions from their actual justification. *)
    (forall tg' it' loc,
       tree_lookup tr tg' it' ->
       range'_contains range loc ->
       match rel_dec tr acc_tg tg', (item_lookup it' loc).(initialized), (item_lookup it' loc).(perm)  with
       | Foreign (Parent _), _, (Reserved _ _ | Active) => False (* No Reserved/Active children *)
       | Foreign Cousin, _, Active => False (* No Active cousins *)
       | Child _, PermLazy, _ => False (* Tag and its parents are initialized *)
       | Child This, _, Disabled => False (* The tag itself is not Disabled *)
       | _, _, _ => True
       end
    ) ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessRead C acc_tg range tr = Some tr' ->
    tree_equal tr tr'.
  Proof.
    intros Lkup Protected NoReadSensitiveChildren Spurious.
    split; last split.
    - intro tg. eapply access_preserves_tags. eassumption.
    - intros tg1 tg2. eapply access_same_rel_dec. eassumption.
    (* That was the easy part, helped by the fact that our initial configuration
       is reflexivity instead of a more general instance of [tree_equal].
       Soon it will get more interesting. *)
    - intros tg0 Ex.
      destruct (unique_implies_lookup (GloballyUnique _ Ex)) as [it0 Lookup0].
      exists it0.
      assert (tree_unique tg0 tr') as Unq0'. {
        erewrite <- tree_apply_access_preserve_unique; last eassumption.
        apply GloballyUnique. assumption.
      }
      destruct (apply_access_spec_per_node (proj1 Lookup0) (proj2 Lookup0) Spurious) as
          (it0' & it0'Spec & Ex0' & Det0').
      symmetry in it0'Spec.
      exists it0'.
      split; first assumption.
      split; first (split; assumption).
      (* Now down to per-item reasoning *)
      intro loc.
            split; first (eapply item_apply_access_preserves_metadata; eassumption).
      rewrite bind_Some in it0'Spec; destruct it0'Spec as (perms' & perms'Spec & EqIt).
      injection EqIt; intros; subst; clear EqIt.
      pose proof (mem_apply_range'_spec _ _ loc _ _ perms'Spec) as PerLoc.
      clear perms'Spec.
      assert (itag it0 = tg0) by (eapply tree_determined_specifies_tag; eapply Lookup0).
      assert (itag it = acc_tg) by (eapply tree_determined_specifies_tag; eapply Lkup).
      subst.
      (* Finally the reasoning is per-location *)
      destruct (decide _).
      + (* In range *)
        (* This will be needed when we later want to prove that [acc_tg] is a witness
           for [pseudo_conflicted]. *)
        assert ((item_lookup it loc).(initialized) = PermInit
                /\ (item_lookup it loc).(perm) ≠ Disabled) as WitnessProps. {
          specialize (NoReadSensitiveChildren (itag it) it loc Lkup ltac:(assumption)).
          rewrite rel_dec_refl in NoReadSensitiveChildren.
          destruct (initialized _); try tauto.
          destruct (perm _); try tauto.
          all: split; congruence.
        }
        (* Keep digging until [apply_access_perm_inner] *)
        destruct PerLoc as (perm' & perm'Lookup & perm'Spec).
        specialize (NoReadSensitiveChildren (itag it0) it0 loc Lookup0 ltac:(assumption)).
        unfold item_lookup in *; simpl.
        rewrite perm'Lookup /=.
        rewrite bind_Some in perm'Spec; destruct perm'Spec as (tmperm & Inner & perm'Spec).
        rewrite bind_Some in perm'Spec; destruct perm'Spec as (validated & MoreInit & EqPerm).
        injection EqPerm; clear EqPerm; intros; subst.
        (* Now big case analysis on the transition *)
        destruct (default _ _) as (initialized & perm) eqn:Lookup; simpl in *.
        destruct (rel_dec _ _ _) as [[]|[]] eqn:Rel; simpl in *; try discriminate; try tauto.
        all: destruct perm as [mut confl| | |]; simpl in *; try discriminate; try tauto.
        all: destruct (bool_decide _) eqn:isprot, initialized; simpl in *; try discriminate.
        (* Handle all the successes *)
        all: try (injection Inner; intros; subst).
        all: try (injection MoreInit; intros; subst).
        all: try constructor.
        (* Simplify and resume the case analysis *)
        all: try discriminate; try tauto.
        all: try destruct confl.
        all: try (injection Inner; intros; subst).
        all: try (injection MoreInit; intros; subst).
        all: try (apply perm_eq_up_to_C_refl; done).
        (* Finally the pseudo-conflicted analysis *)
        * eapply perm_eq_up_to_C_pseudo.
          ** eapply bool_decide_eq_true_1; assumption.
          (* The tag is indeed pseudo-conflicted, the witness is the accessed
             tag and we have all the hypotheses already. *)
          ** econstructor.
             ++ apply rel_dec_cousin_sym.
                apply Rel.
             ++ eassumption.
             ++ eassumption.
             ++ apply WitnessProps.
             ++ apply WitnessProps.
          ** econstructor.
        (* Exact same strategy as above *)
        * eapply perm_eq_up_to_C_pseudo.
          ** eapply bool_decide_eq_true_1; assumption.
          ** econstructor.
             ++ apply rel_dec_cousin_sym.
                apply Rel.
             ++ eassumption.
             ++ eassumption.
             ++ apply WitnessProps.
             ++ apply WitnessProps.
          ** econstructor.
      + (* Outside of access range, this was a noop. *)
        rewrite /item_lookup /= PerLoc.
        constructor.
  Qed.

  (* A portion of the preconditions come from well-formedness *)
  Lemma tree_equal_wf_asymetric_read
    {tr tr' acc_tg range it}
    (WF : wf_tree tr)
    (MoreInit : parents_more_init tr)
    :
    tree_lookup tr acc_tg it ->
    protector_is_active it.(iprot) C ->
    (forall tg' it' loc,
       tree_lookup tr tg' it' ->
       range'_contains range loc ->
       match rel_dec tr acc_tg tg', (item_lookup it' loc).(initialized), (item_lookup it' loc).(perm)  with
       | Foreign (Parent _), _, (Reserved _ _ | Active) => False (* No Reserved/Active children *)
       | Foreign Cousin, _, Active => False (* No Active cousins *)
       | Child This, PermLazy, _ => False (* Tag itself is initialized *)
       | Child This, _, Disabled => False (* The tag itself is not Disabled *)
       | _, _, _ => True
       end
    ) ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessRead C acc_tg range tr = Some tr' ->
    tree_equal tr tr'.
  Proof.
    intros Lookup Protected Relations Access.
    eapply tree_equal_asymetric_read.
    + intros tg Ex. apply WF. assumption.
    + eassumption.
    + eassumption.
    + intros tg' it' loc Lookup' Range'.
      assert (initialized (item_lookup it loc) = PermInit) as acc_tg_is_init. {
        specialize (Relations acc_tg it loc Lookup Range').
        rewrite rel_dec_refl in Relations.
        destruct (initialized _); first reflexivity.
        tauto.
      }
      specialize (Relations tg' it' loc Lookup' Range').
      destruct (rel_dec _ _ _) as [[]|[]] eqn:Rel.
      - assumption.
      - assumption.
      - destruct (initialized (item_lookup it' loc)) eqn:Init; first done.
        (* Impossible: parents of the accessed tag must be more initialized. *)
        assert (ParentChildIn tg' acc_tg tr) as Parent. {
          rewrite /rel_dec in Rel.
          destruct (decide (ParentChildIn tg' acc_tg tr)); first assumption.
          destruct (decide _); discriminate.
        }
        pose proof (proj1 (every_child_ParentChildIn tg' _ tr WF (WF _ (proj1 Lookup')))
          (MoreInit tg')) as EveryInit.
        specialize (EveryInit it' (proj2 Lookup') acc_tg (WF _ (proj1 Lookup)) Parent).
        rewrite every_node_eqv_universal in EveryInit.
        specialize (EveryInit it).
        assert (itag it = acc_tg). { eapply tree_determined_specifies_tag; apply Lookup. }
        subst acc_tg.
        specialize (EveryInit (tree_lookup_to_exists_node _ _ Lookup) ltac:(reflexivity)).
        (* Now we finally have our contradiction: it' is lazy, it is init, and it' is more init than it *)
        specialize (EveryInit loc acc_tg_is_init).
        congruence.
      - assumption.
    + eassumption.
  Qed.


  Lemma trees_equal_read_all_protected_initialized trs1 trs1' trs2 cid
    (Hwf1 : wf_trees trs1)
    (Hwf2 : wf_trees trs2) :
    trees_equal trs1 trs2 →
    trees_read_all_protected_initialized C cid trs1 = Some trs1' →
    ∃ trs2', trees_read_all_protected_initialized C cid trs2 = Some trs2' ∧
      trees_equal trs1' trs2'.
  Proof.
    intros Heq Htrapi.
    epose proof (trees_read_all_protected_initialized_pointwise_1 _ _ _ _ Htrapi) as Htrapi1.
    odestruct (trees_read_all_protected_initialized_pointwise_2 _ trs2) as (trs2'&Htrs2').
    { intros k. destruct (Htrapi1 k) as (HH'&_). intros tr2 Htr2.
      specialize (Heq k). rewrite Htr2 in Heq. inversion Heq as [tr1 x1 Heqtr Htr1 e|]. subst x1.
      destruct (HH' tr1) as (tr1'&Htr1'&HHtr1'); first done.
      edestruct tree_equals_read_all_protected_initialized' as (tr2'&Htr2'&Heq').
      3: exact Heqtr. 3: exact HHtr1'. 1: by eapply Hwf1. 1: by eapply Hwf2.
      by eexists. }
    eexists; split; first done.
    intros k. specialize (Heq k).
    epose proof (trees_read_all_protected_initialized_pointwise_1 _ _ _ _ Htrs2' k) as (Htrapi2A&Htrapi2B).
    specialize (Htrapi1 k) as (Htrapi1A&Htrapi1B).
    inversion Heq as [tr1 tr2 Heqtr Htr1 Htr2|HNone1 HNone2]; last first.
    - rewrite Htrapi1B // Htrapi2B //. econstructor.
    - symmetry in Htr1,Htr2.
      destruct (Htrapi1A _ Htr1) as (tr1'&Htr1'&Hrapi1'). destruct (Htrapi2A _ Htr2) as (tr2'&Htr2'&Hrapi2').
      rewrite Htr1' Htr2'. econstructor.
      edestruct tree_equals_read_all_protected_initialized' as (tr2''&Htr2'u&Htr2'eq).
      4: exact Hrapi1'. 3: exact Heqtr. 1: by eapply Hwf1. 1: by eapply Hwf2.
      rewrite Hrapi2' in Htr2'u. injection Htr2'u as <-. done.
  Qed.

  Lemma rel_dec_equal_ParentChildIn_equiv tr1 tr2 :
    (∀ tg, tree_contains tg tr1 ↔ tree_contains tg tr2) →
    (∀ tg1 tg2, rel_dec tr1 tg1 tg2 = rel_dec tr2 tg1 tg2) →
    ∀ tg1 tg2, (ParentChildIn tg1 tg2 tr1 ↔ ParentChildIn tg1 tg2 tr2) ∧ (ImmediateParentChildIn tg1 tg2 tr1 ↔ ImmediateParentChildIn tg1 tg2 tr2).
  Proof.
    intros Hcont H tg1 tg2.
    specialize (H tg2 tg1).
    rewrite /rel_dec in H. destruct (decide (ParentChildIn tg1 tg2 tr1)) as [H1|H1]; last first.
    all: destruct (decide (ParentChildIn tg1 tg2 tr2)) as [H2|H2]; try done.
    all: split; first tauto.
    - split; intros H3%Immediate_is_StrictParentChild; exfalso. 1: eapply H1. 2: eapply H2. all: by right.
    - destruct (decide (tree_contains tg1 tr1)) as [Hin|Hnin]; last first.
      { split; intros _; eapply ImmediateParentChildIn_parent_not_in; last done.
        by setoid_rewrite <- Hcont. }
      destruct (decide (tg1 = tg2)) as [->|Hne].
      { split; intros H3%Immediate_is_StrictParentChild; exfalso; (eapply strict_parent_self_impossible; last done).
        2: rewrite <- Hcont. all: done. }
      destruct H1 as [?|H1]; first done.
      destruct H2 as [?|H2]; first done.
      rewrite decide_False in H. 2: { intros [?|H3]; first done. eapply strict_parent_self_impossible; first done. by eapply StrictParentChild_transitive. }
      rewrite (decide_False This) in H. 2: { intros [?|H3]; first done. setoid_rewrite Hcont in Hin. eapply strict_parent_self_impossible; first done. by eapply StrictParentChild_transitive. }
      destruct (decide (ImmediateParentChildIn tg1 tg2 tr1)), (decide (ImmediateParentChildIn tg1 tg2 tr2)); done.
  Qed.

  Lemma rel_dec_equal_ParentChildIn_equiv_lift tr1 tr2 :
    (∀ tg, tree_contains tg tr1 ↔ tree_contains tg tr2) →
    (∀ tg1 tg2, rel_dec tr1 tg1 tg2 = rel_dec tr2 tg1 tg2) →
    (∀ tg1 tg2, ParentChildIn tg1 tg2 tr1 ↔ ParentChildIn tg1 tg2 tr2) ∧
    (∀ tg1 tg2, StrictParentChildIn tg1 tg2 tr1 ↔ StrictParentChildIn tg1 tg2 tr2) ∧
    (∀ tg1 tg2, ImmediateParentChildIn tg1 tg2 tr1 ↔ ImmediateParentChildIn tg1 tg2 tr2).
  Proof.
    intros H1 H2.
    epose proof (rel_dec_equal_ParentChildIn_equiv _ _ H1 H2) as H. split_and!.
    1, 3: eapply H.
    intros tg1 tg2.
    destruct (decide (tree_contains tg1 tr1)) as [H3|H3]; last first.
    all: epose proof H3 as H3'; setoid_rewrite H1 in H3'.
    { split; intros _; rewrite /StrictParentChildIn; eapply every_subtree_eqv_universal.
      all: intros br Hex Htg; exfalso. 1: eapply H3'. 2: eapply H3.
      all: eapply exists_node_iff_exists_root.
      all: eapply exists_subtree_eqv_existential; eexists.
      all: split; first done; done.
      all: split; first eapply exists_node_iff_exists_root. }
    destruct (decide (tg1 = tg2)) as [->|Hne].
    { split; intros []%strict_parent_self_impossible; done. }
    destruct (H tg1 tg2) as ((HH1&HH2)&_).
    split; intros Hc.
    - destruct HH1 as [?|HH1]; try done. by right.
    - destruct HH2 as [?|HH2]; try done. by right.
  Qed.

  Lemma tree_equal_create_child tr1 tr2 tr1' tg_new tg_old pk rk cid ev2 :
    wf_tree tr1 → wf_tree tr2 →
    tree_items_compat_nexts tr1 tg_new ev2 → tree_items_compat_nexts tr2 tg_new ev2 →
    (cid < ev2)%nat →
    tree_contains tg_old tr1 →
    ¬ tree_contains tg_new tr1 →
    tree_equal tr1 tr2 →
    create_child C tg_old tg_new pk rk cid tr1 = Some tr1' →
    ∃ tr2', create_child C tg_old tg_new pk rk cid tr2 = Some tr2' ∧
      tree_equal tr1' tr2'.
  Proof.
    intros Hwf1 Hwf2 Hiwf1 Hiwf2 Hcidwf.
    rewrite /create_child.
    pose (create_new_item tg_new pk rk cid) as it_new. fold it_new.
    assert (itag it_new = tg_new) as Htgnew by done.
    intros Hcontains1 Hnotcont1 (H1&H2&H3) [= <-].
    assert (tg_old ≠ tg_new) as Htgsne by (intros ->; firstorder).
    pose proof Hcontains1 as Hcontains2. setoid_rewrite H1 in Hcontains2.
    pose proof Hnotcont1 as Hnotcont2. setoid_rewrite H1 in Hnotcont2.
    epose proof create_new_item_wf _ _ _ _ _ Hcidwf as Hitemwf.
    epose proof insert_child_wf C _ _ _ _ _ _ _ _ Hitemwf eq_refl Hiwf1 Hwf1 as (_&Hwf1').
    epose proof insert_child_wf C _ _ _ _ _ _ _ _ Hitemwf eq_refl Hiwf2 Hwf2 as (_&Hwf2').
    eexists. split; first done.
    pose proof (rel_dec_equal_ParentChildIn_equiv_lift _ _ H1 H2) as (H2A&H2B&H2C).
    split_and!. 
    - intros tg. destruct (decide (tg = tg_new)) as [->|Hne].
      + split; (intros _; eapply insert_true_produces_exists; [done|]); assumption.
      + split; (intros H%insert_false_infer_exists; last done); eapply insert_preserves_exists, H1, H.
    - eapply same_parent_childs_agree; intros tg tg'.
      + destruct (decide (tg = tg_new)) as [->|Hne], (decide (tg' = tg_new)) as [->|Hne'].
        * split; intros _; by left.
        * split; (intros [|Hc]; first done); exfalso; (eapply inserted_not_strict_parent; [| |exact Hc]; done).
        * destruct (decide (tg = tg_old)) as [->|Hneold].
          1: split; intros _; eapply insert_produces_ParentChild; done.
          split; (intros [|Hc]; first done).
          all: rewrite -Htgnew in Hc.
          all: eapply insert_produces_minimal_ParentChild in Hc; [|done..|by rewrite Htgnew].
          all: eapply ParentChild_transitive; last by eapply insert_produces_ParentChild.
          all: right; setoid_rewrite <- insert_eqv_strict_rel; [|done..].
          1: by setoid_rewrite <- H2B. 1: by setoid_rewrite H2B.
        * split; (intros [->|Hc]; [by left|right]).
          all: setoid_rewrite <- insert_eqv_strict_rel; [|done..].
          all: eapply H2B.
          all: setoid_rewrite -> insert_eqv_strict_rel; first done; done.
      + destruct (decide (tg = tg_new)) as [->|Hne], (decide (tg' = tg_new)) as [->|Hne'].
        * split; intros H; exfalso; (eapply immediate_parent_child_not_equal; [..|done|done]).
          1-2: eapply Hwf1'. 3-4: eapply Hwf2'.
          all: eapply insert_true_produces_exists; first done; done.
        * split; (intros Hc%Immediate_is_StrictParentChild); exfalso; (eapply inserted_not_strict_parent; [| |exact Hc]; done).
        * destruct (decide (tg = tg_old)) as [->|Hneold].
          1: split; intros _; rewrite -Htgnew; eapply insert_produces_ImmediateParentChild; done.
          destruct (decide (tree_contains tg tr1)) as [Htgin|Htgnin]; last first.
          { split; intros _; eapply ImmediateParentChildIn_parent_not_in.
            all: intros Hc%remove_false_preserves_exists; last done. 
            all: eapply Htgnin. 1: eapply H1. all: eapply Hc. }
          split; intros Hc; exfalso.
          all: rewrite -Htgnew in Hc; eapply ImmediateParentChild_of_insert_is_parent in Hc; [done|done|..|done].
          1: done. by eapply H1.
        * setoid_rewrite <- insert_eqv_imm_rel. 1: apply H2C.
          all: done.
    - intros tg Hcont.
      destruct (decide (tg = tg_new)) as [->|Hne].
      { exists it_new, it_new. split_and!.
        1-2: split; first by eapply insert_true_produces_exists.
        1-2: by eapply inserted_determined.
        eapply item_eq_up_to_C_reflexive. }
      eapply remove_false_preserves_exists in Hcont. 2: done.
      destruct (H3 tg Hcont) as (it1&it2&Hlu1&Hlu2&Hequptoc).
      exists it1, it2. split_and!.
      1-2: destruct Hlu1, Hlu2.
      1-2: split; first by eapply insert_preserves_exists.
      1-2: setoid_rewrite <- insert_true_preserves_every; done.
      intros l. specialize (Hequptoc l) as (Heq1&Heq2).
      split; first done.
      inversion Heq2 as [|pi im c1 c2 Hi1 Hi2 Hi3 Hi4 Hi5| |witness_tg ? ? Dis1 Dis2]; simplify_eq.
      + by econstructor 1.
      + destruct Hlu1 as (Hlu1A&Hlu1B), Hlu2 as (Hlu2A&Hlu2B).
        pose proof Hcont as Hcont2. setoid_rewrite H1 in Hcont2. econstructor 2. 1: done.
        * inversion Hi2 as [|tg_cs it_cs Hii1 Hii2 Hii3 Hii4 Hii5 Hii6]; simplify_eq; first by econstructor 1.
          destruct Hii2 as [HA HB].
          econstructor 2. 3-5: done.
          2: { split. 1: by eapply insert_preserves_exists.
               setoid_rewrite <- insert_true_preserves_every; first done.
               intros <-. done. }
          rewrite /rel_dec in Hii1|-*.
          destruct (decide (ParentChildIn tg_cs tg tr1)) as [|HnPC]; first done.
          destruct (decide (ParentChildIn tg tg_cs tr1)) as [|HnPC2]; first done.
          rewrite decide_False; first rewrite decide_False //; last first.
          -- intros [|Hc]; eapply HnPC; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
          -- intros [|Hc]; eapply HnPC2; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
        * inversion Hi3 as [|tg_cs it_cs Hii1 Hii2 Hii3 Hii4 Hii5 Hii6]; simplify_eq; first by econstructor 1.
          destruct Hii2 as [HA HB].
          econstructor 2. 3-5: done.
          2: { split. 1: by eapply insert_preserves_exists.
               setoid_rewrite <- insert_true_preserves_every; first done.
               intros <-. done. }
          rewrite /rel_dec in Hii1|-*.
          destruct (decide (ParentChildIn tg_cs tg tr2)) as [|HnPC]; first done.
          destruct (decide (ParentChildIn tg tg_cs tr2)) as [|HnPC2]; first done.
          rewrite decide_False; first rewrite decide_False //; last first.
          -- intros [|Hc]; eapply HnPC; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
          -- intros [|Hc]; eapply HnPC2; first by left. right.
             eapply insert_eqv_strict_rel; last exact Hc.
             1-2: by intros <-.
      + by econstructor 3.
      + econstructor 4.
        * eapply disabled_in_practice_create_child_irreversible; last reflexivity.
          -- lia.
          -- inversion Dis1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (tg_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
        * eapply disabled_in_practice_create_child_irreversible; last reflexivity.
          -- lia.
          -- inversion Dis1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (tg_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
        * auto.
        * auto.
  Qed.

  Lemma trees_equal_create_child trs1 trs2 trs1' blk tg_new tg_old pk rk cid nxtc :
    wf_trees trs1 → wf_trees trs2 →
    trees_compat_nexts trs1 tg_new nxtc → trees_compat_nexts trs2 tg_new nxtc →
    (cid < nxtc)%nat →
    trees_contain tg_old trs1 blk →
    ¬ trees_contain tg_new trs1 blk →
    trees_equal trs1 trs2 →
    apply_within_trees (create_child C tg_old tg_new pk rk cid) blk trs1 = Some trs1' →
    ∃ trs2', apply_within_trees (create_child C tg_old tg_new pk rk cid) blk trs2 = Some trs2' ∧
      trees_equal trs1' trs2'.
  Proof.
    intros Hwf1 Hwf2 Hiwf1 Hiwf2 Hcidwf Hcont Hncont Heq.
    intros (tr1&Htr1&(tr1'&Htr1'&[= <-])%bind_Some)%bind_Some.
    epose proof (Heq blk) as HeqblkI.
    inversion HeqblkI as [t1x tr2 Heqblk Heq1x Htr2|]; simplify_eq; last congruence.
    symmetry in Htr2. assert (t1x = tr1) as -> by congruence. clear Heq1x.
    eapply tree_equal_create_child in Htr1' as (tr2'&Htr2'&Heqtr).
    - eexists. rewrite /apply_within_trees /= Htr2 /=.
      split; first done.
      intros blk'. destruct (decide (blk = blk')) as [->|Hne].
      + rewrite !lookup_insert. econstructor. injection Htr2' as <-. apply Heqtr.
      + rewrite !lookup_insert_ne //.
    - by eapply Hwf1.
    - by eapply Hwf2.
    - by eapply Hiwf1.
    - by eapply Hiwf2.
    - done.
    - by rewrite /trees_contain /trees_at_block Htr1 in Hcont.
    - by rewrite /trees_contain /trees_at_block Htr1 in Hncont.
    - done.
  Qed.
    

End utils.

Section call_set.

  Lemma call_is_active_mono C1 C2 cid :
    C1 ⊆ C2 →
    call_is_active cid C1 →
    call_is_active cid C2.
  Proof.
    rewrite /call_is_active. set_solver.
  Qed.

  Lemma protector_is_active_mono C1 C2 prot :
    C1 ⊆ C2 →
    protector_is_active prot C1 →
    protector_is_active prot C2.
  Proof.
    intros Hss (c&Hc1&Hc2). eexists; split; by eauto using call_is_active_mono.
  Qed.

  Lemma pseudo_conflicted_mono C1 C2 tr tg off rc :
    C1 ⊆ C2 →
    pseudo_conflicted C1 tr tg off rc →
    pseudo_conflicted C2 tr tg off rc.
  Proof.
    induction 2.
    + econstructor 1.
    + econstructor 2; by eauto using protector_is_active_mono.
  Qed.

  Lemma protector_not_active_extend
    {p c C}
    (Hwf : ∀ c' : nat, protector_is_for_call c' p → (c' < c)%nat)
    (NoProt : ¬ protector_is_active p C)
    : ¬ protector_is_active p (C ∪ {[ c ]}).
  Proof.
    intros (cc&Hcc&[Hact|<-%elem_of_singleton]%elem_of_union).
    1: eapply NoProt; by eexists.
    apply Hwf in Hcc. lia.
  Qed.

  Lemma perm_eq_up_to_C_mono (C1 : gset nat) (nxtc : nat)
    tr1 tr2 tg l cid lp1 lp2 {nxtp} :
    (∀ cc, protector_is_for_call cc cid → (cc < nxtc)%nat) →
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    perm_eq_up_to_C C1 tr1 tr2 tg l cid lp1 lp2 →
    perm_eq_up_to_C (C1 ∪ {[ nxtc ]}) tr1 tr2 tg l cid lp1 lp2.
  Proof.
    intros Hwf Hwf_all1 Hwf_all2 Hwf_tr1 Hwf_tr2.
    induction 1 as [| |???? H|??? H1 H2 ? H].
    1: by econstructor.
    1: econstructor; try done. 1: eapply protector_is_active_mono; last done; set_solver.
    1-2: eapply pseudo_conflicted_mono; last done; set_solver.
    - econstructor 3; try done.
      apply protector_not_active_extend; assumption.
    - econstructor 4; try done.
      3: apply protector_not_active_extend; assumption.
      all: inversion H1; inversion H2.
      all: econstructor; try done.
      all: apply protector_not_active_extend.
      + unfold tree_items_compat_nexts in Hwf_all1.
        rewrite every_node_iff_every_lookup in Hwf_all1.
        * eapply Hwf_all1; eassumption.
        * unfold wf_tree, tree_items_unique in Hwf_tr1.
          intros tg0 Ex. specialize (Hwf_tr1 tg0 Ex).
          apply unique_lookup; assumption.
      + assumption.
      + unfold tree_items_compat_nexts in Hwf_all2.
        rewrite every_node_iff_every_lookup in Hwf_all2.
        * eapply Hwf_all2; eassumption.
        * unfold wf_tree, tree_items_unique in Hwf_tr2.
          intros tg0 Ex. specialize (Hwf_tr2 tg0 Ex).
          apply unique_lookup; assumption.
      + assumption.
  Qed.

  Lemma loc_eq_up_to_C_mono C1 tr1 tr2 tg it1 it2 nxtc nxtp l :
    item_wf it1 nxtp nxtc →
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    loc_eq_up_to_C C1 tr1 tr2 tg it1 it2 l →
    loc_eq_up_to_C (C1 ∪ {[ nxtc ]}) tr1 tr2 tg it1 it2 l.
  Proof.
    intros Hwf1 Hwf_all1 Hwf_all2 Hwf_tr1 Hwf_tr2.
    induction 1; econstructor; try done.
    eapply perm_eq_up_to_C_mono; last done.
    1: apply Hwf1.
    all: eassumption.
  Qed.

  Lemma item_eq_up_to_C_mono C1 tr1 tr2 tg it1 it2 nxtc nxtp :
    item_wf it1 nxtp nxtc →
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    item_eq_up_to_C C1 tr1 tr2 tg it1 it2 →
    item_eq_up_to_C (C1 ∪ {[ nxtc ]}) tr1 tr2 tg it1 it2.
  Proof.
    intros Hss Hwf_all1 Hwf_all2 Hwf_tr1 Hwf_tr2 H1 l.
    specialize (H1 l). by eapply loc_eq_up_to_C_mono.
  Qed.

  Lemma tree_equal_mono C1 tr1 tr2 nxtc nxtp :
    tree_items_compat_nexts tr1 nxtp nxtc →
    tree_items_compat_nexts tr2 nxtp nxtc →
    wf_tree tr1 →
    wf_tree tr2 →
    tree_equal C1 tr1 tr2 →
    tree_equal (C1 ∪ {[ nxtc ]}) tr1 tr2.
  Proof.
    intros Hss Hss2 Hwf_tr1 Hwf_tr2 (H1&H2&H3). do 2 (split; first done).
    intros tg (it1&it2&H4&H5&H6)%H3.
    exists it1, it2. split_and!; try done.
    eapply item_eq_up_to_C_mono; try done.
    setoid_rewrite every_node_eqv_universal in Hss.
    apply Hss, tree_lookup_to_exists_node.
    erewrite <-tree_lookup_correct_tag in H4; done.
  Qed.

  Lemma trees_equal_mono C1 trs1 trs2 nxtc nxtp :
    trees_compat_nexts trs1 nxtp nxtc →
    trees_compat_nexts trs2 nxtp nxtc →
    wf_trees trs1 →
    wf_trees trs2 ->
    trees_equal C1 trs1 trs2 →
    trees_equal (C1 ∪ {[ nxtc ]}) trs1 trs2.
  Proof.
    intros Hss Hss2 Hwf_trs1 Hwf_trs2 Heq blk. specialize (Heq blk). inversion Heq; simplify_eq.
    all: econstructor; try done.
    eapply tree_equal_mono; try done.
    + eapply Hss. done.
    + eapply Hss2. done.
    + eapply Hwf_trs1. done.
    + eapply Hwf_trs2. done.
  Qed.

End call_set.
