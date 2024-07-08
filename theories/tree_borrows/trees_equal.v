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

  Inductive pseudo_disabled (tr : tree item) (tg : tag) (l : Z) : permission → (option protector) → Prop :=
    | pseudo_disabled_disabled prot :
        (* a Disabled it also pseudo-disabled *)
        pseudo_disabled _ _ _ Disabled prot
    | pseudo_disabled_cousin_active tg_cous it_cous lp prot :
        rel_dec tr tg tg_cous = Foreign Cousin ->
        tree_lookup tr tg_cous it_cous ->
        protector_is_active it_cous.(iprot) C ->
        (item_lookup it_cous l) = mkPerm PermInit Active ->
        (* This is not allowed, since it actually survives foreign writes. *)
        (∀ c, lp ≠ Reserved InteriorMut c) ->
        pseudo_disabled _ _ _ lp prot
    .

  (* this implicitly requires (by state_wf) that it's not (protected and initialized) *)
  (* it also implies (via state_wf) that all children are not (protected and initialized) *)
  Inductive is_disabled (tr : tree item) (tg : tag) (l : Z) : lazy_permission → option protector → Prop :=
    | disabled_init prot : 
        is_disabled _ _ _ (mkPerm PermInit Disabled) prot
    | disabled_pseudo lp prot :
        pseudo_disabled tr tg l lp prot →
        is_disabled _ _ _ (mkPerm PermLazy lp) prot.

  Inductive disabled_in_practice (tr : tree item) (tg : tag) (witness : tag) (l : Z)
    : Prop :=
    | disabled_parent it_witness inclusive :
      (* Doesn't have to be immediate, just any parent is Disabled *)
      rel_dec tr tg witness = Child inclusive ->
      tree_lookup tr witness it_witness ->
      is_disabled tr witness l (item_lookup it_witness l) (iprot it_witness) ->
      disabled_in_practice tr tg witness l
    .

  Inductive frozen_in_practice (tr : tree item) (tg : tag) (witness : tag) (l : Z)
    : Prop :=
    (* This means being Reserved and having a parent that is exactly Frozen.
       [frozen_in_practice] behaves indistinguishably from Frozen.
       We could probably make [Frozen] and [frozen_in_practice] equivalent, but
       this shouldn't turn up in practice. *)
    | frozen_parent it_witness inclusive :
        rel_dec tr tg witness = Child inclusive ->
        tree_lookup tr witness it_witness ->
        (item_lookup it_witness l).(perm) = Frozen ->
        (* be initialized so that protectors trigger if applicable *)
        (item_lookup it_witness l).(initialized) = PermInit ->
        frozen_in_practice tr tg witness l
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
    | perm_eq_up_to_C_pseudo_disabled p1 p2 :
        (* A pseudo-disabled tag is one that's lazy, does not support child accesses due to a protected Active cousin,
           and will become Disabled on protector-end write for that cousin.
           It must be lazy, because a protected active has no non-disabled initialized cousins.
           Only exception: ¬prot Reserved InteriorMut, for which this case here does not apply. *)
        pseudo_disabled tr1 tg l p1 cid ->
        pseudo_disabled tr2 tg l p2 cid ->
        perm_eq_up_to_C tr1 tr2 tg l cid
          {| initialized := PermLazy; perm := p1 |}
          {| initialized := PermLazy; perm := p2 |}
    | perm_eq_up_to_C_disabled_parent witness_tg p p' :
        (* Finally if they have a Disabled parent we allow anything (unprotected) since
           nothing is possible through this tag anyway *)
        disabled_in_practice tr1 tg witness_tg l ->
        disabled_in_practice tr2 tg witness_tg l ->
        (* Added initialization requirement to help with the lemma [perm_eq_up_to_C_same_init] *)
        (initialized p = initialized p') ->
        perm_eq_up_to_C tr1 tr2 tg l cid p p'
    | perm_eq_up_to_C_frozen_parent ini im confl1 confl2 witness_tg :
        (* Important: they need the same interior mutability so that the protectors
           trigger under exactly the same conditions *)
        frozen_in_practice tr1 tg witness_tg l ->
        frozen_in_practice tr2 tg witness_tg l ->
        perm_eq_up_to_C tr1 tr2 tg l cid
          {| initialized := ini; perm := Reserved im confl1 |}
          {| initialized := ini; perm := Reserved im confl2 |}
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
    + econstructor 1.
    + econstructor 2; eassumption.
    + econstructor 3; eassumption.
    + econstructor 4; eassumption.
    + econstructor 5; try eassumption.
      done.
    + econstructor 6; eassumption.
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

  Lemma pseudo_disabled_allows_same_access
    {tr1 tr2 tg l p1 p2 kind rel isprot acc_tg range it1 b}
    (* Main hypotheses *)
    (Confl1 : pseudo_disabled tr1 tg l p1 (iprot it1))
    (Confl2 : pseudo_disabled tr2 tg l p2 (iprot it1))
    (AccEx : tree_unique acc_tg tr1)
    (TgEx : tree_unique tg tr1)
    (* Auxiliary stuff to bind the local access to the global success for the pseudo conflicted case *)
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (ProtSpec : isprot = bool_decide (protector_is_active (iprot it1) C))
    (RelSpec : rel = rel_dec tr1 acc_tg tg)
    (PermSpec : item_lookup it1 l = {| initialized := PermLazy; perm := p1 |})
    (InRange : range'_contains range l)
    : is_Some
         (apply_access_perm kind rel isprot
            {| initialized := PermLazy; perm := p1 |})
    -> is_Some
         (apply_access_perm kind rel isprot
            {| initialized := PermLazy; perm := p2 |}).
  Proof.
    rewrite /apply_access_perm /apply_access_perm_inner; simpl.
    destruct rel; last first.
    - inversion Confl1 as [H1 H2|tg_cs it_cs X1 X2 Hcs Hlu Hluact Hpp XX X3]; simplify_eq.
      1: destruct kind; simpl; intros [? [=]].
      exfalso. eapply apply_access_success_condition in GlobalSuccess.
      eapply every_node_eqv_universal in GlobalSuccess.
      2: eapply tree_lookup_to_exists_node, Hlu.
      rewrite /item_apply_access /permissions_apply_range' in GlobalSuccess.
      erewrite is_Some_ignore_bind in GlobalSuccess.
      eapply mem_apply_range'_success_condition in GlobalSuccess.
      2: exact InRange.
      rewrite /rel_dec in GlobalSuccess.
      assert (itag it_cs = tg_cs) as Hcstg by by eapply tree_lookup_correct_tag.
      rewrite decide_False in GlobalSuccess.
      2: { intros HPC. eapply cousins_have_disjoint_children.
           4: exact Hcs. 2: done. 1: exact AccEx.
           1: eapply GloballyUnique1, Hlu. 2: by subst.
           rewrite /rel_dec in RelSpec. destruct decide in RelSpec; done. }
      rewrite decide_False in GlobalSuccess.
      2: { intros HPC. rewrite /rel_dec in RelSpec Hcs.
           destruct decide as [HP1|?] in RelSpec; try done.
           destruct decide as [?|HnP1] in Hcs; try done.
           destruct decide as [?|HnP2] in Hcs; try done.
           eapply HnP2. eapply ParentChild_transitive.
           1: exact HP1. subst. done. }
      rewrite /item_lookup in Hpp.
      rewrite Hpp bool_decide_true // in GlobalSuccess.
      rewrite maybe_non_children_only_no_effect // in GlobalSuccess.
      destruct kind; destruct GlobalSuccess as [x [=]].
    - rewrite /=. intros _. destruct kind, isprot, p2 as [[][]| | |]; simpl; done.
  Qed.

  (* FIXME: move this elsewhere *)
  Lemma if_fun_absorb_args {X Y} {b : bool} {x : X} {f g : X -> Y} :
    (if b then f else g) x = if b then f x else g x.
  Proof. destruct b; reflexivity. Qed.

  Lemma rel_dec_child_transitive
    {tr tg1 tg2 tg3 incl1 incl2}
    : rel_dec tr tg1 tg2 = Child incl1 ->
      rel_dec tr tg2 tg3 = Child incl2 ->
      exists incl3, rel_dec tr tg1 tg3 = Child incl3.
  Proof.
    intros Rel12 Rel23.
    unfold rel_dec in *.
    destruct (decide (ParentChildIn tg2 tg1 tr)); last congruence.
    destruct (decide (ParentChildIn tg3 tg2 tr)); last congruence.
    assert (ParentChildIn tg3 tg1 tr) by (eapply ParentChild_transitive; eassumption).
    eexists.
    destruct (decide (ParentChildIn tg3 tg1 tr)); last contradiction.
    f_equal.
  Qed.

  Lemma frozen_in_practice_rejects_child_write
    {tr tg witness l b acc_tg range}
    (InRange : range'_contains range l)
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    (Frz : frozen_in_practice tr tg witness l)
    (Acc : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm AccessWrite)) C acc_tg range tr))
    (Rel : exists x, rel_dec tr acc_tg tg = Child x)
    : False.
  Proof.
    inversion Frz as [it_witness ? Rel' Lkup Perm].
    rewrite -apply_access_success_condition in Acc.
    rewrite every_node_iff_every_lookup in Acc. 2: {
      intros tg0 Ex0. apply unique_lookup. apply GloballyUnique. assumption.
    }
    specialize (Acc _ _ Lkup).
    assert (exists x, rel_dec tr acc_tg witness = Child x) as FullRel. 1: {
      destruct Rel as [? Rel].
      eapply rel_dec_child_transitive; eassumption.
    }
    destruct FullRel as [? FullRel].
    assert (itag it_witness = witness) as WitnessTg. {
      eapply tree_determined_specifies_tag; apply Lkup.
    }
    rewrite WitnessTg FullRel in Acc.
    unfold item_apply_access, maybe_non_children_only in Acc.
    unfold is_Some in Acc.
    destruct Acc as [? Acc].
    rewrite bind_Some in Acc.
    destruct Acc as [? [Acc Res]].
    injection Res; clear Res; intros; subst.
    unfold permissions_apply_range' in Acc.
    pose proof (mk_is_Some _ _ Acc) as AccSome; clear Acc.
    rewrite -mem_apply_range'_success_condition in AccSome.
    specialize (AccSome l InRange).
    do 4 rewrite if_fun_absorb_args in AccSome.
    unfold nonchildren_only in AccSome.
    rewrite Tauto.if_same in AccSome.
    unfold apply_access_perm, apply_access_perm_inner in AccSome.
    rewrite Perm in AccSome.
    simpl in AccSome.
    inversion AccSome; congruence.
  Qed.

  Lemma loc_eq_up_to_C_allows_same_access
    {tr1 tr2 tg it1 it2 l kind acc_tg range b}
    (Tg1 : itag it1 = tg)
    (Tg2 : itag it2 = tg)
    (UnqAcc : tree_unique acc_tg tr1)
    (UnqAcc2 : tree_unique acc_tg tr2)
    (Ex1 : tree_unique tg tr1)
    (Ex2 : tree_lookup tr2 tg it2)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
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
      |p1 p2 Confl1 Confl2 Lookup1 Lookup2
      |witness_tg ?? Dis1 Dis2 Lookup1 Lookup2
      |ini ??? witness_tg Frz1 Frz2 Lookup1 Lookup2
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
    - rewrite Lookup2.
      rewrite -Lookup1 in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq.
      rewrite Heq. rewrite -Lookup2.
      eapply (pseudo_disabled_allows_same_access Confl1 Confl2 UnqAcc Ex1 GloballyUnique1 GlobalSuccess).
      + rewrite -EqProt; reflexivity.
      + rewrite SameRel -Tg2 //=.
      + rewrite /item_lookup Lookup1 //=.
      + exact InRange.
      + rewrite Tg1 -Tg2 SameRel EqProt Heq // in Acc1.
    - (* FIXME: there has to be a shorter proof *)
      (* This has to be a foreign access *)
      destruct (rel_dec tr1 acc_tg (itag it1)) eqn:AccRel; last first.
      + (* If it's a child access then it's also a child access for the Disabled parent. *)
        inversion Dis1 as [it_witness ? RelWitness LookupWitness DisWitnessPre].
        destruct (decide (perm (item_lookup it_witness l) = Disabled)) as [Hdis|HNonDis]; simplify_eq.
        * rewrite <- apply_access_success_condition in GlobalSuccess.
          rewrite every_node_iff_every_lookup in GlobalSuccess. 2: {
            intros tg0 Ex0. apply unique_lookup. apply GloballyUnique1. assumption.
          }
          specialize (GlobalSuccess _ _ LookupWitness).
          pose proof (tree_determined_specifies_tag _ _ _ (proj1 LookupWitness) (proj2 LookupWitness))
            as WitnessTg.
          subst witness_tg.
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
          unfold item_lookup in Hdis.
          rewrite /maybe_non_children_only in PermissionApply.
          rewrite /nonchildren_only /= in PermissionApply.
          repeat rewrite if_fun_absorb_args in PermissionApply.
          rewrite Tauto.if_same in PermissionApply.
          rewrite /apply_access_perm /= in PermissionApply.
          destruct PermissionApply as [tmp_lazy PermissionApply].
          rewrite bind_Some in PermissionApply.
          destruct PermissionApply as [tmp_perm [ApplyAccessInner ValidateProt]].
          rewrite Hdis in ApplyAccessInner.
          rewrite /apply_access_perm_inner in ApplyAccessInner.
          case_match; discriminate.
        * inversion DisWitnessPre as [HX DisWitness|lp HDis Hlookup HX]; simplify_eq.
          1: rewrite -DisWitness in HNonDis; done.
          inversion Hlookup as [HX1 HX2|tg_w2 it_w2 x1 x2 Hcs2 Hlu2 Hprot2 Hperm2 Hlp]; simplify_eq.
          1: rewrite -HX // in HNonDis.
          rewrite <- apply_access_success_condition in GlobalSuccess.
          rewrite every_node_iff_every_lookup in GlobalSuccess. 2: {
            intros tg0 Ex0. apply unique_lookup. apply GloballyUnique1. assumption.
          }
          specialize (GlobalSuccess _ _ Hlu2).
          pose proof (tree_determined_specifies_tag _ _ _ (proj1 Hlu2) (proj2 Hlu2))
            as <-.
          rewrite /rel_dec in RelWitness.
          destruct decide as [HPC1|] in RelWitness; last done. clear RelWitness.
          rewrite /rel_dec in AccRel.
          destruct decide as [HPC2|] in AccRel; last done. clear AccRel.
          rewrite /rel_dec decide_False in GlobalSuccess; last first.
          { intros HH. exfalso. eapply cousins_have_disjoint_children. 4: exact Hcs2.
            5: exact HH. 4: eapply ParentChild_transitive; eassumption.
            1: done. all: eapply GloballyUnique1. 2: eapply Hlu2. eapply LookupWitness. }
          rewrite decide_False in GlobalSuccess; last first.
          { intros HH. rewrite /rel_dec in Hcs2.
            destruct decide as [|HHH] in Hcs2; first done.
            destruct decide as [|HHH2] in Hcs2; first done.
            eapply HHH2. do 3 (eapply ParentChild_transitive; first done). by left. }
          exfalso. rewrite /item_apply_access in GlobalSuccess.
          rewrite is_Some_ignore_bind in GlobalSuccess.
          eapply mem_apply_range'_success_condition in GlobalSuccess. 2: done.
          rewrite maybe_non_children_only_no_effect // in GlobalSuccess.
          rewrite /item_lookup in Hperm2. rewrite Hperm2 in GlobalSuccess.
          rewrite bool_decide_true // in GlobalSuccess.
          destruct kind; cbv in GlobalSuccess; by destruct GlobalSuccess.
      + rewrite <- EqProt.
        destruct (bool_decide (protector_is_active (iprot it1) C)) eqn:Heq; last first.
        { rewrite Tg2 -Tg1 -SameRel AccRel.
          rewrite /maybe_non_children_only /nonchildren_only.
          repeat rewrite if_fun_absorb_args.
          repeat case_match; first done.
          all: rewrite /apply_access_perm /apply_access_perm_inner //=.
          all: repeat case_match; done. }
        rewrite Tg2 -Tg1 -SameRel AccRel.
        rewrite /maybe_non_children_only /nonchildren_only.
        repeat rewrite if_fun_absorb_args.
        inversion Dis2 as [it_witness ? RelWitness LookupWitness DisWitnessPre].
        (* we are protected. this means we are not initalized by state_wf *)
        assert (initialized (item_lookup it2 l) = PermLazy) as HH.
        1: inversion DisWitnessPre as [HX DisWitness|lp HX HDis Hlookup]; simplify_eq.
        { specialize (ProtParentsNonDis witness_tg). eapply every_child_ParentChildIn in ProtParentsNonDis.
          2: done. 2: eapply GloballyUnique2, LookupWitness. 2: eapply LookupWitness. 2: eapply GloballyUnique2, Ex2.
          2: rewrite /rel_dec in RelWitness; by destruct (decide (ParentChildIn witness_tg (itag it1) tr2)).
          setoid_rewrite every_node_eqv_universal in ProtParentsNonDis.
          ospecialize (ProtParentsNonDis it2 _ _).
          1: eapply exists_determined_exists; eapply Ex2. 1: by eapply tree_lookup_correct_tag.
          rewrite /item_protected_all_parents_not_disabled in ProtParentsNonDis.
          ospecialize (ProtParentsNonDis l). destruct (initialized (item_lookup it2 l)); last done.
          rewrite -EqProt -DisWitness in ProtParentsNonDis. ospecialize (ProtParentsNonDis _ _).
          1: done. 1: by eapply bool_decide_eq_true_1. 1: done. }
        { specialize (ParentsMoreInit witness_tg). eapply every_child_ParentChildIn in ParentsMoreInit.
          2: done. 2: eapply GloballyUnique2, LookupWitness. 2: eapply LookupWitness. 2: eapply GloballyUnique2, Ex2.
          2: rewrite /rel_dec in RelWitness; by destruct (decide (ParentChildIn witness_tg (itag it1) tr2)).
          setoid_rewrite every_node_eqv_universal in ParentsMoreInit.
          ospecialize (ParentsMoreInit it2 _ _).
          1: eapply exists_determined_exists; eapply Ex2. 1: by eapply tree_lookup_correct_tag.
          ospecialize (ParentsMoreInit l). destruct (initialized (item_lookup it2 l)); last done.
          rewrite -Hlookup in ParentsMoreInit. ospecialize (ParentsMoreInit _).
          1: done. 1: done. }
        all: rewrite /apply_access_perm /apply_access_perm_inner HH //=.
        all: repeat case_match; done.
    - (* Frozen in practice case.
         Before we do the usual manipulations we make both the left and right access use
         the same [rel_dec] so that the [maybe_non_children_only] case distinction works
         on both simultaneously. *)
      rewrite SameRel in Acc1.
      edestruct maybe_non_children_only_effect_or_nop as [Heq|Heq].
      2: by erewrite Heq. (* Noop case, easy. *)
      rewrite Heq.
      rewrite Tg1 -Tg2 Heq in Acc1.
      destruct kind, (rel_dec tr2 _ _) eqn:Rel.
      + (* Foreign read is allowed *)
        unfold apply_access_perm, apply_access_perm_inner.
        repeat (case_match; simpl; try auto).
      + (* Child read is allowed *)
        unfold apply_access_perm, apply_access_perm_inner.
        repeat (case_match; simpl; try auto).
      + (* Foreign write is allowed, except when there is a protector.
           Once we eliminate all other cases we'll have to prove that the protector is inactive by
           using the left tree in which the access suceeded. *)
        unfold apply_access_perm, apply_access_perm_inner.
        repeat (case_match; simpl; try auto).
        (* Now we have a goal that is definitely not provable, but we have gained
           a hypothesis [protector_is_active] in the context. We can derive a contradiction. *)
        all: exfalso.
        all: unfold apply_access_perm, apply_access_perm_inner in Acc1.
        all: repeat (case_match; simpl in Acc1; try auto).
        all: try (inversion Acc1; congruence).
        (* We have all the elements of the contradiction, but a bit of rewriting is necessary
           to get them in a shape that is obviously conflicting.
           At that point there are two kinds of goals
           - some where the protector is active only on one side, solve them using [EqProt],
           - others whene [initialized] returns inconsistent results, solve them by
             unifying the same [ini] everywhere. *)
        all: repeat multimatch goal with
        | H : bool_decide _ = true |- _ => pose proof (bool_decide_eq_true_1 _ H); clear H
        | H : bool_decide _ = false |- _ => pose proof (bool_decide_eq_false_1 _ H); clear H
        | H : context [ iprot _ ] |- _ => rewrite EqProt in H
        | |- _ => try contradiction
        end.
        all: assert (initialized (item_lookup it1 l) = ini) as Ini1 by (rewrite -Lookup1; done).
        all: simpl in *; congruence.
      + (* Child write is necessarily UB due to the Frozen parent *)
        exfalso.
        eapply frozen_in_practice_rejects_child_write. 4: exact GlobalSuccess.
        * eassumption.
        * eassumption.
        * eassumption.
        * eexists. rewrite SameRel. rewrite -Tg2. apply Rel.
  Qed.

  Lemma item_eq_up_to_C_allows_same_access (b:bool)
    {tr1 tr2 tg it1 it2 kind acc_tg range}
    (Tg1 : itag it1 = tg)
    (Tg2 : itag it2 = tg)
    (UnqAcc : tree_unique acc_tg tr1)
    (UnqAcc2 : tree_unique acc_tg tr2)
    (Ex1 : tree_unique tg tr1)
    (Ex2 : tree_lookup tr2 tg it2)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2)
    (GlobalSuccess : is_Some (tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1))
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
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
    eapply (loc_eq_up_to_C_allows_same_access Tg1 Tg2 UnqAcc UnqAcc2 Ex1 Ex2 SameRel); done.
  Qed.

  Lemma tree_equal_allows_same_access_maybe_nonchildren_only (b:bool)
    {tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2) :
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
    eapply (item_eq_up_to_C_allows_same_access b).
    - erewrite tree_determined_specifies_tag. 2,3: eapply Lookup1. reflexivity.
    - erewrite tree_determined_specifies_tag. 2,3: eapply Lookup2. reflexivity.
    - apply UnqAcc.
    - eapply GloballyUnique2. destruct Eq as (H1&H2&H3). eapply H1. by eapply unique_exists.
    - apply GloballyUnique1. apply Lookup1.
    - done. 
    - eassumption.
    - eapply ProtParentsNonDis.
    - done.
    - apply Acc1.
    - exact GloballyUnique1.
    - exact GloballyUnique2.
    - done.
    - eapply Every1; eassumption.
  Qed.

  Lemma tree_equal_allows_same_access
    {tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_access kind C acc_tg range tr1) ->
    is_Some (memory_access kind C acc_tg range tr2).
  Proof.
    by eapply (tree_equal_allows_same_access_maybe_nonchildren_only false).
  Qed. 

  Lemma tree_equal_allows_same_access_nonchildren_only
    {tr1 tr2 kind acc_tg range}
    (GloballyUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (ParentsMoreInit : parents_more_init tr2) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_access_nonchildren_only kind C acc_tg range tr1) ->
    is_Some (memory_access_nonchildren_only kind C acc_tg range tr2).
  Proof.
    by eapply (tree_equal_allows_same_access_maybe_nonchildren_only true).
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

  Lemma access_preserves_pseudo_disabled lp pr (b:bool)
    {tr tg l kind acc_tg range tr'} :
    pseudo_disabled tr tg l lp pr ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr' ->
    pseudo_disabled tr' tg l lp pr.
  Proof.
    intros PseudoC Acc.
    inversion PseudoC as [|tg_cous it_cous X1 X2 cous_rel [cous_ex cous_det] cous_nondis cous_init Hextra]; simplify_eq.
    1: econstructor 1.
    destruct (apply_access_spec_per_node cous_ex cous_det Acc)
          as (cous' & cous'_spec & cous'_ex & cous'_det).
    symmetry in cous'_spec.
    rewrite bind_Some in cous'_spec.
    destruct cous'_spec as (perms' & perms'_spec & cous'_build).
    injection cous'_build; intros; subst; clear cous'_build.
    pose proof (mem_apply_range'_spec _ _ l _ _ perms'_spec) as effect_at_l.
    destruct (decide _); last first.
    + (* out of range is a lot easier *)
      econstructor 2.
      * erewrite <- access_same_rel_dec; eassumption.
      * split; eassumption.
      * eassumption.
      * rewrite /item_lookup /= effect_at_l. assumption.
      * done.
    + (* within range. Big case analysis incoming. *)
      destruct effect_at_l as (perm' & perm'_lookup & perm'_spec).
      rewrite /item_lookup in cous_init. rewrite cous_init in perm'_spec.
      rewrite bool_decide_true in perm'_spec. 2: done.
      destruct b, kind, rel_dec as [[]|] in perm'_spec; cbv in perm'_spec.
      all: try discriminate perm'_spec.
      all: injection perm'_spec as <-.
      all: econstructor 2;
           [ erewrite <- access_same_rel_dec; eassumption
           | split; eassumption
           | done
           | rewrite /item_lookup perm'_lookup /= //
           | done
           ].
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

  Lemma is_disabled_tree_apply_access_child
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Dis : is_disabled tr tg loc (item_lookup it loc) (iprot it))
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Inside : range'_contains range loc)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : ¬ ParentChildIn tg acc_tg tr.
  Proof.
    intros HPC.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    eapply tree_lookup_correct_tag in Lookup as HH; subst tg.
    rewrite decide_True // in LocSpec.
    destruct LocSpec as (v&Hv&HHv).
    destruct (decide (perm (item_lookup it loc) = Disabled)) as [Hdis|Hnondis].
    { rewrite /rel_dec decide_True // in HHv.
      rewrite maybe_non_children_only_no_effect // in HHv.
      rewrite /apply_access_perm /apply_access_perm_inner /= Hdis in HHv.
      by destruct kind. }
    inversion Dis as [X1 Hlu X2|lp X1 Hdis Hlu X2]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    inversion Hdis as [X1 X2 X3|tg_cs it_cs X1 X2 Hcs Hlucs Hprotcs Hppcs Hcsfoo X3 X4]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    destruct (apply_access_spec_per_node (proj1 Hlucs) (proj2 Hlucs) Acc) as [itcs' [Speccs' Hlucs']].
    symmetry in Speccs'.
    rewrite bind_Some in Speccs'. destruct Speccs' as [tmpcs [PermsAppcs [= <-]]].
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsAppcs) as LocSpeccs.
    rewrite decide_True // in LocSpeccs.
    destruct LocSpeccs as [valcs [Hvcs HHvcs]].
    rewrite /rel_dec in HHvcs.
    eapply tree_lookup_correct_tag in Hlucs' as HH; subst tg_cs.
    rewrite decide_False in HHvcs; last first.
    { intros HnPCI1. eapply cousins_have_disjoint_children in Hcs. 5: done. 5: done.
      1: done. all: simpl; eapply Uni. 1: done. 1: apply Lookup. 1: eapply Hlucs. }
    rewrite decide_False in HHvcs; last first.
    { intros HnPCI1.
      rewrite /rel_dec in Hcs.
      destruct decide as [?|HNP2] in Hcs; first done.
      destruct decide as [?|HNP3] in Hcs; first done.
      eapply HNP3; simpl. eapply ParentChild_transitive.
      1: done. done. }
    rewrite maybe_non_children_only_no_effect // in HHvcs.
    rewrite bool_decide_true // in HHvcs.
    rewrite /item_lookup in Hppcs.
    rewrite Hppcs in HHvcs. destruct kind; done.
  Qed.

  Lemma is_disabled_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Dis : is_disabled tr tg loc (item_lookup it loc) (iprot it))
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it' ∧ iprot it = iprot it' ∧
        is_disabled tr' tg loc (item_lookup it' loc) (iprot it').
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    injection Build; intros; subst; clear Build. split; first done.
    destruct (decide (perm (item_lookup it loc) = Disabled)) as [Hdis|Hnondis].
    { eapply disabled_tree_apply_access_irreversible in Hdis as (it'&Htr'&Hit'). 2-3: done.
      eapply tree_determined_unify in Det'. 2: done. 2: apply Htr'.
      destruct (item_lookup it' loc) as [[] pp] eqn:Hini; subst it'.
      all: rewrite Hini. all: simpl in Hit'; subst pp.
      1: econstructor 1. 1: econstructor 2. econstructor 1. }
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec.
    inversion Dis as [X1 Hlu X2|lp X1 Hdis Hlu X2]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    inversion Hdis as [X1 X2 X3|tg_cs it_cs X1 X2 Hcs Hlucs Hprotcs Hppcs Hcsfoo X3 X4]; simplify_eq.
    1: rewrite -Hlu in Hnondis; done.
    destruct (apply_access_spec_per_node (proj1 Hlucs) (proj2 Hlucs) Acc) as [itcs' [Speccs' Hlucs']].
    symmetry in Speccs'.
    rewrite bind_Some in Speccs'. destruct Speccs' as [tmpcs [PermsAppcs [= <-]]].
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsAppcs) as LocSpeccs.
    destruct (decide _) as [In|Out]; last first.
    + rewrite /item_lookup /= LocSpec.
      rewrite /item_lookup in Hlu. rewrite -Hlu.
      econstructor. eapply access_preserves_pseudo_disabled. 1: done. done.
    + destruct LocSpec as [val [LookupVal SpecVal]].
      destruct LocSpeccs as [valcs [LookupValcs SpecValcs]].
      rewrite /rel_dec in SpecVal.
      eapply tree_lookup_correct_tag in Lookup as HH; subst tg.
      eapply tree_lookup_correct_tag in Hlucs' as HH; subst tg_cs.
      rewrite decide_False in SpecVal.
      2: { eapply is_disabled_tree_apply_access_child. 6: done. 2: done. all: done. }
      edestruct maybe_non_children_only_effect_or_nop as [Heff|Heff];
      erewrite Heff in SpecVal; clear Heff.
      2: { injection SpecVal as <-. simpl.
           rewrite /item_lookup /= in Hlu|-*.
           rewrite LookupVal /= -Hlu.
           econstructor 2. eapply access_preserves_pseudo_disabled; last done.
           done. }
      rewrite /item_lookup in Hlu. rewrite -Hlu in SpecVal.
      rewrite /apply_access_perm /apply_access_perm_inner most_init_comm /= in SpecVal.
      destruct kind, bool_decide eqn:Hbdc, lp as [[][]| | |] eqn:Hpm in SpecVal.
      all: simpl in SpecVal. all: try discriminate SpecVal.
      all: injection SpecVal as <-.
      all: rewrite /= /item_lookup /= LookupVal /=.
      all: econstructor 2.
      all: eapply access_preserves_pseudo_disabled; last done.
      all: econstructor; [exact Hcs|exact Hlucs|exact Hprotcs|exact Hppcs|].
      all: intros c [=]; subst c.
      all: subst lp; eapply Hcsfoo; done.
  Qed.

  Lemma create_child_irreversible
    {tr tr' tg tg_old tg_new it pk rk cid}
    (Lookup : tree_lookup tr tg it)
    (Fresh : tg_new ≠ tg)
    (Ins : create_child C tg_old tg_new pk rk cid tr = Some tr')
    : tree_lookup tr' tg it.
  Proof.
    unfold create_child in Ins.
    injection Ins; clear Ins; intro Ins.
    subst tr'.
    destruct Lookup as [Ex Det]. split.
    - apply insert_preserves_exists; assumption.
    - apply insert_true_preserves_every; last assumption.
      intro SameTg.
      rewrite /create_new_item //= in SameTg.
  Qed.

  Definition becomes_frozen (kind : access_kind) (range : Z * nat) (loc : Z) (b:bool) tr acc_tg it_tg: Prop :=
    if decide (range'_contains range loc) then kind = AccessRead ∨ (∃ k, b = true ∧ rel_dec tr acc_tg it_tg = Foreign (Parent k)) else True.

  Lemma frozen_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range loc b it}
    (Lookup : tree_lookup tr tg it)
    (Frz : (item_lookup it loc).(perm) = Frozen)
    (Ini : (item_lookup it loc).(initialized) = PermInit)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : exists it',
        tree_lookup tr' tg it'
        /\ let k := (item_lookup it' loc) in let bf := becomes_frozen kind range loc b tr acc_tg (itag it) in
            k.(initialized) = PermInit
           /\ (k.(perm) = Frozen ∧ bf ∨ (k.(perm) = Disabled ∧ ¬ bf ∧ ¬ protector_is_active it'.(iprot) C)).
  Proof.
    destruct (apply_access_spec_per_node (proj1 Lookup) (proj2 Lookup) Acc) as [it' [Spec' [Ex' Det']]].
    exists it'.
    split; first done.
    symmetry in Spec'.
    rewrite bind_Some in Spec'. destruct Spec' as [tmp [PermsApp Build]].
    intros k bf.
    injection Build; intros; subst; clear Build.
    pose proof (mem_apply_range'_spec _ _ loc _ _ PermsApp) as LocSpec. subst bf. rewrite /becomes_frozen.
    destruct (decide _); last first.
    + subst k. rewrite /item_lookup /= LocSpec Frz Ini //. split; first done. by left.
    + destruct LocSpec as [val [LookupVal SpecVal]]. subst k.
      rewrite /item_lookup LookupVal /=.
      rewrite /maybe_non_children_only /nonchildren_only in SpecVal.
      repeat case_match.
      1: { injection SpecVal; intros; subst; split; first done. left. split; first done. eauto. }
      all: rewrite /apply_access_perm /apply_access_perm_inner /= in SpecVal.
      all: rewrite Frz /= Ini /= in SpecVal.
      all: repeat case_match; simpl in *; try congruence.
      all: injection SpecVal; intros; subst; simpl; split; first done.
      all: first [ left; split; first done; eauto | right; split; first done; split ].
      2, 4: by eapply bool_decide_eq_false_1.
      all: intros [[=]|(k&Hb&Hk)]; congruence. 
  Qed.

  Lemma disabled_in_practice_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range witness loc b}
    (Dis : disabled_in_practice tr tg witness loc)
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : disabled_in_practice tr' tg witness loc.
  Proof.
    inversion Dis as [?? Rel Lookup Perm].
    destruct (is_disabled_tree_apply_access_irreversible Lookup Perm Cont Uni Acc) as [it' [Lookup' Perm']].
    econstructor.
    + erewrite <- access_same_rel_dec; eassumption.
    + apply Lookup'.
    + apply Perm'.
  Qed.

  Lemma frozen_in_practice_tree_apply_access_irreversible
    {tr tr' tg acc_tg kind range witness loc b}
    (Frz : frozen_in_practice tr tg witness loc)
    (Cont : tree_contains acc_tg tr)
    (Uni : wf_tree tr)
    (Acc : tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr = Some tr')
    : let bf := becomes_frozen kind range loc b tr acc_tg witness in
      (frozen_in_practice tr' tg witness loc ∧ bf) ∨ (disabled_in_practice tr' tg witness loc ∧ ¬ bf).
  Proof.
    inversion Frz as [it_witness incl Rel Lookup Perm Init].
    assert (itag it_witness = witness) as <- by by eapply tree_lookup_correct_tag.
    destruct (frozen_tree_apply_access_irreversible Lookup Perm Init Acc) as [it' [Lookup' [Init' [[Perm' BF]|[Perm' [BF NoProt]]]]]].
    - left. split; last done. econstructor.
      + erewrite <- access_same_rel_dec; eassumption.
      + apply Lookup'.
      + apply Perm'.
      + apply Init'.
    - right. split; last done. econstructor.
      + erewrite <- access_same_rel_dec; eassumption.
      + apply Lookup'.
      + destruct (item_lookup it' loc) as [lp pp]; simpl in Init',Perm'; subst. econstructor.
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

  Lemma disabled_in_practice_create_child_irreversible
    {tr tr' tg tg_old tg_new pk rk cid witness loc}
    (Ne : tg_new ≠ tg)
    (Ne' : tg_new ≠ witness)
    (Nc : ¬ tree_contains tg_new tr)
    (Dis : disabled_in_practice tr tg witness loc)
    (Ins : create_child C tg_old tg_new pk rk cid tr = Some tr')
    : disabled_in_practice tr' tg witness loc.
  Proof.
    inversion Dis as [it_witness ? Rel Lookup Perm].
    econstructor.
    - erewrite <-create_child_same_rel_dec. 1: exact Rel. 3: done. 1-2: done.
    - eapply create_child_irreversible.
      1: done. 2: done. done.
    - inversion Perm as [|lp X H1 H2 X2]; simplify_eq. 1: econstructor 1.
      econstructor 2. inversion H1 as [|tgcs itcs X1 X2 H1' H2' H3 H4 H5 X3 X4]; simplify_eq. 1: econstructor 1.
      destruct (decide (tgcs = tg_new)) as [->|Hne].
      { exfalso. eapply Nc, H2'. }
      econstructor 2. 
      + erewrite <-create_child_same_rel_dec. 1: exact H1'. 3: done. 1-2: done.
      + eapply create_child_irreversible. 1: exact H2'. 2: done. done.
      + done.
      + done.
      + done.
  Qed.

  Lemma frozen_in_practice_create_child_irreversible
    {tr tr' tg tg_old tg_new pk rk cid witness loc}
    (Ne : tg_new ≠ tg)
    (Ne' : tg_new ≠ witness)
    (Frz : frozen_in_practice tr tg witness loc)
    (Ins : create_child C tg_old tg_new pk rk cid tr = Some tr')
    : frozen_in_practice tr' tg witness loc.
  Proof.
    inversion Frz as [it_witness ? Rel Lookup Perm Ini].
    opose proof (create_child_irreversible Lookup Ne' Ins) as Lookup'.
    econstructor.
    + erewrite <- create_child_same_rel_dec; first eassumption.
      - eassumption.
      - eassumption.
      - eassumption.
    + apply Lookup'.
    + done.
    + done.
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
    {tr1 tr1' tr2 tr2' it1 it1' it2 it2' tg l acc_tg kind range} (Hunq : wf_tree tr2)
    (SameProt : iprot it1 = iprot it2)
    (SameTg : itag it1 = itag it2) (* note: redundant *)
    (SameRel : forall tg tg', rel_dec tr1 tg tg' = rel_dec tr2 tg tg')
    (Unq1 : wf_tree tr1)
    (Unq2 : wf_tree tr2)
    :
    perm_eq_up_to_C tr1 tr2 tg l (iprot it1) (item_lookup it1 l) (item_lookup it2 l) ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr1 = Some tr1' ->
    tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) C acc_tg range tr2 = Some tr2' ->
    tree_lookup tr1 tg it1 ->
    tree_lookup tr1' tg it1' ->
    tree_lookup tr2 tg it2 ->
    tree_lookup tr2' tg it2' ->
    tree_contains acc_tg tr2 ->
    tree_contains acc_tg tr1 ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1 = Some it1' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2 = Some it2' ->
    perm_eq_up_to_C tr1' tr2' tg l (iprot it1') (item_lookup it1' l) (item_lookup it2' l).
  Proof.
    intros EqC Acc1 Acc2 Lookup1 Lookup1' Lookup2 Lookup2' Hacctg1 Hacctg2 ItAcc1 ItAcc2. 
    inversion EqC as [
        p pSpec Equal
        |ini im confl1 confl2 Prot Confl1 Confl2 itLookup1 itLookup2
        |ini im confl1 confl2 NoProt itLookup1 itLookup2
        |p1 p2 Confl1 Confl2 itLookup1 itLookup2
        |????? SameInit
        |ini im confl1 confl2 witness_tg Hfrz1 Hfrz2 itLookup1 itLookup2
    ].
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
      (* pseudo-disabled *)
    - rewrite SameRel SameTg in ItAcc1.
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
        econstructor 4.
        all: eapply access_preserves_pseudo_disabled; first done.
        all: done.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      edestruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec. all: clear Heff.
      2: { injection perm1'Spec as <-. injection perm2'Spec as <-.
           econstructor 4.
           all: eapply access_preserves_pseudo_disabled; first done.
           all: done. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      assert (¬ ParentChildIn (itag it2) acc_tg tr2) as HnPC.
      { intros HnPC. clear perm1'Spec perm1Spec.
        inversion Confl2 as [|tg_cs it_cs X1 X2 H1 H2 H3 H4 H5]; simplify_eq.
        1: { rewrite /apply_access_perm_inner /= in perm2Spec.
             rewrite /rel_dec decide_True // in perm2Spec. by destruct kind. }
        destruct (apply_access_spec_per_node (proj1 H2) (proj2 H2) Acc2)
              as (cous' & cous'_spec & cous'_ex & cous'_det).
        symmetry in cous'_spec.
        rewrite bind_Some in cous'_spec.
        destruct cous'_spec as (perms' & perms'_spec & cous'_build).
        injection cous'_build; intros; subst; clear cous'_build.
        pose proof (mem_apply_range'_spec _ _ l _ _ perms'_spec) as effect_at_l.
        rewrite decide_True // in effect_at_l.
        destruct effect_at_l as (perm' & perm'_lookup & perm'_spec).
        rewrite /item_lookup in H4. rewrite H4 in perm'_spec.
        rewrite bool_decide_true in perm'_spec. 2: done.
        assert (tg_cs = itag it_cs) as -> by (symmetry; by eapply tree_lookup_correct_tag).
        assert (tg = itag it2) as -> by (symmetry; by eapply tree_lookup_correct_tag).
        rewrite /rel_dec decide_False in perm'_spec.
        2: { intros Hx. eapply cousins_have_disjoint_children. 4: eassumption. 4-5: done.
             all: eapply Hunq. 1: done. 1: eapply Lookup2. 1: eapply H2. }
        rewrite decide_False in perm'_spec.
        2: { intros Hx. rewrite /rel_dec in H1.
             destruct decide as [|HH1] in H1; first done.
             destruct decide as [|HH2] in H1; first done.
             eapply HH2. eapply ParentChild_transitive. 2: exact Hx. 1: done. }
        rewrite maybe_non_children_only_no_effect in perm'_spec. 2: done.
        destruct kind in perm'_spec; cbv in perm'_spec; done. }
      rewrite /rel_dec decide_False // /= in perm2'Spec. injection perm2'Spec as <-.
      rewrite /rel_dec decide_False // /= in perm1'Spec. injection perm1'Spec as <-.
      rewrite /rel_dec decide_False // /= in perm2Spec.
      rewrite /rel_dec decide_False // /= in perm1Spec.
      econstructor 4; eapply access_preserves_pseudo_disabled. 2,4: done.
      + inversion Confl1 as [|X1 X2 X3 X4 X5 X6 X7 X8 H]; simplify_eq.
        1: destruct kind, bool_decide in perm1Spec; cbv in perm1Spec; injection perm1Spec as <-; econstructor 1.
        econstructor 2. 1-4: done.
        intros c ->.
        destruct (bool_decide (protector_is_active (iprot it1) C)), kind, p1 as [[][]| | |]; try discriminate perm1Spec.
        all: cbn in perm1Spec; injection perm1Spec as <-.
        all: by eapply H.
      + inversion Confl2 as [|X1 X2 X3 X4 X5 X6 X7 X8 H]; simplify_eq.
        1: destruct kind, bool_decide in perm1Spec; cbv in perm2Spec; injection perm2Spec as <-; econstructor 1.
        econstructor 2. 1-4: done.
        intros c ->.
        destruct (bool_decide (protector_is_active (iprot it2) C)), kind, p2 as [[][]| | |]; try discriminate perm2Spec.
        all: cbn in perm2Spec; injection perm2Spec as <-.
        all: by eapply H.
    - econstructor.
      + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption. 2-3: done.
        eassumption.
      + eapply disabled_in_practice_tree_apply_access_irreversible; last eassumption. 2-3: done.
        eassumption.
      + rewrite (item_apply_access_effect_on_initialized ItAcc1).
        rewrite (item_apply_access_effect_on_initialized ItAcc2).
        rewrite SameInit.
        case_match; last reflexivity.
        f_equal. f_equal. rewrite SameTg. apply SameRel.
    - (* Proof idea:
         each item is Reserved. Therefore it can:
         - get a child read: nothing happens
         - get a child write: it's UB, since the parent is frozen
         - get a foreign read: the conflictedness might change but that's OK, this case is precisely for that
         - get a foreign write: it's either UB or we remain, depending on interior mutability.
           + however, since such a write must disable our parent, it should not matter that IM is the same here.
             But reasoning about this is complicated (because of maybe_nonchildren_only) so let's just not. *)
      (* We're frozen in practice *)
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
      destruct (decide (range'_contains range l)) eqn:Hrangedec.
      2: {
        rewrite perm1'Spec.
        rewrite perm2'Spec.
        rewrite /item_lookup in itLookup1, itLookup2.
        rewrite -itLookup1 -itLookup2.
        econstructor 6.
        - eapply frozen_in_practice_tree_apply_access_irreversible in Hfrz1. 4: exact Acc1. 2-3: done.
          destruct Hfrz1 as [(Hf&HX)|(Hf&HX)]; first done.
          rewrite /becomes_frozen Hrangedec in HX. done.
        - eapply frozen_in_practice_tree_apply_access_irreversible in Hfrz2. 4: exact Acc2. 2-3: done.
          destruct Hfrz2 as [(Hf&HX)|(Hf&HX)]; first done.
          rewrite /becomes_frozen Hrangedec in HX. done.
      }
      (* Now we're within range *)
      destruct perm1'Spec as [perm1' [perm1'Lookup perm1'Spec]].
      destruct perm2'Spec as [perm2' [perm2'Lookup perm2'Spec]].
      rewrite perm1'Lookup perm2'Lookup; clear perm1'Lookup perm2'Lookup.
      simpl.
      rewrite /item_lookup in itLookup1, itLookup2.
      rewrite -itLookup1 in perm1'Spec; clear itLookup1.
      rewrite -itLookup2 in perm2'Spec; clear itLookup2.
      eapply frozen_in_practice_tree_apply_access_irreversible in Hfrz1; last exact Acc1. 2-3: done.
      eapply frozen_in_practice_tree_apply_access_irreversible in Hfrz2; last exact Acc2. 2-3: done.
      destruct Hfrz1 as [(H1&HX)|(H1&HX)],  Hfrz2 as [(H2&HY)|(H2&HY)].
      2,3: rewrite /becomes_frozen ?SameRel in HX,HY; done.
      all: edestruct (maybe_non_children_only_effect_or_nop b (apply_access_perm kind) (rel_dec tr2 acc_tg (itag it2))) as [Heff|Heff].
      all: rewrite !Heff /= in perm1'Spec,perm2'Spec; clear Heff.
      2: { simplify_eq. econstructor 6; eassumption. }
      3: { simplify_eq. econstructor 5. all: done. }
      (* Next we need to unwrap the apply_access_perm to get to apply_access_perm_inner *)
      all: rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [perm1 [perm1Spec perm1'Spec]].
      all: rewrite bind_Some in perm1'Spec; destruct perm1'Spec as [tmp1 [tmp1Spec perm1'Spec]].
      all: injection perm1'Spec; simpl; intros; subst; clear perm1'Spec.
      all: rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [perm2 [perm2Spec perm2'Spec]].
      all: rewrite bind_Some in perm2'Spec; destruct perm2'Spec as [tmp2 [tmp2Spec perm2'Spec]].
      all: injection perm2'Spec; simpl; intros; subst; clear perm2'Spec.
      2: { econstructor 5. 1-2: done. done. }
      simpl in *. rewrite -SameProt in tmp2Spec,perm2Spec.
      (* We can finally start the big case analysis at the level of the state machine *)
      edestruct (most_init ini _), perm1, perm2, (bool_decide (protector_is_active (iprot it1) C)); try congruence.
      all: injection tmp1Spec; intros; subst; clear tmp1Spec.
      all: injection tmp2Spec; intros; subst; clear tmp2Spec.
      all: destruct kind, (rel_dec _ _ _) eqn:relation, im, confl1; simpl in *; try discriminate.
      all: destruct confl2; simpl in *; try discriminate.
      all: try (injection perm1Spec; intros; subst); clear perm1Spec.
      all: try (injection perm2Spec; intros; subst); clear perm2Spec.
      all: try by econstructor 1.
      all: try by econstructor 6.
  Qed.

  Lemma item_eq_up_to_C_preserved_by_access (b : bool)
    {tr1 tr1' tr2 tr2' it1 it1' it2 it2' tg acc_tg kind range} (Hunq1 : wf_tree tr1) (Hunq2 : wf_tree tr2)
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
    tree_contains acc_tg tr1 ->
    tree_contains acc_tg tr2 ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr1 acc_tg (itag it1)) range it1 = Some it1' ->
    item_apply_access (maybe_non_children_only b (apply_access_perm kind)) C (rel_dec tr2 acc_tg (itag it2)) range it2 = Some it2' ->
    item_eq_up_to_C tr1' tr2' tg it1' it2'.
  Proof.
    intros EqC Acc1 Acc2 Lookup1 Lookup1' Lookup2 Lookup2' AccTg1 AccTg2 ItAcc1 ItAcc2.
    econstructor.
    - rewrite <- (proj1 (proj2 (item_apply_access_preserves_metadata _ _ ItAcc1))).
      rewrite <- (proj1 (proj2 (item_apply_access_preserves_metadata _ _ ItAcc2))).
      apply EqC. assumption.
    - eapply perm_eq_up_to_C_preserved_by_access.
      + done.
      + apply EqC. assumption.
      + apply SameTg.
      + apply SameRel.
      + eassumption.
      + eassumption.
      + apply EqC.
      + eassumption.
      + eassumption.
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
        * exact GloballyUnique1.
        * exact GloballyUnique2.
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
        * eassumption.
        * by eapply SameTg.
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
    (GloballyUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (PMI : parents_more_init tr2) :
    tree_equal tr1 tr2 ->
    tree_unique acc_tg tr1 ->
    is_Some (memory_deallocate C acc_tg range tr1) ->
    is_Some (memory_deallocate C acc_tg range tr2).
  Proof.
    intros Heq Hunq (tr1'&(pw1&Hpw1&Htrr%mk_is_Some)%bind_Some).
    pose proof Hpw1 as HH.
    eapply mk_is_Some, tree_equal_allows_same_access in HH as (pw2&Hpw2). 2-7: done.
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
    ∀ z v, lst !! z = Some v ↔ initialized (item_lookup it z) = PermInit ∧ (v = AccessWrite ↔ perm (item_lookup it z) = Active).
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
    intros H. try by inversion H.
  Qed.

  Lemma parents_not_disabled_child_not_active tr tg1 tg2 it1 it2 off
    (Hwf : wf_tree tr)
    (HPP : parents_more_active tr) :
    tree_lookup tr tg1 it1 →  
    tree_lookup tr tg2 it2 →
    ParentChildIn tg1 tg2 tr →
    perm (item_lookup it1 off) = Disabled →
    perm (item_lookup it2 off) = Active →
    False.
  Proof.
    intros Hl1 Hl2 HPC Hp1 Hp2.
    specialize (HPP tg1). eapply every_child_ParentChildIn in HPP.
    2: done. 2, 4: eapply Hwf. 2,4: eapply Hl1. 2: eapply Hl2. 2: done.
    assert (tg1 = itag it1) as -> by by eapply tree_lookup_correct_tag in Hl1.
    assert (tg2 = itag it2) as -> by by eapply tree_lookup_correct_tag in Hl2.
    eapply every_node_eqv_universal in HPP.
    2: eapply tree_lookup_to_exists_node, Hl2.
    ospecialize (HPP _ _ Hp2). 1: done. congruence.
  Qed.

  Lemma disabled_in_practice_not_active tr tg1 tg2 it off
    (Hwf : wf_tree tr)
    (HPP : parents_more_active tr)
    (HNC : no_active_cousins C tr) :
    tree_lookup tr tg2 it →
    perm (item_lookup it off) = Active →
    disabled_in_practice tr tg2 tg1 off →
    False.
  Proof.
    intros Hl1 Hact [it_witness incl H1 H2 H3].
    destruct (decide (perm (item_lookup it_witness off) = Disabled)) as [Hdis|Hnondis].
    + eapply parents_not_disabled_child_not_active. 1: exact Hwf. 1: done. 4: exact Hdis. 4: exact Hact.
      1-2: done.
      rewrite /rel_dec in H1. destruct decide; done.
    + inversion H3 as [X1 X2 X3|lp X HH1 HH2 X2]; simplify_eq.
      { rewrite -X2 in Hnondis. done. }
      inversion HH1 as [|tgcs itcs X1 X2 H1' H2' H3' H4 H5 X3 X4]; simplify_eq.
      { rewrite -HH2 in Hnondis. done. }
      eapply HNC. 1: exact H2'. 1: exact Hl1. 3: exact Hact. 2: right; split; first done.
      2: by rewrite H4.
      rewrite /rel_dec in H1|-*.
      destruct decide as [HPC1|] in H1; last done. clear H1.
      rewrite decide_False; last first.
      { intros HPC2. rewrite /rel_dec in H1'.
        destruct decide in H1'; try done.
        rewrite decide_True // in H1'.
        eapply ParentChild_transitive. 1: exact HPC1. done. }
      rewrite decide_False //.
      intros HPC2.
      eapply cousins_have_disjoint_children. 4: exact H1'. 4: exact HPC1. 4: done.
      all: eapply Hwf. 1: eapply Hl1. 1: eapply H2. 1: eapply H2'.
  Qed.

  Lemma perm_eq_up_to_C_same_active tr1 tr2 tg off prot it1 it2 ev1 ev2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2)
    (ProtParentsNonDis1 : parents_more_active tr1)
    (ProtParentsNonDis2 : parents_more_active tr2)
    (HCS1 : no_active_cousins C tr1)
    (HCS2 : no_active_cousins C tr2)
    (Hiwf1 : item_wf it1 ev1 ev2)
    (Hiwf2 : item_wf it2 ev1 ev2) :
    tree_lookup tr1 tg it1 →
    tree_lookup tr2 tg it2 →
    perm_eq_up_to_C tr1 tr2 tg off prot (item_lookup it1 off) (item_lookup it2 off) →
    perm (item_lookup it1 off) = Active ↔ perm (item_lookup it2 off) = Active.
  Proof.
    intros Hl1 Hl2 H. inversion H as [| | |p1 p2 HX1 HX2 HX3 HX4| |]; try done; simplify_eq.
    - simpl; split; intros Hact; exfalso.
      + rewrite /item_lookup in HX3.
        destruct lookup eqn:Heq in HX3.
        2: { simpl in HX3. injection HX3 as ->.
             eapply item_default_perm_valid in Hact; done. }
        rewrite /= in HX3. subst.
        eapply item_perms_valid in Heq. 2: done.
        simpl in Heq. by ospecialize (Heq _).
      + rewrite /item_lookup in HX4.
        destruct lookup eqn:Heq in HX4.
        2: { simpl in HX3. injection HX4 as ->.
             eapply item_default_perm_valid in Hact; done. }
        rewrite /= in HX4. subst.
        eapply item_perms_valid in Heq. 2: done.
        simpl in Heq. by ospecialize (Heq _).
    - split; intros XX; exfalso; 
      (eapply disabled_in_practice_not_active in XX; [| | | |done| ]; done).
  Qed.

  Lemma tree_equals_protected_initialized tr1 tr2 cid ev1 ev2
    (AllUnique1 : forall tg, tree_contains tg tr1 -> tree_unique tg tr1)
    (AllUnique2 : forall tg, tree_contains tg tr2 -> tree_unique tg tr2)
    (PMA1 : parents_more_active tr1)
    (PMA2 : parents_more_active tr2)
    (HCS1 : no_active_cousins C tr1)
    (HCS2 : no_active_cousins C tr2)
    (Hiwf1 : tree_items_compat_nexts tr1 ev1 ev2)
    (Hiwf2 : tree_items_compat_nexts tr2 ev1 ev2)
    (ProtParentsNonDis2 : protected_parents_not_disabled C tr2) :
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
      erewrite <- perm_eq_up_to_C_same_init. 2: done.
      setoid_rewrite <- perm_eq_up_to_C_same_active. 12: eassumption. 2-7: done.
      1,4,5: done.
      + eapply every_node_eqv_universal in Hiwf1. 2: eapply tree_lookup_to_exists_node, Hlu.
        exact Hiwf1.
      + eapply every_node_eqv_universal in Hiwf2. 2: eapply tree_lookup_to_exists_node, Hit'.
        exact Hiwf2.
    - edestruct (tree_equal_transfer_lookup_2 Heq Hlu) as (it'&Hit'&Heqit').
      exists it'. split; first done.
      split; first by erewrite item_eq_up_to_C_same_iprot.
      intros z. specialize (Hinit z). destruct (Heqit' z) as (_&Heqlu).
      erewrite perm_eq_up_to_C_same_init. 2: done.
      setoid_rewrite perm_eq_up_to_C_same_active. 12: eassumption. 2-7: done.
      1,4,5: done.
      + eapply every_node_eqv_universal in Hiwf1. 2: eapply tree_lookup_to_exists_node, Hit'.
        exact Hiwf1.
      + eapply every_node_eqv_universal in Hiwf2. 2: eapply tree_lookup_to_exists_node, Hlu.
        exact Hiwf2.
  Qed.

  Lemma tree_equals_access_many_helper_2 tg (L : gmap Z _) tr1 tr1' tr2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2) 
    (PMI : parents_more_init tr2)
    (ProtParentsNonDis2 : protected_parents_not_disabled C tr2) :
    tree_equal tr1 tr2 →
    tree_unique tg tr1 →
    let fn := (λ tr, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr) L) in
    fn tr1 = Some tr1' →
    ∃ tr2', fn tr2 = Some tr2' ∧  tree_equal tr1' tr2'.
  Proof.
    intros Heq Hunq''. simpl.
    map_fold_ind L as off acc E Hnone Hfoo IH in tr1' Hunq''.
    { simpl. intros [= ->]; by eexists. }
    simpl. intros (tr1'''&H1&H2)%bind_Some.
    specialize (IH _ Hunq'' H1) as (tr2'''&Htr2&HHtr2p). rewrite Hfoo Htr2 /=.
    assert (tree_unique tg tr1''') as Hunq'''.
    { rewrite /tree_unique. erewrite <- tree_access_many_helper_2. 1: exact Hunq''. exact H1. }
    assert (wf_tree tr1''') as Hwf1'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf1. 1: apply H1. }
    assert (wf_tree tr2''') as Hwf2'''.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_2. 1: exact Hwf2. 1: apply Htr2. } 
    opose proof (tree_equal_allows_same_access_nonchildren_only _ _ _ _ HHtr2p Hunq''' _) as (trr&Htrr).
    1, 2: by apply wf_tree_tree_unique.
    1: { eapply tree_access_many_protected_not_disabled_helper_2. 5: exact Htr2. 1,3,4: done. destruct Heq as (H&_). by eapply H, unique_exists. }
    1: { eapply tree_access_many_more_init_helper_2. 4: exact Htr2. 1,3: done. destruct Heq as (H&_). by eapply H, unique_exists. }
    1: by eapply mk_is_Some.
    exists trr; split; first done.
    eapply tree_equal_preserved_by_memory_access_nonchildren_only.
    5-6: done. 3: done. 3: by eapply unique_exists.
    1-2: by eapply wf_tree_tree_unique.
  Qed.

  Lemma tree_equals_access_many_helper_1 (E : list (tag * gmap Z _)) tr1 tr1' tr2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2)
    (PMI2 : parents_more_init tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2) :
    tree_equal tr1 tr2 →
    (∀ tg L, (tg, L) ∈ E → tree_unique tg tr1)→
    let fn := (λ tr, foldr (λ '(tg, L) tr, tr ≫= λ tr1, map_fold (λ l acc tr2, tr2 ≫= memory_access_nonchildren_only acc C tg (l, 1%nat)) (Some tr1) L) (Some tr) E) in
    fn tr1 = Some tr1' →
    ∃ tr2', fn tr2 = Some tr2' ∧ tree_equal tr1' tr2'.
  Proof.
    intros Heq Hunq.
    induction E as [|(tg&init_locs) S IH] in tr1',Hunq|-*.
    { simpl. intros [= ->]; by eexists. }
    simpl. intros (tr1''&H1&H2)%bind_Some.
    opose proof (IH _ _ H1) as (tr2''&Htr2&HHtr2); clear IH.
    { intros ???. eapply Hunq. by right. }
    rewrite Htr2 /=. pose proof Hunq as Hunq2.
    ospecialize (Hunq tg init_locs _). 1: by left. revert H2.
    eapply tree_equals_access_many_helper_2.
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf1. 1: apply H1. }
    { eapply preserve_tag_count_wf. 1: eapply tree_access_many_helper_1. 1: exact Hwf2. 1: exact Htr2. }
    { eapply tree_access_many_more_init_helper_1. 4: exact Htr2. 1,3: done. intros ???. destruct Heq as (HH&_); eapply HH, unique_exists, Hunq2. by right. }
    { eapply tree_access_many_protected_not_disabled_helper_1. 5: exact Htr2. 1,3,4: done. intros ???. destruct Heq as (HH&_); eapply HH, unique_exists, Hunq2. by right. }
    { done. }
    { rewrite /tree_unique. erewrite <- tree_access_many_helper_1. 1: exact Hunq. exact H1. }
  Qed.

  Lemma tree_equals_access_all_protected_initialized' tr1 tr1' tr2 cid ev1 ev2
    (Hwf1 : wf_tree tr1)
    (Hwf2 : wf_tree tr2)
    (PMI : parents_more_init tr2)
    (PMA1 : parents_more_active tr1)
    (PMA2 : parents_more_active tr2)
    (ProtParentsNonDis : protected_parents_not_disabled C tr2)
    (NA1 : no_active_cousins C tr1)
    (NA2 : no_active_cousins C tr2)
    (CC1 : tree_items_compat_nexts tr1 ev1 ev2)
    (CC2 : tree_items_compat_nexts tr2 ev1 ev2) :
    tree_equal tr1 tr2 →
    tree_access_all_protected_initialized C cid tr1 = Some tr1' →
    ∃ tr2', tree_access_all_protected_initialized C cid tr2 = Some tr2' ∧
      tree_equal tr1' tr2'.
  Proof.
    intros Heq.
    rewrite /tree_access_all_protected_initialized.
    erewrite <- (tree_equals_protected_initialized tr1 tr2); last done.
    2-3: by eapply wf_tree_tree_unique. 2-8: done.
    eapply tree_equals_access_many_helper_1. 1-5: done.
    {intros tg E. setoid_rewrite elem_of_elements.
      intros (it&Hit&_)%tree_all_protected_initialized_elem_of. all: eapply wf_tree_tree_unique; try apply Hwf1.
      by eapply lookup_implies_contains. }
  Qed.

  Lemma apply_within_trees_lift trs fn blk trs' :
    wf_trees trs →
    apply_within_trees fn blk trs = Some trs' →
    (∀ tr tr', trs !! blk = Some tr → trs' !! blk = Some tr' → fn tr = Some tr' → tree_equal tr tr') →
    trees_equal trs trs'.
  Proof.
    intros Hwf (tr&Htr&(tr'&Htr'&[= <-])%bind_Some)%bind_Some Heq.
    intros bb. destruct (decide (bb = blk)) as [<-|Hne].
    - rewrite lookup_insert Htr. econstructor. eapply Heq. 1,3: done. by rewrite lookup_insert.
    - rewrite lookup_insert_ne //. destruct (trs !! bb) eqn:HHeq. all: rewrite !HHeq. all: econstructor.
      eapply tree_equal_reflexive. eapply wf_tree_tree_item_determined, Hwf, HHeq.
  Qed.

  Lemma trees_equal_access_all_protected_initialized trs1 trs1' trs2 cid ev1 ev2
    (Hwf1 : wf_trees trs1)
    (Hwf2 : wf_trees trs2)
    (PMI : each_tree_parents_more_init trs2)
    (PMA1 : each_tree_parents_more_active trs1)
    (PMA2 : each_tree_parents_more_active trs2)
    (ProtParentsNonDis2 : each_tree_protected_parents_not_disabled C trs2)
    (NA1 : each_tree_no_active_cousins C trs1)
    (NA2 : each_tree_no_active_cousins C trs2)
    (CC1 : trees_compat_nexts trs1 ev1 ev2)
    (CC2 : trees_compat_nexts trs2 ev1 ev2) :
    trees_equal trs1 trs2 →
    trees_access_all_protected_initialized C cid trs1 = Some trs1' →
    ∃ trs2', trees_access_all_protected_initialized C cid trs2 = Some trs2' ∧
      trees_equal trs1' trs2'.
  Proof.
    intros Heq Htrapi.
    epose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ Htrapi) as Htrapi1.
    odestruct (trees_access_all_protected_initialized_pointwise_2 _ trs2) as (trs2'&Htrs2').
    { intros k. destruct (Htrapi1 k) as (HH'&_). intros tr2 Htr2.
      specialize (Heq k). rewrite Htr2 in Heq. inversion Heq as [tr1 x1 Heqtr Htr1 e|]. subst x1.
      destruct (HH' tr1) as (tr1'&Htr1'&HHtr1'); first done.
      edestruct tree_equals_access_all_protected_initialized' as (tr2'&Htr2'&Heq').
      11: exact Heqtr. 11: exact HHtr1'. 1: by eapply Hwf1. 1: by eapply Hwf2.
      9: by eexists. 1: by eapply PMI. 1: by eapply PMA1. 1: by eapply PMA2. 1: by eapply ProtParentsNonDis2.
      1: by eapply NA1. 1: by eapply NA2. 1: by eapply CC1. 1: by eapply CC2. }
    eexists; split; first done.
    intros k. specialize (Heq k).
    epose proof (trees_access_all_protected_initialized_pointwise_1 _ _ _ _ Htrs2' k) as (Htrapi2A&Htrapi2B).
    specialize (Htrapi1 k) as (Htrapi1A&Htrapi1B).
    inversion Heq as [tr1 tr2 Heqtr Htr1 Htr2|HNone1 HNone2]; last first.
    - rewrite Htrapi1B // Htrapi2B //. econstructor.
    - symmetry in Htr1,Htr2.
      destruct (Htrapi1A _ Htr1) as (tr1'&Htr1'&Hrapi1'). destruct (Htrapi2A _ Htr2) as (tr2'&Htr2'&Hrapi2').
      rewrite Htr1' Htr2'. econstructor.
      edestruct tree_equals_access_all_protected_initialized' as (tr2''&Htr2'u&Htr2'eq).
      12: exact Hrapi1'. 11: exact Heqtr. 1: by eapply Hwf1. 1: by eapply Hwf2. 1: by eapply PMI. 1: by eapply PMA1. 1: by eapply PMA2. 1: by eapply ProtParentsNonDis2.
      1: by eapply NA1. 1: by eapply NA2. 1: by eapply CC1. 1: by eapply CC2.
      rewrite Hrapi2' in Htr2'u. injection Htr2'u as <-. done.
  Qed.

    (* A bunch of extra conditions on the structure.
       They are put in the same clause to simplify this theorem, but we will want
       a higher-level lemma that derives these assumptions from their actual justification. *)
  Definition tree_equal_asymmetric_read_pre_protected tr range it acc_tg (mode:bool) := 
    (∀ off, range'_contains range off → 
            let pp_acc := item_lookup it off in
            pp_acc.(initialized) = PermInit ∧ pp_acc.(perm) ≠ Disabled ∧
            ∀ tg' it', tree_lookup tr tg' it' → 
            let pp := item_lookup it' off in
            let rd := rel_dec tr tg' acc_tg in (* flipped here so that it's correcty lined up with logical_state *)
            match rd with
              Foreign (Parent _) => pp.(initialized) = PermInit ∧ pp.(perm) ≠ Disabled
            | Foreign Cousin => pp.(perm) ≠ Active | _ => True end ∧
            if mode then (rd = Child (Strict Immediate) → pp.(perm) = Disabled) else
             (pp_acc.(perm) = Frozen ∧ (∀ i, rd = Child (Strict i) → pp.(perm) ≠ Active))).

  (* Remember that the entire reason we have [trees_equal] in the first place
     is to enable spurious reads. This is the lemma that verifies that after we
     do a spurious read we get a [tree_equal]. A companion lemma (stating
     that under certain circumstances the spurious read will succeed) will be proved
     separately.

     The hypotheses are guided by the optimizations that we want to prove.
     We can't (and don't plan to) do spurious reads anywhere, only on protected
     tags. For now we require that the tag also doesn't have any Active
     children. Both of these can be relaxed slightly, but a more general version
     of this lemma will come only if actually required.

     Because we have nice properties of transitivity and reflexivity of [tree_equal]
     already, the proof can be simplified by only considering the case where
     before the asymmetric read the trees are identical. In other words we're going
     to check that a tree is [tree_equal] to itself after a read. *)
  Lemma tree_equal_asymmetric_read_protected
    {tr tr' acc_tg range it} (mode:bool)
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    :
    (* Accessed tag must be in the tree and protected*)
    tree_lookup tr acc_tg it ->
    protector_is_active it.(iprot) C ->
    tree_equal_asymmetric_read_pre_protected tr range it acc_tg mode ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessRead C acc_tg range tr = Some tr' ->
    tree_equal tr tr'.
  Proof.
    intros Lkup Protected TreeShapeProper Acc.
    split; last split.
    { intro tg. eapply access_preserves_tags. eassumption. }
    { intros tg1 tg2. eapply access_same_rel_dec. eassumption. }
    (* That was the easy part, helped by the fact that our initial configuration
       is reflexivity instead of a more general instance of [tree_equal].
       Soon it will get more interesting. *)
    intros tg0 Ex.
    destruct (unique_implies_lookup (GloballyUnique _ Ex)) as [it0 Lookup0].
    exists it0.
    assert (tree_unique tg0 tr') as Unq0'. {
      erewrite <- tree_apply_access_preserve_unique; last eassumption.
      apply GloballyUnique. assumption.
    }
    destruct (apply_access_spec_per_node (proj1 Lookup0) (proj2 Lookup0) Acc) as
        (it0' & it0'Spec & Ex0' & Det0').
    symmetry in it0'Spec.
    exists it0'.
    split; first assumption.
    split; first (split; assumption).
    (* Now down to per-item reasoning *)
    intro loc.
    split; first (eapply item_apply_access_preserves_metadata; eassumption).
    rewrite bind_Some in it0'Spec; destruct it0'Spec as (perms' & perms'Spec & [= <-]).
    pose proof (mem_apply_range'_spec _ _ loc _ _ perms'Spec) as PerLoc.
    clear perms'Spec.
    assert (itag it0 = tg0) by (eapply tree_determined_specifies_tag; eapply Lookup0).
    assert (itag it = acc_tg) by (eapply tree_determined_specifies_tag; eapply Lkup).
    subst.
    (* Finally the reasoning is per-location *)
    destruct (decide _) as [HinRange|?]; last first.
    { rewrite /item_lookup /= PerLoc.
      constructor. }
    destruct (TreeShapeProper _ HinRange) as (Htginit&Htgnondis&Hothers).
    (* Keep digging until [apply_access_perm_inner] *)
    destruct PerLoc as (perm' & perm'Lookup & perm'Spec).
    pose proof Hothers as Hothers_pure.
    ospecialize (Hothers _ _ Lookup0).
    change (default _ _) with (item_lookup it0 loc) in perm'Spec.
    rewrite {2}/item_lookup perm'Lookup /=.
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (tmperm & Inner & perm'Spec).
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (validated & MoreInit & EqPerm).
    injection EqPerm; clear EqPerm; intros; subst.
    rewrite rel_dec_flip2 in Hothers.
    destruct Hothers as (Hothers&Hspecials).
    destruct (rel_dec tr (itag it) (itag it0)) as [[]|[]] eqn:Hreldec.
    - destruct mode.
      + assert (∃ tg, tree_contains tg tr ∧ rel_dec tr tg (itag it) = Child (Strict Immediate) ∧ ParentChildIn tg (itag it0) tr) as (tgsw & Hin & Hswdec&Hpar).
        { rewrite /rel_dec in Hreldec. destruct decide as [HP|HnP]; try done. destruct decide as [HP|?]; try done.
          destruct HP as [Heq|HSP]. 1: exfalso; eapply HnP; by left.
          eapply immediate_sandwich in HSP as HSP2. 2, 3: eapply GloballyUnique. 2: eapply Lkup.
          destruct HSP2 as (tsw&Htsw&HPC). exists tsw.
          assert (tree_contains tsw tr) as Hcont.
          { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild.
            eapply Lkup. }
           split_and!. 1: done. 2: done.
          rewrite /rel_dec decide_True. 
          2: right; by eapply Immediate_is_StrictParentChild.
          rewrite decide_False. 1: by rewrite decide_True.
          intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
          all: eapply GloballyUnique. 1: eapply Lkup. done. }
        assert (∃ itsw, tree_lookup tr tgsw itsw) as (itsw&Hitsw).
        1: eapply unique_implies_lookup, GloballyUnique, Hin.
        specialize (Hothers_pure _ _ Hitsw).
        destruct (apply_access_spec_per_node (proj1 Hitsw) (proj2 Hitsw) Acc) as
        (itsw' & itsw'Spec & Hitsw').
        destruct Hothers_pure as (_&HH). ospecialize (HH _). 1: done.
        eapply (perm_eq_up_to_C_disabled_parent _ _ _ _ _ tgsw). 3: rewrite /= most_init_comm //=.
        * econstructor. 2: done. 1: rewrite /rel_dec decide_True //.
          destruct (item_lookup itsw loc) as [[] pp] eqn:HHH; simpl in *; subst pp.
          1: econstructor 1. econstructor 2. econstructor 1.
        * econstructor. 1: erewrite <- access_same_rel_dec. 2: eassumption. 1: rewrite /rel_dec decide_True //.
          1: exact Hitsw'. symmetry in itsw'Spec.
          eapply bind_Some in itsw'Spec as (psw&Hsw&[= Hitsweq]).
          pose proof (mem_apply_range'_spec _ _ loc _ _ Hsw) as PerLocSW.
          rewrite decide_True // in PerLocSW. destruct PerLocSW as (p & HPP & Hacc).
          rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hacc.
          change (default _ _) with (item_lookup itsw loc) in Hacc.
          assert (itag itsw = tgsw) as <- by by eapply tree_lookup_correct_tag.
          rewrite rel_dec_flip2 Hswdec /= HH /= most_init_comm /= in Hacc.
          rewrite /item_lookup /= -Hitsweq HPP /=.
          destruct (item_lookup itsw loc) as [ini prm] eqn:Heq; simpl in *; subst prm.
          edestruct (bool_decide (protector_is_active (iprot itsw) C)), ini in Hacc; simpl in Hacc; try discriminate Hacc; injection Hacc as <-.
          all: try econstructor 1. all: econstructor 2; econstructor 1.
      + rewrite /apply_access_perm_inner /= in Inner. rewrite /= most_init_comm /=.
        destruct Hspecials as (Hfrz&Hnact).
        destruct (item_lookup it0 loc) as [ini [imm cfl| | |]] eqn:Hperm.
        3,4: by (destruct ini, (bool_decide (protector_is_active (iprot it0) C)); simpl in *; simplify_eq; econstructor 1).
        2: exfalso; by eapply Hnact.
        simpl in *. assert (∃ cfl', validated = Reserved imm cfl') as (cfl'&->).
        { destruct ini, cfl, (bool_decide (protector_is_active (iprot it0) C)); simpl in *; eexists; simplify_eq; done. }
        destruct (apply_access_spec_per_node (proj1 Lkup) (proj2 Lkup) Acc) as
        (it' & it'Spec & Hit'). symmetry in it'Spec.
        eapply bind_Some in it'Spec as (pit&Hpit&[= Hiteq]).
        pose proof (mem_apply_range'_spec _ _ loc _ _ Hpit) as PerLoc.
        rewrite decide_True // in PerLoc. destruct PerLoc as (p & HPP & Hacc).
        rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hacc.
        change (default _ _) with (item_lookup it loc) in Hacc.
        assert (itag it' = itag it) as Hit by by eapply tree_lookup_correct_tag.
        rewrite rel_dec_refl Hfrz /= most_init_comm /= in Hacc.
        rewrite Tauto.if_same /= in Hacc. injection Hacc as <-.
        eapply perm_eq_up_to_C_frozen_parent with (witness_tg := itag it).
        * econstructor. 1: rewrite rel_dec_flip2 Hreldec //. 1: exact Lkup. 1: done. 1: done.
        * econstructor.
          { erewrite <- access_same_rel_dec. 2: done. rewrite rel_dec_flip2 Hreldec //. }
          { eapply Hit'. }
          all: rewrite /item_lookup -Hiteq /= HPP /= //.
    - rewrite /= most_init_comm /=.
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [[] [? []| | |]] eqn:Hperm, (bool_decide (protector_is_active (iprot it0) C)) eqn:Hprot; simpl in *.
      all: try by (simplify_eq; econstructor 1).
      1-2: simplify_eq; econstructor 2;
            [by eapply bool_decide_eq_true_1| |econstructor 1].
      1-2: eapply (pseudo_conflicted_cousin_init _ _ _ (itag it) it);
            [rewrite rel_dec_flip2 Hreldec //|done..].
    - destruct Hothers as (Hinit&Hndis).
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [[] pp] eqn:Hperm. 2: done.
      assert (pp = tmperm) as ->.
      { simpl in *. destruct pp; simplify_eq; done. }
      rewrite /= in MoreInit|-*.
      destruct tmperm, (bool_decide (protector_is_active (iprot it0) C)); simpl in MoreInit.
      all: try done. all: simplify_eq; econstructor 1.
    - simpl in *. assert (itag it = itag it0) as Htageq.
      { rewrite /rel_dec in Hreldec. do 2 (destruct decide; try done).
        eapply mutual_parent_child_implies_equal. 1: done. 1: eapply Lkup. all: done. }
      assert (it = it0) as ->.
      { eapply tree_determined_unify. 1, 2: eapply Lkup. rewrite Htageq. eapply Lookup0. }
      rewrite Htginit in MoreInit|-*.
      rewrite bool_decide_true // /= in MoreInit.
      destruct (item_lookup it0 loc) as [[] pp] eqn:Hperm. 2: done.
      destruct pp; try done. all: repeat (simpl in *; simplify_eq); by econstructor 1.
  Qed.

  (* We can also do symmetric writes, provided we have sufficiently strong preconditions,
     which include being protected. *)
  Definition tree_equal_asymmetric_write_pre_protected tr range it acc_tg := 
    (∀ off, range'_contains range off → 
            let pp_acc := item_lookup it off in
            pp_acc.(initialized) = PermInit ∧ pp_acc.(perm) = Active ∧
            ∀ tg' it', tree_lookup tr tg' it' → 
            let pp := item_lookup it' off in
            let rd := rel_dec tr tg' acc_tg in (* flipped here so that it's correcty lined up with logical_state *)
            match rd with
            | Child (Strict Immediate) => pp.(perm) = Disabled
            | Child _ => True
            | Foreign (Parent _) => pp.(initialized) = PermInit ∧ pp.(perm) = Active (* this follows from state_wf *)
            | Foreign Cousin => match pp.(perm) with Disabled => True | Reserved InteriorMut _ => ¬ protector_is_active it'.(iprot) C (* never occurs *) | _ => pp.(initialized) = PermLazy end end).

  Lemma disabled_is_disabled x1 x2 x3 x4 pp : perm pp = Disabled → is_disabled x1 x2 x3 pp x4.
  Proof.
    destruct pp as [[] pp]; simpl; intros ->.
    1: econstructor 1.
    econstructor 2. econstructor 1.
  Qed.

  Lemma tree_equal_asymmetric_write_protected
    {tr tr' acc_tg range it}
    (GloballyUnique : forall tg, tree_contains tg tr -> tree_unique tg tr)
    :
    (* Accessed tag must be in the tree and protected*)
    tree_lookup tr acc_tg it ->
    protector_is_active it.(iprot) C ->
    tree_equal_asymmetric_write_pre_protected tr range it acc_tg ->
    (* Under the above conditions if we do a spurious read and it succeeds
       we get a [tree_equal] on the outcome. *)
    memory_access AccessWrite C acc_tg range tr = Some tr' ->
    tree_equal tr tr'.
  Proof.
    intros Lkup Protected TreeShapeProper Acc.
    split; last split.
    { intro tg. eapply access_preserves_tags. eassumption. }
    { intros tg1 tg2. eapply access_same_rel_dec. eassumption. }
    (* That was the easy part, helped by the fact that our initial configuration
       is reflexivity instead of a more general instance of [tree_equal].
       Soon it will get more interesting. *)
    intros tg0 Ex.
    destruct (unique_implies_lookup (GloballyUnique _ Ex)) as [it0 Lookup0].
    exists it0.
    assert (tree_unique tg0 tr') as Unq0'. {
      erewrite <- tree_apply_access_preserve_unique; last eassumption.
      apply GloballyUnique. assumption.
    }
    destruct (apply_access_spec_per_node (proj1 Lookup0) (proj2 Lookup0) Acc) as
        (it0' & it0'Spec & Ex0' & Det0').
    symmetry in it0'Spec.
    exists it0'.
    split; first assumption.
    split; first (split; assumption).
    (* Now down to per-item reasoning *)
    intro loc.
    split; first (eapply item_apply_access_preserves_metadata; eassumption).
    rewrite bind_Some in it0'Spec; destruct it0'Spec as (perms' & perms'Spec & [= <-]).
    pose proof (mem_apply_range'_spec _ _ loc _ _ perms'Spec) as PerLoc.
    clear perms'Spec.
    assert (itag it0 = tg0) by (eapply tree_determined_specifies_tag; eapply Lookup0).
    assert (itag it = acc_tg) by (eapply tree_determined_specifies_tag; eapply Lkup).
    subst.
    (* Finally the reasoning is per-location *)
    destruct (decide _) as [HinRange|?]; last first.
    { rewrite /item_lookup /= PerLoc.
      constructor. }
    destruct (TreeShapeProper _ HinRange) as (Htginit&Htgactive&Hothers).
    (* Keep digging until [apply_access_perm_inner] *)
    destruct PerLoc as (perm' & perm'Lookup & perm'Spec).
    pose proof Hothers as Hothers_pure.
    ospecialize (Hothers _ _ Lookup0).
    change (default _ _) with (item_lookup it0 loc) in perm'Spec.
    rewrite {2}/item_lookup perm'Lookup /=.
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (tmperm & Inner & perm'Spec).
    rewrite bind_Some in perm'Spec; destruct perm'Spec as (validated & MoreInit & EqPerm).
    injection EqPerm; clear EqPerm; intros; subst.
    rewrite rel_dec_flip2 /= in Hothers.
    destruct (rel_dec tr (itag it) (itag it0)) as [[]|[]] eqn:Hreldec; simpl in Hothers.
    - assert (∃ tg, tree_contains tg tr ∧ rel_dec tr tg (itag it) = Child (Strict Immediate) ∧ ParentChildIn tg (itag it0) tr) as (tgsw & Hin & Hswdec&Hpar).
      { rewrite /rel_dec in Hreldec. destruct decide as [HP|HnP]; try done. destruct decide as [HP|?]; try done.
        destruct HP as [Heq|HSP]. 1: exfalso; eapply HnP; by left.
        eapply immediate_sandwich in HSP as HSP2. 2, 3: eapply GloballyUnique. 2: eapply Lkup.
        destruct HSP2 as (tsw&Htsw&HPC). exists tsw.
        assert (tree_contains tsw tr) as Hcont.
        { eapply contains_child. 1: right; by eapply Immediate_is_StrictParentChild.
          eapply Lkup. }
         split_and!. 1: done. 2: done.
        rewrite /rel_dec decide_True. 
        2: right; by eapply Immediate_is_StrictParentChild.
        rewrite decide_False. 1: by rewrite decide_True.
        intros HH. eapply immediate_parent_not_child. 4: exact HH. 3: done.
        all: eapply GloballyUnique. 1: eapply Lkup. done. }
      assert (∃ itsw, tree_lookup tr tgsw itsw) as (itsw&Hitsw).
      1: eapply unique_implies_lookup, GloballyUnique, Hin.
      specialize (Hothers_pure _ _ Hitsw).
      destruct (apply_access_spec_per_node (proj1 Hitsw) (proj2 Hitsw) Acc) as
      (itsw' & itsw'Spec & Hitsw'). rewrite Hswdec /= in Hothers_pure.
      eapply (perm_eq_up_to_C_disabled_parent _ _ _ _ _ tgsw). 3: rewrite /= most_init_comm //=.
      * econstructor. 2: done. 1: rewrite /rel_dec decide_True //.  eapply disabled_is_disabled, Hothers_pure.
      * econstructor. 1: erewrite <- access_same_rel_dec. 2: eassumption. 1: rewrite /rel_dec decide_True //.
        1: exact Hitsw'. symmetry in itsw'Spec.
        eapply bind_Some in itsw'Spec as (psw&Hsw&[= Hitsweq]).
        pose proof (mem_apply_range'_spec _ _ loc _ _ Hsw) as PerLocSW.
        rewrite decide_True // in PerLocSW. destruct PerLocSW as (p & HPP & Hacc).
        rewrite /= /apply_access_perm /apply_access_perm_inner /= in Hacc.
        change (default _ _) with (item_lookup itsw loc) in Hacc.
        assert (itag itsw = tgsw) as <- by by eapply tree_lookup_correct_tag.
        rewrite rel_dec_flip2 Hswdec /= Hothers_pure /= in Hacc.
        rewrite /item_lookup /= -Hitsweq HPP /=.
        repeat (case_match; simpl in *; try done; simplify_eq).
        all: by eapply disabled_is_disabled.
    - rewrite /= most_init_comm /=.
      rewrite /apply_access_perm_inner /= in Inner.
      eapply rel_dec_flip in Hreldec.
      destruct (item_lookup it0 loc) as [[] [[] []| | |]] eqn:Hperm, (bool_decide (protector_is_active (iprot it0) C)) eqn:Hprot; simpl in *.
      all: try by (simplify_eq; first [done | econstructor 1]).
      all: try by eapply bool_decide_eq_true_1 in Hprot.
      all: injection Inner as <-; injection MoreInit as <-. 
      all: econstructor 4; last econstructor 1.
      all: econstructor 2; [exact Hreldec|exact Lkup|done|destruct (item_lookup it loc); simpl in *; congruence| ].
      all: intros ? [=]. all: by eapply bool_decide_eq_true_1.
    - destruct Hothers as (Hini&Hact).
      rewrite /apply_access_perm_inner /= in Inner.
      destruct (item_lookup it0 loc) as [ini pp] eqn:Hperm.
      simpl in Hini, Hact. subst ini pp. simpl in Inner. simplify_eq. simpl in MoreInit.
      destruct (bool_decide (protector_is_active (iprot it0) C)); simpl in MoreInit|-*; simplify_eq.
      all: econstructor 1.
    - simpl in *. assert (itag it = itag it0) as Htageq.
      { rewrite /rel_dec in Hreldec. do 2 (destruct decide; try done).
        eapply mutual_parent_child_implies_equal. 1: done. 1: eapply Lkup. all: done. }
      assert (it = it0) as ->.
      { eapply tree_determined_unify. 1, 2: eapply Lkup. rewrite Htageq. eapply Lookup0. }
      rewrite Htginit in MoreInit|-*. rewrite Htgactive in Inner. simplify_eq.
      rewrite bool_decide_true // /= in MoreInit. simplify_eq.
      destruct (item_lookup it0 loc) as [ii pp]. simpl in *; subst ii pp. econstructor 1.
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
    no_protected_reserved_interiormut pk rk →
    tree_equal tr1 tr2 →
    create_child C tg_old tg_new pk rk cid tr1 = Some tr1' →
    ∃ tr2', create_child C tg_old tg_new pk rk cid tr2 = Some tr2' ∧
      tree_equal tr1' tr2'.
  Proof.
    intros Hwf1 Hwf2 Hiwf1 Hiwf2 Hcidwf.
    rewrite /create_child.
    pose (create_new_item tg_new pk rk cid) as it_new. fold it_new.
    assert (itag it_new = tg_new) as Htgnew by done.
    intros Hcontains1 Hnotcont1 Hhack (H1&H2&H3) [= <-].
    assert (tg_old ≠ tg_new) as Htgsne by (intros ->; firstorder).
    pose proof Hcontains1 as Hcontains2. setoid_rewrite H1 in Hcontains2.
    pose proof Hnotcont1 as Hnotcont2. setoid_rewrite H1 in Hnotcont2.
    epose proof create_new_item_wf _ _ _ _ _ Hcidwf Hhack as Hitemwf.
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
      inversion Heq2 as [|pi im c1 c2 Hi1 Hi2 Hi3 Hi4 Hi5| |p1 p2 Hi2 Hi3 Hi4 Hi5|witness_tg ? ? Dis1 Dis2|???? witness_tg Frz1 Frz2]; simplify_eq.
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
      + destruct Hlu1 as (Hlu1A&Hlu1B), Hlu2 as (Hlu2A&Hlu2B).
        pose proof Hcont as Hcont2. setoid_rewrite H1 in Hcont2. econstructor 4.
        * inversion Hi2 as [|tg_cs it_cs X1 X2 Hii1 Hii2 Hii3 Hii4]; simplify_eq; first by econstructor 1.
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
        * inversion Hi3 as [|tg_cs it_cs X1 X2 Hii1 Hii2 Hii3 Hii4]; simplify_eq; first by econstructor 1.
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
      + econstructor 5.
        * eapply disabled_in_practice_create_child_irreversible; last reflexivity.
          -- lia.
          -- inversion Dis1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (tg_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
          -- eassumption.
        * eapply disabled_in_practice_create_child_irreversible; last reflexivity.
          -- lia.
          -- inversion Dis1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (tg_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
          -- eassumption.
        * auto.
      + econstructor 6.
        * eapply frozen_in_practice_create_child_irreversible; last reflexivity.
          -- lia.
          -- inversion Frz1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (tg_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
        * eapply frozen_in_practice_create_child_irreversible; last reflexivity.
          -- lia.
          -- inversion Frz1 as [it_witness ?? LuWitness].
             pose proof (tree_determined_specifies_tag _ _ _ (proj1 LuWitness) (proj2 LuWitness)) as itag_witness_spec.
             pose proof ((proj1 (every_node_iff_every_lookup (wf_tree_tree_item_determined _ Hwf1)) Hiwf1 witness_tg it_witness ltac:(assumption)).(item_tag_valid _ _ _) witness_tg itag_witness_spec).
             enough (tg_new ≠ witness_tg) by eassumption.
             lia.
          -- eassumption.
  Qed.

  Lemma trees_equal_create_child trs1 trs2 trs1' blk tg_new tg_old pk rk cid nxtc :
    wf_trees trs1 → wf_trees trs2 →
    trees_compat_nexts trs1 tg_new nxtc → trees_compat_nexts trs2 tg_new nxtc →
    (cid < nxtc)%nat →
    trees_contain tg_old trs1 blk →
    ¬ trees_contain tg_new trs1 blk →
    no_protected_reserved_interiormut pk rk →
    trees_equal trs1 trs2 →
    apply_within_trees (create_child C tg_old tg_new pk rk cid) blk trs1 = Some trs1' →
    ∃ trs2', apply_within_trees (create_child C tg_old tg_new pk rk cid) blk trs2 = Some trs2' ∧
      trees_equal trs1' trs2'.
  Proof.
    intros Hwf1 Hwf2 Hiwf1 Hiwf2 Hcidwf Hcont Hncont Hhack Heq.
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
    - done.
  Qed.

  Lemma trees_equal_find_equal_tag_protected_initialized_not_disabled trs1 trs2 it1 tg blk off:
    each_tree_protected_parents_not_disabled C trs2 →
    wf_trees trs2 →
    trees_equal trs1 trs2 →
    trees_lookup trs1 blk tg it1 →
    (initialized (item_lookup it1 off) = PermInit → perm (item_lookup it1 off) ≠ Disabled) →
    protector_is_active it1.(iprot) C →
    ∃ it2, trees_lookup trs2 blk tg it2 ∧
      (initialized (item_lookup it2 off) = PermInit → perm (item_lookup it2 off) ≠ Disabled) ∧
      protector_is_active it2.(iprot) C.
  Proof.
    intros Heach Hwf Heq (tr1&Htr1&Hit) Hperm Hactive.
    specialize (Heq blk). rewrite Htr1 in Heq. inversion Heq as [x tr2 Heq' Hx Htr2|]. subst x.
    destruct Heq' as (Heq1&Heq2&Heq3).
    pose proof Hit as (Hitin&Hitdet).
    specialize (Heq3 _ Hitin) as (it1'&it2&Hit1'&Hit2&Heqit).
    assert (it1 = it1') as <-.
    { eapply tree_determined_unify. 2: done. 1: done. apply Hit1'. }
    exists it2. specialize (Heqit off) as (Hprotit&Hlocit).
    split. 1: exists tr2; done.
    rewrite -Hprotit. inversion Hlocit as [|e m c1 c2 H H1 H2 H3 H4| | | |]; simplify_eq.
    - done.
    - rewrite -!H3 /= in Hperm. simpl. done.
    - exfalso. done.
    - done.
    - split; last done. intros Hinit Hdis.
      ospecialize (Heach _ _ _ tg). 1: symmetry; exact Htr2.
      eapply every_child_ParentChildIn in Heach. 2: by eapply Hwf. 2,4: eapply Hwf; first done; eapply Hit2.
      2: eapply Hit2. 2: by left.
      rewrite every_node_eqv_universal in Heach. ospecialize (Heach it2 _ _ off _ _ Hdis).
      1: eapply exists_determined_exists; eapply Hit2. 1: by eapply tree_lookup_correct_tag.
      1: done. 1: by rewrite -Hprotit. done.
    - split; last done. simpl. done.
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

  Lemma tree_equal_transfer_item_non_disabled tr1 tr2 tg it off :
    protected_parents_not_disabled C tr1 →
    no_active_cousins C tr1 →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    tree_equal tr1 tr2 →
    tree_lookup tr1 tg it →
    protector_is_active (iprot it) C ∧ perm (item_lookup it off) ≠ Disabled ∧ initialized (item_lookup it off) = PermInit →
    ∃ it2, tree_lookup tr2 tg it2 ∧ protector_is_active (iprot it2) C ∧ perm (item_lookup it2 off) ≠ Disabled ∧ initialized (item_lookup it2 off) = PermInit.
  Proof.
    intros Hpnd Hnac Hunq (He1&He2&He3) Hlu (Hprot&Hndis&Hini).
    destruct (He3 tg) as (it1&it2&Hlu1&Hlu2&Heq).
    1: eapply Hlu.
    assert (it = it1) as -> by by eapply tree_lookup_unique.
    exists it2. specialize (Heq off) as (Hproteq&Hiteq). split; first done.
    split. 1: by rewrite -Hproteq.
    inversion Hiteq as [pp1|ini1 im1 confl1 confl2 HprotX HP1 HP2 Heq1 Heq2|ini1 im1 confl1 confl2 HnoProt|p1 p2 HP1 HP2 Heq1 Heq2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX Heq1 Heq2|ini1 im1 confl1 confl2 wit_tg HF1 HF2 Heq1 Heq2]; simplify_eq.
    - done.
    - split; first done. rewrite -Heq1 /= in Hini. rewrite /= Hini //.
    - rewrite -Heq1 in Hini. done.
    - exfalso.
      inversion Hdip1 as [itw p Hreldec Hluw Hdisw].
      rewrite /rel_dec in Hreldec. destruct decide; last done.
      eapply tree_lookup_correct_tag in Hlu as HH. subst tg.
      specialize (Hpnd wit_tg). eapply every_child_ParentChildIn in Hpnd.
      2: eapply Hunq. 2: eapply Hunq, Hluw. 2: eapply Hluw. 2: eapply Hunq, Hlu.
      2: done.
      eapply every_node_eqv_universal in Hpnd.
      2: { eapply tree_lookup_to_exists_node. eapply Hlu. }
      inversion Hdisw as [X1 HH X2|pp X2 Hdis Hlazy X5]; simplify_eq.
      { unshelve eapply (Hpnd _ off); [done..|by rewrite -HH]. }
      inversion Hdis as [X1 HH X2|tgcs itcs lp X1 Hcs Hlucs Hprotcs Hactcs HH X2 X3]; simplify_eq.
      { unshelve eapply (Hpnd _ off). 1-3: done. rewrite -Hlazy. done. }
      eapply Hnac. 2: eapply Hlucs. 1: eapply Hlu. 3: by erewrite Hactcs.
      2: right; split; done.
      eapply child_of_this_is_foreign_for_cousin. 4: exact Hcs.
      1-3: eapply Hunq. 1: eapply Hluw. 1: eapply Hlucs. 1: eapply Hlu.
      rewrite /rel_dec decide_True //.
    - split; first done. rewrite -Heq1 /= in Hini. rewrite /= Hini //.
 Qed.

  Lemma tree_equal_transfer_pseudo_conflicted tr1 tr2 tg off confl :
    protected_parents_not_disabled C tr1 →
    no_active_cousins C tr1 →
    (∀ tg, tree_contains tg tr1 → tree_unique tg tr1) →
    tree_equal tr1 tr2 →
    pseudo_conflicted tr1 tg off confl →
    pseudo_conflicted tr2 tg off confl.
  Proof.
    intros Hpnd Hnac Hunq (HH1&HH2&HH3) Hconfl.
    inversion Hconfl as [|tg_cs it_cs Hcs Hlu Hprot Hperm Hini]; simplify_eq.
    - econstructor 1.
    - edestruct tree_equal_transfer_item_non_disabled as (it2&Hit2&Hprot2&Hndis2&Hini2).
      1: exact Hpnd. 1: exact Hnac. 1: exact Hunq. 1: split; done. 1: exact Hlu.
      1: split; done.
      econstructor 2. 1: by erewrite <- HH2. 1: exact Hit2.
      all: done.
  Qed.

  Global Instance pseudo_disabled_dec tr tg off pp oprot : Decision (pseudo_disabled tr tg off pp oprot).
  Proof.
    destruct (decide (pp = Disabled)) as [->|Hne].
    1: left; econstructor 1.
    pose (P it_cs := let tg_cs := itag it_cs in
                     rel_dec tr tg tg_cs = Foreign Cousin ∧
                     tree_item_determined tg_cs it_cs tr ∧
                     protector_is_active (iprot it_cs) C ∧
                     item_lookup it_cs off = mkPerm PermInit Active ∧
                     match pp with Reserved InteriorMut _ => False | _ => True end).
    assert (∀ it, Decision (P it)) as DecP.
    { intros it.
      rewrite /P.
      do 4 (eapply and_dec; first eapply _).
      destruct pp as [[]?| | |].
      all: eapply _. }
    destruct (decide (exists_node P tr)) as [HP|HnP].
    - left. eapply exists_node_eqv_existential in HP as (it&Htgit&H1&H2&H3&H4&H5).
      econstructor 2.
      1: exact H1. 1: split. 2: exact H2.
      1: eapply exists_node_eqv_existential; exists it; done.
      1: done. 1: done.
      1: intros ? ->. done.
    - right. intros Hdis.
      induction Hdis as [|tg_cs it_cs lp Hlp H1 H2 H3 H4 H5]; first done.
      eapply HnP. eapply exists_node_eqv_existential.
      exists it_cs. split. 1: eapply tree_lookup_to_exists_node; done.
      assert (itag it_cs = tg_cs) as <- by by eapply tree_lookup_correct_tag.
      split; first done.
      split; first eapply H2.
      split; first done.
      split; first done. 
      destruct lp as [[]?| | |]; try done.
      eapply H5. done.
  Defined.

  Global Instance is_disabled_dec tr tg off lp oprot : Decision (is_disabled tr tg off lp oprot).
  Proof.
    destruct (decide (lp = mkPerm PermInit Disabled)) as [->|Hne].
    1: left; econstructor 1.
    destruct lp as [[] pp].
    1: { right. intros HH. inversion HH. subst pp. done. }
    destruct (decide (pseudo_disabled tr tg off pp oprot)) as [Hpd|Hnpd].
    1: left; econstructor 2; done.
    right.
    intros HH. inversion HH; simplify_eq.
  Qed.

  Lemma trees_equal_decide_disabled_in_practice tr tg off :
    (∀ tg, tree_contains tg tr → tree_unique tg tr) →
    tree_contains tg tr →
    (∃ tgp itp, tree_lookup tr tgp itp ∧ is_disabled tr tgp off (item_lookup itp off) (iprot itp) ∧ ParentChildIn tgp tg tr ∧ 
          ∀ tgpp itpp, tree_lookup tr tgpp itpp → StrictParentChildIn tgpp tgp tr → ¬ is_disabled tr tgpp off (item_lookup itpp off) (iprot itpp))
    + (∀ tgp itp, tree_lookup tr tgp itp → ParentChildIn tgp tg tr → ¬ is_disabled tr tgp off (item_lookup itp off) (iprot itp)).
  Proof.
    intros Hunq H.
    assert (Decision (exists_node (λ it, is_disabled tr (itag it) off (item_lookup it off) (iprot it) ∧ ParentChildIn (itag it) tg tr) tr)) as Hdec.
    { eapply exists_node_dec. intros itx. eapply and_dec. 2: by eapply ParentChildIn_dec. apply _. }
    destruct Hdec as [Hleft|Hright].
    - left.
      edestruct (find_highest_parent_with_property (λ x, is_disabled tr (itag x) off (item_lookup x off) (iprot x) ∧ ParentChildIn (itag x) tg tr)) as (tgpp&Htgpp&Hppp).
      { intros x. eapply and_dec. 2: by eapply ParentChildIn_dec. apply _. }
      { done. }
      { done. }
      eapply exists_node_eqv_existential in Htgpp. destruct Htgpp as (itpp&Hitpp&(HHitpp1&HHitpp2)&<-).
      eapply exists_node_to_tree_lookup in Hitpp. 2: done.
      exists (itag itpp), itpp. do 3 (split; first done).
      intros tgppp itppp Hitppp HSPppp Hdis.
      eapply Hppp. 2: exact HSPppp.
      eapply tree_lookup_correct_tag in Hitppp as Htg. subst tgppp.
      eapply exists_node_eqv_existential. exists itppp.
      split. 2: split_and!; try done. 1: by eapply tree_lookup_to_exists_node.
      eapply ParentChild_transitive; [|exact HHitpp2]; right; done.
    - right. intros tgp itp Hlu HPC Hdis. eapply tree_lookup_correct_tag in Hlu as Htg; subst tgp.
      eapply Hright. eapply exists_node_eqv_existential.
      eexists. split. 1: eapply tree_lookup_to_exists_node, Hlu. split; done.
  Qed.

  Lemma tree_equal_transfer_pseudo_disabled {tr tr2 tgcld off lp pp} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    pseudo_disabled tr2 tgcld off lp pp →
    tree_equal tr tr2 → pseudo_disabled tr tgcld off lp pp.
  Proof.
    intros Hunq Hwf1 Hwf2 HH (He1&He2&He3).
    induction HH as [|tg_cs it_cs lp prot H1 H2 H3 H4 H5].
    1: econstructor 1.
    edestruct He3 as (it_cs1&X&Hit_cs1&HX&Hiteq).
    1: eapply He1, H2.
    assert (X = it_cs) as -> by by eapply tree_lookup_unique.
    specialize (Hiteq off) as (Hprot&Hiteq).
    econstructor 2. 2: exact Hit_cs1.
    1: by rewrite He2.
    1: rewrite Hprot //.
    2: done.
    rewrite H4 in Hiteq.
    inversion Hiteq; simplify_eq. 1: congruence.
    exfalso. eapply disabled_in_practice_not_active.
    5: erewrite H4; done.
    4: done. 1: done. 3: eassumption. all: done.
  Qed.

  Lemma conflicted_transfer_pseudo_disabled c1 c2 imm tr tg off pp :
    pseudo_disabled tr tg off (Reserved imm c1) pp →
    pseudo_disabled tr tg off (Reserved imm c2) pp.
  Proof.
    inversion 1 as [|X1 X2 X3 X4 X5 X6 X7 X8 X9]; econstructor.
    1-4: done. intros ? [= ->]. eapply X9. done.
  Qed.

  Lemma tree_equal_transfer_is_disabled {tr tr2 tgcld off lp pp} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    is_disabled tr2 tgcld off lp pp →
    tree_equal tr tr2 → is_disabled tr tgcld off lp pp.
  Proof.
    intros Hunq ?? Hdis Heq.
    induction Hdis as [|lp prot HH].
    1: econstructor 1.
    econstructor 2.
    by eapply tree_equal_transfer_pseudo_disabled.
  Qed.
    

  Lemma trees_equal_transfer_disabled_in_practice_many {tr2 tgpar tgcld off} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    disabled_in_practice tr2 tgcld tgpar off →
    ∃ tgpar',
      disabled_in_practice tr2 tgcld tgpar' off ∧
      ∀ tr', tree_equal tr2 tr' → disabled_in_practice tr' tgcld tgpar' off.
  Proof.
    intros Hunq1 Hwf1 Hwf2 Hdip.
    inversion Hdip as [itw incl Hrel Hlu Hperm].
    rewrite /rel_dec in Hrel. destruct decide as [HPCo|?]; try done.
    destruct (trees_equal_decide_disabled_in_practice tr2 tgcld off) as [(tgp&itp&Hlup&Hdisp&HPC&Hothers)|HR].
    1: done.
    { eapply contains_child. 1: done. eapply Hlu. }
    2: { exfalso. eapply HR. 1: exact Hlu. 1: done. done. }
    exists tgp. split_and!.
    { econstructor. 2: exact Hlup. 2: done. rewrite /rel_dec decide_True //. }
    intros tr1 (Heq1&Heq2&Heq3).
    destruct (Heq3 tgp) as (itp'&itp2&Hitp'&Hitp2&Heq).
    1: eapply Hlup.
    assert (itp = itp') as <- by by eapply tree_lookup_unique.
    specialize (Heq off) as (Hprot&Heq).
    inversion Heq as [pp1 X1 HH|ini1 im1 confl1 confl2 HprotX HP1 HP2 HeqX1 HeqX2|ini1 im1 confl1 confl2 HnoProt HeqX1 HeqX2|p1 p2 HP1 HP2 HeqX1 HeqX2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX HeqX1 HeqX2|ini1 im1 confl1 confl2 wit_tg HF1 HF2 HeqX1 HeqX2]; simplify_eq.
    - econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      rewrite -HH -Hprot.
      eapply tree_equal_transfer_is_disabled. 1-3: eassumption. 2: eapply tree_equal_sym; done. done.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      by eapply conflicted_transfer_pseudo_disabled.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      by eapply conflicted_transfer_pseudo_disabled.
    - econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      rewrite -HeqX2. econstructor 2. rewrite -Hprot. done.
    - inversion Hdip2 as [itwF incl H1 H2 H3].
      inversion Hdip1 as [itwF' incl' H1' H2' H3'].
      assert (incl = incl') as <-.
      { rewrite Heq2 H1 in H1'. by simplify_eq. }
      rewrite /rel_dec in H1'. destruct decide as [HPCF|] in H1'; last done.
      clear H1'. destruct HPCF as [<-|Hne].
      1: { assert (itwF = itp2) as <- by by eapply tree_lookup_unique.
           econstructor. 2: exact Hitp2.
           1: rewrite -Heq2 /rel_dec decide_True //. done. }
      exfalso. eapply Hothers. 2: exact Hne. 1: done. done.
    - rewrite -HeqX1 in Hdisp.
      econstructor. 2: exact Hitp2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      inversion Hdisp as [|lp prot HH1 HH2 HH3]; simplify_eq.
      rewrite -HeqX2 -Hprot. econstructor 2.
      eapply tree_equal_transfer_pseudo_disabled in HH1. 2-4: done. 2: by eapply tree_equal_sym.
      by eapply conflicted_transfer_pseudo_disabled.
  Qed.

  Lemma trees_equal_transfer_disabled_in_practice_twice {tr1 tr2 tr3 tgpar tgcld off} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal tr1 tr2 →
    tree_equal tr2 tr3 →
    disabled_in_practice tr2 tgcld tgpar off →
    ∃ tgpar',
      disabled_in_practice tr1 tgcld tgpar' off ∧
      disabled_in_practice tr2 tgcld tgpar' off ∧
      disabled_in_practice tr3 tgcld tgpar' off.
  Proof.
    intros H1 Hu1 Hu2 H2%tree_equal_sym H3 Hdip.
    odestruct trees_equal_transfer_disabled_in_practice_many as (tg&Htg&Htg2).
    1: exact H1. 1-2: done. 1: exact Hdip.
    exists tg. split_and!.
    - by eapply Htg2.
    - done.
    - by eapply Htg2.
  Qed.

  Lemma trees_equal_transfer_frozen_in_practice_many {tr2 tgpar tgcld off} :
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    frozen_in_practice tr2 tgcld tgpar off →
    ∃ tgpar',
      (frozen_in_practice tr2 tgcld tgpar' off ∧
       ∀ tr', tree_equal tr2 tr' → frozen_in_practice tr' tgcld tgpar' off) ∨
      (disabled_in_practice tr2 tgcld tgpar' off ∧
       ∀ tr', tree_equal tr2 tr' → disabled_in_practice tr' tgcld tgpar' off).
  Proof.
    intros Hunq1 Hwf1 Hwf2 Hdip.
    inversion Hdip as [itw incl Hrel Hlu Hperm Hinit].
    rewrite /rel_dec in Hrel. destruct decide as [HPCo|?]; try done.
    destruct (trees_equal_decide_disabled_in_practice tr2 tgcld off) as [(tgp&itp&Hlup&Hdisp&HPC&Hothers)|HR].
    1: done.
    { eapply contains_child. 1: done. eapply Hlu. }
    - odestruct trees_equal_transfer_disabled_in_practice_many as (tg&Htg).
      1: exact Hunq1. 1-2: done. 2: { exists tg. right. exact Htg. }
      econstructor. 3: done. 2: done. rewrite /rel_dec decide_True //.
    - exists tgpar. left. split.
      1: done.
      intros tr1 (Heq1&Heq2&Heq3).
      destruct (Heq3 tgpar) as (itw'&itw2&Hitw'&Hitw2&Heq).
      1: eapply Hlu.
      assert (itw = itw') as <- by by eapply tree_lookup_unique.
      assert (item_lookup itw2 off = mkPerm PermInit Frozen) as Hitlu.
      { specialize (Heq off) as (HeqL1&HeqL2).
        inversion HeqL2 as [pp1|ini1 im1 confl1 confl2 HprotX HP1 HP2 HeqX1 HeqX2|ini1 im1 confl1 confl2 HnoProt HeqX1 HeqX2|lp1 lp2 Hdip1 Hdip2 HeqX1 HeqX2|wit_tg lp1 lp2 Hdip1 Hdip2 HiniX HeqX1 HeqX2|ini1 im1 confl1 confl2 wit_tg HF1 HF2 HeqX1 HeqX2]; simplify_eq.
        + destruct item_lookup; simpl in *; simplify_eq. done.
        + rewrite -HeqX1 // in Hperm.
        + rewrite -HeqX1 // in Hperm.
        + rewrite -HeqX1 // in Hinit.
        + inversion Hdip1 as [itw1' incl1 Hrel1 Hlu1 Hperm1].
          rewrite /rel_dec in Hrel1. destruct decide as [HPC1|?] in Hrel1; last done.
          eapply HR in Hperm1. 1: done. 1: done.
          eapply ParentChild_transitive. 2: eassumption. done.
        + rewrite -HeqX1 // in Hperm. }
      econstructor. 2: exact Hitw2.
      1: rewrite -Heq2 /rel_dec decide_True //.
      all: by rewrite Hitlu.
  Qed.

  Lemma perm_eq_up_to_C_trans {tr1 tr2 tr3 tg l cid perm1 perm2 perm3} :
    protected_parents_not_disabled C tr2 →
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal tr1 tr2 →
    tree_equal tr2 tr3 →
    perm_eq_up_to_C tr1 tr2 tg l cid perm1 perm2 →
    perm_eq_up_to_C tr2 tr3 tg l cid perm2 perm3 →
    perm_eq_up_to_C tr1 tr3 tg l cid perm1 perm3.
  Proof.
    intros Hpnd Hunq Hpma Hnac Heq12 Heq23 EqC1 EqC2.
    inversion EqC1 as [pp1|ini1 im1 confl1 confl2 Hprot HP1 HP2|ini1 im1 confl1 confl2 HnoProt|p1 p2 HP1 HP2|wit_tg lp1 lp2 Hdip1 Hdip2 Hini|ini1 im1 confl1 confl2 wit_tg HF1 HF2]; simplify_eq;
    inversion EqC2 as [pp1'|ini1' im1' confl1' confl2' Hprot' HP1' HP2'|ini1' im1' confl1' confl2' HnoProt'|p1' p2' HP1' HP2'|wit_tg' lp1 lp2 Hdip1' Hdip2' Hini'|ini1' im1' confl1' confl2' wit_tg' HF1' HF2']; simplify_eq.
    (* easy case: perm1 = perm2 *)
    + econstructor 1.
    + econstructor 2. 1: done. 2: done.
      eapply tree_equal_transfer_pseudo_conflicted. 1: done. 1: done. 1: done.
      1: by eapply tree_equal_sym. done.
    + by econstructor 3.
    + econstructor 4. 2: done.
      eapply tree_equal_transfer_pseudo_disabled. 2: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. congruence.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF1' as (tr&[(Hfip&Hfip2)|(Hdi9p&Hdip2)]). 3-5: eassumption.
      * econstructor 6. all: eapply Hfip2. 2: done. 1: by eapply tree_equal_sym.
      * econstructor 5; last done. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    (* case 2: perm1 and perm2 are pseudo_conflicted Reserved *)
    + econstructor 2. 1: done. 1: done.
      eapply tree_equal_transfer_pseudo_conflicted. 5: exact HP2. all: done.
    + econstructor 2; done.
    + exfalso. done.
    + econstructor 4. 2: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 4: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor 5. 1: exact Hw1. 1: exact Hw3. simpl in *. eapply Hini'.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF1' as (tr&[(Hfip&Hfip2)|(Hdi9p&Hdip2)]). 3-5: eassumption.
      * econstructor 6. all: eapply Hfip2. 2: done. 1: by eapply tree_equal_sym.
      * econstructor 5; last done. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    (* case 3: perm1 and perm2 are unprotected reserved *)
    + by econstructor 3.
    + exfalso. done.
    + by econstructor 3.
    + econstructor 4. 2: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 4: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + by econstructor 3.
    (* case 4: perm1 and perm2 are pseudo-disabled *)
    + econstructor 4. 1: done.
      eapply tree_equal_transfer_pseudo_disabled. 2: done. 4: by eapply tree_equal_sym. all: done.
    + econstructor 4. 1: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 2: done. 4: by eapply tree_equal_sym. all: done.
    + econstructor 4. 1: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 2: done. 4: by eapply tree_equal_sym. all: done.
    + econstructor 4. all: done. 
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + econstructor 4. 1: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 2: done. 4: by eapply tree_equal_sym. all: done.
    (* case 5: perm1 and perm2 are disabled in practice *)
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. congruence.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    (* case 6: perm1 and perm2 are frozen in practice. *)
    + eapply trees_equal_transfer_frozen_in_practice_many in HF2 as (tr&[(Hfip&Hfip2)|(Hdi9p&Hdip2)]). 3-5: eassumption.
      * econstructor 6. all: eapply Hfip2. 2: done. 1: by eapply tree_equal_sym.
      * econstructor 5; last done. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF2 as (tr&[(Hfip&Hfip2)|(Hdi9p&Hdip2)]). 3-5: eassumption.
      * econstructor 6. all: eapply Hfip2. 2: done. 1: by eapply tree_equal_sym.
      * econstructor 5; last done. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF2 as (tr&[(Hfip&Hfip2)|(Hdi9p&Hdip2)]). 3-5: eassumption.
      * econstructor 6. all: eapply Hfip2. 2: done. 1: by eapply tree_equal_sym.
      * econstructor 5; last done. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
    + econstructor 4. 2: done.
      eapply conflicted_transfer_pseudo_disabled.
      eapply tree_equal_transfer_pseudo_disabled. 2: done. all: done.
    + odestruct (trees_equal_transfer_disabled_in_practice_twice Hunq Hpma Hnac Heq12 Heq23) as (ww&Hw1&Hw2&Hw3).
      1: done. econstructor. 1: exact Hw1. 1: exact Hw3. simpl in *. done.
    + eapply trees_equal_transfer_frozen_in_practice_many in HF2 as (tr&[(Hfip&Hfip2)|(Hdi9p&Hdip2)]). 3-5: eassumption.
      * econstructor 6. all: eapply Hfip2. 2: done. 1: by eapply tree_equal_sym.
      * econstructor 5; last done. all: eapply Hdip2. 2: done. 1: by eapply tree_equal_sym.
  Qed.

  Lemma item_eq_up_to_C_trans {tr1 tr2 tr3 tg it1 it2 it3} : 
    protected_parents_not_disabled C tr2 →
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal tr1 tr2 →
    tree_equal tr2 tr3 →
    item_eq_up_to_C tr1 tr2 tg it1 it2 →
    item_eq_up_to_C tr2 tr3 tg it2 it3 →
    item_eq_up_to_C tr1 tr3 tg it1 it3.
  Proof.
    intros Hnd Hu Hu2 Hu3 He1 He2 H1 H2 l.
    destruct (H1 l) as (H1l&H1r), (H2 l) as (H2l&H2r).
    split; first congruence.
    eapply perm_eq_up_to_C_trans. 1-6: done.
    1: exact H1r. rewrite H1l. 1: exact H2r.
  Qed.


  Lemma tree_equal_trans tr1 tr2 tr3 :
    protected_parents_not_disabled C tr2 →
    (∀ tg, tree_contains tg tr2 → tree_unique tg tr2) →
    parents_more_active tr2 →
    no_active_cousins C tr2 →
    tree_equal tr1 tr2 →
    tree_equal tr2 tr3 →
    tree_equal tr1 tr3.
  Proof.
    rewrite /tree_equal.
    intros Hu1 Hu2 Hu3 Hu4 [SameTg1 [SameRel1 EqC1]] [SameTg2 [SameRel2 EqC2]].
    split; [|split].
    + intro tg. rewrite SameTg1 SameTg2 //.
    + intros tg tg'. rewrite SameRel1 SameRel2 //.
    + intros tg Ex.
      destruct (EqC1 _ Ex) as (it1M&it2M&Hlu1M&Hlu2M&Hiteq).
      destruct (EqC2 tg) as (it1R&it2R&Hlu1R&Hlu2R&Hiteq2).
      1: by eapply Hlu2M.
      assert (it2M = it1R) as -> by by eapply tree_lookup_unique.
      exists it1M, it2R. split_and!; [done..|].
      eapply item_eq_up_to_C_trans; done.
  Qed.

  Lemma trees_equal_trans trs1 trs2 trs3 :
    each_tree_protected_parents_not_disabled C trs2 →
    wf_trees trs2 →
    each_tree_parents_more_active trs2 →
    each_tree_no_active_cousins C trs2 →
    trees_equal trs1 trs2 →
    trees_equal trs2 trs3 →
    trees_equal trs1 trs3.
  Proof.
    rewrite /trees_equal.
    intros Hu1 Hu2 Hu3 Hu4 Equals1 Equals2 blk.
    specialize (Equals1 blk). specialize (Equals2 blk).
    destruct (trs1 !! blk) as [tr1|] eqn:Heq1;
    destruct (trs2 !! blk) as [tr2|] eqn:Heq2;
    destruct (trs3 !! blk) as [tr3|] eqn:Heq3.
    all: inversion Equals1; inversion Equals2; simplify_eq; first [exfalso; congruence | econstructor].
    eapply tree_equal_trans. 5-6: eassumption.
    2: by eapply Hu2. 1: by eapply Hu1. 1: by eapply Hu3. 1: by eapply Hu4.
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

  Lemma pseudo_disabled_mono C1 nxtc tr1 tg l p1 cid :
    pseudo_disabled C1 tr1 tg l p1 cid →
    pseudo_disabled (C1 ∪ {[ nxtc ]}) tr1 tg l p1 cid.
  Proof.
    induction 1 as [|???????? HH]. 1: by econstructor 1.
    econstructor 2. 1,2,4: done.
    1: eapply protector_is_active_mono; last done; set_solver.
    intros ? Hc1. by eapply HH.
  Qed.

  Lemma is_disabled_mono C1 nxtc tr1 tg l p1 cid :
    is_disabled C1 tr1 tg l p1 cid →
    is_disabled (C1 ∪ {[ nxtc ]}) tr1 tg l p1 cid.
  Proof.
    induction 1 as [|]. 1: by econstructor 1.
    econstructor 2. eapply pseudo_disabled_mono. done.
  Qed.

  Lemma disabled_in_practice_mono C1 nxtc tr1 tg tg2 l:
    disabled_in_practice C1 tr1 tg tg2 l →
    disabled_in_practice (C1 ∪ {[ nxtc ]}) tr1 tg tg2 l.
  Proof.
    induction 1. econstructor. 1-2: done.
    eapply is_disabled_mono. done.
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
    induction 1 as [| |???? H|?? H1 H2|??? H1 H2 ?|].
    1: by econstructor.
    1: econstructor; try done. 1: eapply protector_is_active_mono; last done; set_solver.
    1-2: eapply pseudo_conflicted_mono; last done; set_solver.
    - econstructor 3; try done.
      apply protector_not_active_extend; assumption.
    - econstructor 4. all: eapply pseudo_disabled_mono; last done; done.
    - econstructor 5; try done.
      all: eapply disabled_in_practice_mono; last done.
    - econstructor 6; done.
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
    apply Hss. eapply tree_lookup_to_exists_node.
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


