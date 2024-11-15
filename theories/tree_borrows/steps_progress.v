(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.tree_borrows Require Export steps_wf.
From Equations Require Import Equations.
From iris.prelude Require Import options.

Lemma alloc_base_step P σ sz :
  state_wf σ ->
  (sz > 0)%nat ->
  let l := (fresh_block σ.(shp), 0) in
  let t := σ.(snp) in
  let σ' := mkState (init_mem l sz σ.(shp))
                    (extend_trees t l.1 0 sz σ.(strs)) σ.(scs) (S t) σ.(snc) in
  base_step P (Alloc sz) σ (Place l t sz) σ' [].
Proof.
  simpl. econstructor.
  - econstructor.
  - apply (AllocIS (strs σ) (scs σ) (snp σ) (snc σ) (fresh_block (shp σ)) 0).
    2: assumption.
    assert (forall i, (fresh_block (shp σ), i) ∉ dom (shp σ)) as FreshHp by apply is_fresh_block.
    apply not_elem_of_dom.
    rewrite state_wf_dom; [|assumption].
    intro FreshMap.
    destruct (elem_of_map_1 fst (dom (shp σ)) (fresh_block (shp σ)) FreshMap) as [[blk z] [Fresh Dom]].
    apply (FreshHp z).
    rewrite Fresh; simpl.
    exact Dom.
Qed.


Lemma apply_access_success_condition tr cids access_tag range fn :
  every_node (fun it => is_Some (item_apply_access fn cids (rel_dec tr access_tag (itag it)) range it)) tr
  <-> is_Some (tree_apply_access fn cids access_tag range tr).
Proof.
  rewrite /tree_apply_access.
  rewrite join_success_condition.
  rewrite every_node_map /compose.
  tauto.
Qed.


Lemma apply_access_fail_condition tr cids access_tag range fn :
  exists_node (fun it => item_apply_access fn cids (rel_dec tr access_tag (itag it)) range it = None) tr
  <-> tree_apply_access fn cids access_tag range tr = None.
Proof.
  rewrite /tree_apply_access.
  rewrite join_fail_condition.
  rewrite exists_node_map /compose.
  tauto.
Qed.

Lemma mem_apply_range'_success_condition {X} (map : gmap Z X) fn range :
  (forall l, range'_contains range l -> is_Some (fn (map !! l))) <->
  is_Some (mem_apply_range' fn range map).
Proof.
  destruct range as [z sz].
  generalize dependent z.
  generalize dependent map.
  induction sz as [|sz IHsz]; intros map z.
  - rewrite /mem_apply_range' //=.
    split; intro.
    + econstructor; reflexivity.
    + rewrite /range'_contains; simpl. intros. lia.
  - split.
    + intro PerLoc.
      rewrite /mem_apply_range' //= /mem_apply_loc.
      destruct (PerLoc z) as [? H]. { rewrite /range'_contains //=; lia. }
      rewrite H //=.
      rewrite /mem_apply_range' //= in IHsz.
      eapply IHsz.
      intros l Contains.
      rewrite lookup_insert_ne.
      * apply PerLoc. rewrite /range'_contains //= in Contains |- *. lia.
      * rewrite /range'_contains //= in Contains. lia.
    + intros Success l InRange.
      inversion Success as [map' App'].
      rewrite /mem_apply_range' /= in App'.
      remember (mem_apply_loc _ _ _) as AppLoc eqn:HeqAppLoc.
      destruct AppLoc as [map''|]; last discriminate.
      simpl in *.
      destruct (decide (l = z)).
      * subst; simpl in *.
        rewrite /mem_apply_loc in HeqAppLoc.
        destruct (fn _); last discriminate; auto.
      * assert (range'_contains (z+1, sz) l) as InSubRange. {
          rewrite /range'_contains in InRange |- *. simpl in *. lia.
        }
        assert (map'' !! l = map !! l) as Eql. {
          rewrite /mem_apply_loc in HeqAppLoc.
          destruct (fn _); [simpl in *|discriminate].
          injection HeqAppLoc; intros; subst.
          rewrite lookup_insert_ne; [reflexivity|lia].
        }
        rewrite <- Eql.
        rewrite /mem_apply_loc in HeqAppLoc.
        assert (is_Some (mem_apply_range' fn (z+1, sz) map'')) as App''. {
         eexists. rewrite /mem_apply_range'. simpl. apply App'.
        }
        apply (proj2 (IHsz _ _) App'' l InSubRange).
Qed.

Lemma mem_apply_range'_fail_condition {X} (map : gmap Z X) fn range : 
  mem_apply_range' fn range map = None ↔
  ∃ l, range'_contains range l ∧ fn (map !! l) = None.
Proof.
  destruct range as [z n].
  rewrite /mem_apply_range' /range'_contains /=.
  induction n as [|n IH] in z,map|-*.
  { simpl. split; try done. intros (l&Hl1&Hl2). lia. }
  simpl; split.
  - intros [H|(x&H1&H2)]%bind_None.
    + exists z. simpl. split; first lia. eapply bind_None in H as [H|(y&Hy1&Hy2)]. 2: done.
      done.
    + destruct (IH x (z+1)) as (IH1&IH2). specialize (IH1 H2) as (l&Hl1&Hl2).
      exists l. split; first lia.
      eapply bind_Some in H1 as (x1&Hx1&[= <-]). rewrite lookup_insert_ne // in Hl2. lia.
  - intros (l&Hl1&Hl2). destruct (decide (l = z)) as [->|Hne].
    + rewrite /mem_apply_loc Hl2 /=. done.
    + destruct (mem_apply_loc fn z map) as [map2|] eqn:Hmap. 2: done.
      simpl. eapply IH. exists l. split; first lia.
      eapply bind_Some in Hmap as (x1&Hx1&[= <-]). rewrite lookup_insert_ne //.
Qed.


Definition is_access_compatible (tr : tree item) (cids : call_id_set) (tg : tag) (range : range') (kind : access_kind) (it : item ) :=
  forall l, range'_contains range l ->
    let initial := item_lookup it l in
    let protected := bool_decide (protector_is_active (iprot it) cids) in
    let rd := (rel_dec tr tg (itag it)) in
    exists post,
      apply_access_perm_inner kind rd protected (perm initial) = Some post
      /\ (post = Disabled -> (most_init (initialized initial) (requires_init rd) = PermLazy \/ protected = false)).

Lemma option_bind_always_some {X Y} (o : option X) (fn : X -> option Y) :
  is_Some o ->
  (forall i, is_Some (fn i)) ->
  is_Some (o ≫= fn).
Proof.
  intros oSome fnSome.
  destruct o; [|inversion oSome; discriminate].
  simpl.
  apply fnSome.
Qed.

Lemma option_bind_assoc {X Y Z} (o : option X) (f : X -> option Y) (g : Y -> option Z) :
  ((o ≫= fun i => f i) ≫= fun i => g i)
  = o ≫= (fun i => f i ≫= fun i => g i).
Proof.
  destruct o; simpl; done.
Qed.

Lemma all_access_compatible_implies_access_success kind tr cids tg range :
  every_node (is_access_compatible tr cids tg range kind) tr ->
  is_Some (memory_access kind cids tg range tr).
Proof.
  intro Compat. apply apply_access_success_condition.
  eapply every_node_increasing; [exact Compat|simpl].
  rewrite every_node_eqv_universal.
  intros it Ex CompatIt.
  rewrite /item_apply_access.
  apply option_bind_always_some; auto.
  simpl.
  rewrite /permissions_apply_range'.
  apply mem_apply_range'_success_condition.
  rewrite /apply_access_perm.
  intros l Range. specialize (CompatIt l Range).
  rewrite <- option_bind_assoc.
  apply option_bind_always_some; auto. 
  destruct CompatIt as [post [PostSpec ProtVulnerable]].
  rewrite PostSpec //=.
  change (default _ _) with (item_lookup it l).
  destruct (most_init _ _) eqn:Heq; last done.
  destruct (bool_decide (protector_is_active _ _)); [|done].
  destruct (decide (post = Disabled)); last first.
  1: { destruct post; auto. contradiction. }
  subst; auto.
  destruct (ProtVulnerable ltac:(reflexivity)); discriminate.
Qed.



(*
Lemma dealloc1_progress stk bor cids
  (PR: Forall (λ it, ¬ is_active_protector cids it) stk)
  (BOR: ∃ it, it ∈ stk ∧ it.(tg) = bor ∧
        it.(perm) ≠ Disabled ∧ it.(perm) ≠ SharedReadOnly) :
  is_Some (dealloc1 stk bor cids).
Proof.
  rewrite /dealloc1.
  destruct (find_granting_is_Some stk AccessWrite bor) as [? Eq]; [naive_solver|].
  rewrite Eq /find_top_active_protector list_find_None_inv;
    [by eexists|done].
Qed.

Lemma for_each_is_Some α l (n: nat) b f :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk → is_Some (f stk)) →
  is_Some (for_each α l n b f).
Proof.
  revert α. induction n as [|n IHn]; intros α IN Hf; [by eexists|]. simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stk Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=. destruct (Hf n stk) as [stk' Eq']; [lia|done|].
  rewrite Eq' /=. destruct b; apply IHn.
  - intros. apply elem_of_dom. rewrite lookup_delete_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_delete_ne.
    + apply Hf. lia.
    + move => /shift_loc_inj. lia.
  - intros. apply elem_of_dom. rewrite lookup_insert_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_insert_ne.
    + apply Hf. lia.
    + move => /shift_loc_inj. lia.
Qed.
*)

(* For a protector to allow deallocation it must be weak or inactive *)
Definition item_deallocateable_protector cids (it: item) :=
  match it.(iprot) with
  | Some {| strong:=strong; call:=c |} => ¬ call_is_active c cids \/ strong = ProtWeak
  | _ => True
  end.

(* Deallocation progress is going to be a bit more tricky because we need the success of the write *)
(*
Lemma memory_deallocated_progress α cids l bor (n: nat) :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
      (∃ it, it ∈ stk ∧ it.(itag) = bor ∧
        it.(perm) ≠ Disabled ∧ it.(perm) ≠ SharedReadOnly) ∧
      ∀ it, it ∈ stk → item_inactive_protector cids it) →
  is_Some (memory_deallocated α cids l bor n).
Proof.
  intros IN IT. apply for_each_is_Some; [done|].
  intros m stk Lt Eq. destruct (IT _ _ Lt Eq) as [In PR].
  destruct (dealloc1_progress stk bor cids) as [? Eq1];
    [|done|rewrite Eq1; by eexists].
  apply Forall_forall. move => it /PR.
  rewrite /item_inactive_protector /is_active_protector /is_active.
  case protector; naive_solver.
Qed.
*)
(*
Lemma memory_deallocate_progress (σ: state) l tg (sz:nat) (WF: state_wf σ) :
  (∀ m : Z, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m ∧ m < sz) →
  (sz > 0)%nat →
  trees_contain tg (strs σ) l.1 →
  is_Some (apply_within_trees (memory_deallocate σ.(scs) tg (l.2, sz)) l.1 σ.(strs)).
Proof.
  intros Hfoo Hbar Hcont.
  eexists. Locate trees_contain. unfold trees_contain in Hcont. unfold trees_at_block in Hcont.
  destruct (strs σ !! l.1) as [tr|] eqn:Heqtr; last done.
  rewrite /apply_within_trees /memory_deallocate Heqtr /=.
  unfold tree_apply_access.
  Print join_nodes.
  Print map_nodes.
  Search join_nodes.
   simpl.
  Print apply_within_trees.
  Print memory_deallocate.
  Print tree_apply_access.
  Print item_apply_access.
  Print memory_deallocate.
*)
Lemma dealloc_base_step' P (σ: state) l tg (sz:nat) α' (WF: state_wf σ) :
  (∀ m : Z, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m ∧ m < sz) →
  (sz > 0)%nat →
  trees_contain tg (strs σ) l.1 →
  apply_within_trees (memory_deallocate σ.(scs) tg (l.2, sz)) l.1 σ.(strs) = Some α' →
  let σ' := mkState (free_mem l sz σ.(shp)) (delete l.1 α') σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Free (Place l tg sz)) σ #[☠] σ' [].
Proof.
  intros Hdom Hpos Hcont Happly. destruct l as [blk off].
  econstructor; econstructor; auto.
Qed.
(*
Lemma dealloc_base_step P (σ: state) T l bor
  (WF: state_wf σ)
  (BLK: ∀ m : Z, l +ₗ m ∈ dom σ.(shp) ↔ 0 ≤ m ∧ m < tsize T)
  (BOR: ∀ (n: nat) stk, (n < tsize T)%nat →
    σ.(sst) !! (l +ₗ n) = Some stk →
    (∃ it, it ∈ stk ∧ it.(tg) = bor ∧
      it.(perm) ≠ Disabled ∧ it.(perm) ≠ SharedReadOnly) ∧
      ∀ it, it ∈ stk → item_inactive_protector σ.(scs) it) :
  ∃ σ',
  base_step P (Free (Place l bor T)) σ #[☠] σ' [].
Proof.
  destruct (memory_deallocated_progress σ.(sst) σ.(scs) l bor (tsize T))
    as [α' Eq']; [|done|].
  - intros. rewrite -(state_wf_dom _ WF). by apply BLK.
  - eexists. econstructor; econstructor; [|done].
    intros. by rewrite -(elem_of_dom (D:= gset loc) σ.(shp)).
Qed.
*)

(* Success of `read_mem` on the heap is unchanged. *)
Lemma read_mem_is_Some' l n h :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom h) ↔
  is_Some (read_mem l n h).
Proof.
  induction n as [|n IH] in l|-*.
  1: simpl; split; intros; first done; lia.
  specialize (IH (l +ₗ 1)).
  setoid_rewrite shift_loc_assoc in IH.
  destruct IH as (IHl & IHr).
  split.
  - intros H. destruct IHl as (x & Hx).
    { intros m Hm. assert (1 + m = S m) as -> by lia. eapply H; lia. }
    rewrite /= Hx /=. setoid_rewrite elem_of_dom in H.
    destruct (H 0%nat) as (y & Hy); first lia.
    rewrite shift_loc_0 in Hy. rewrite Hy //.
  - simpl. intros (rmr&(rr&Hrr&(hl&Hhl&[= <-])%option_bind_inv)%option_bind_inv).
    intros [|m] Hm.
    1: rewrite shift_loc_0; by eapply elem_of_dom_2.
    assert (Z.of_nat (S m) = (1 + m)%Z) as -> by lia.
    apply IHr; last lia.
    by exists rr.
Qed.

Lemma read_mem_is_Some l n h
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom h) :
  is_Some (read_mem l n h).
Proof. by apply read_mem_is_Some'. Qed.

Lemma read_mem_values l n h v :
  read_mem l n h = Some v →
  length v = n ∧
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = v !! i).
Proof.
  induction n as [|n IH] in l,v|-*.
  { simpl. intros [= <-]. split; first done. lia. }
  simpl. intros (rr&Hrr&(hl&Hhl&[= <-])%option_bind_inv)%option_bind_inv.
  destruct (IH _ _ Hrr) as (Hn&Hrst).
  split; first by rewrite -Hn.
  intros [|m] Hm.
  1: rewrite shift_loc_0 /= Hhl //.
  assert (Z.of_nat (S m) = (1 + m)%Z) as -> by lia.
  rewrite /= -Hrst /=; last lia.
  rewrite shift_loc_assoc //.
Qed.

Lemma read_mem_values' l n h v :
  length v = n →
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = v !! i) →
  read_mem l n h = Some v.
Proof.
  intros <- Hs.
  destruct (read_mem_is_Some l (length v) h) as (v' & Hv').
  { intros m Hm. apply elem_of_dom. rewrite Hs; last done.
    apply lookup_lt_is_Some_2. done.
  }
  enough (v' = v) as -> by done.
  apply read_mem_values in Hv' as [Hlen Hv'].
  eapply list_eq_same_length; [reflexivity | lia | ].
  intros i sc sc' Hi.
  rewrite -Hs; last lia. rewrite -Hv'; last lia. intros -> [= ->]. done.
Qed.

(*
Lemma replace_check'_is_Some cids acc stk :
  (∀ it, it ∈ stk → it.(perm) = Unique → item_inactive_protector cids it) →
  is_Some (replace_check' cids acc stk).
Proof.
  revert acc. induction stk as [|si stk IH]; intros acc PR; simpl; [by eexists|].
  case decide => EqU; last by (apply IH; set_solver).
  rewrite (Is_true_eq_true (check_protector cids si)); first by (apply IH; set_solver).
  have IN: si ∈ si :: stk by set_solver. apply PR in IN; [|done].
  move : IN. rewrite /check_protector /item_inactive_protector.
  case si.(protector) => [? /negb_prop_intro|//]. by case is_active.
Qed.

Lemma replace_check_is_Some cids stk :
  (∀ it, it ∈ stk → it.(perm) = Unique → item_inactive_protector cids it) →
  is_Some (replace_check cids stk).
Proof. move => /replace_check'_is_Some IS. by apply IS. Qed.

*)


(*
Definition access1_read_pre cids (stk: stack) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(tg) = bor ∧ it.(perm) ≠ Disabled ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = Disabled ∨ jt.(tg) ≠ bor) ∧
    match jt.(perm) with
    | Unique => item_inactive_protector cids jt
    | _ => True
    end.

Definition access1_write_pre cids (stk: stack) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(perm) ≠ Disabled ∧
  it.(perm) ≠ SharedReadOnly ∧ it.(tg) = bor ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = Disabled ∨ jt.(perm) = SharedReadOnly ∨ jt.(tg) ≠ bor) ∧
    match find_first_write_incompatible (take i stk) it.(perm) with
    | Some idx =>
        if decide (j < idx)%nat then
        (* Note: if a Disabled item is already in the stack, then its protector
          must have been inactive since its insertion, so this condition is
          unneccessary. *)
          item_inactive_protector cids jt
        else True
    | _ => True
    end.
 *)

Definition is_write (access: access_kind) : bool :=
  match access with AccessWrite => true | _ => false end.
(*
Definition access1_pre
  cids (stk: stack) (access: access_kind) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(perm) ≠ Disabled ∧
  (is_write access → it.(perm) ≠ SharedReadOnly) ∧ it.(tg) = bor ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = Disabled ∨
     (if is_write access then jt.(perm) = SharedReadOnly ∨ jt.(tg) ≠ bor
      else jt.(tg) ≠ bor)) ∧
    if is_write access then
      match find_first_write_incompatible (take i stk) it.(perm) with
      | Some idx =>
          if decide (j < idx)%nat then
          (* Note: if a Disabled item is already in the stack, then its protector
            must have been inactive since its insertion, so this condition is
            unneccessary. *)
            item_inactive_protector cids jt
          else True
      | _ => True
      end
    else
      match jt.(perm) with
      | Unique => item_inactive_protector cids jt
      | _ => True
      end.
 *)

(*
Lemma access1_is_Some cids stk kind bor
  (BOR: access1_pre cids stk kind bor) :
  is_Some (access1 stk kind bor cids).
Proof.
  destruct BOR as (i & it & Eqi & ND & IW & Eqit & Lti).
  rewrite /access1 /find_granting.
  rewrite (_: list_find (matched_grant kind bor) stk = Some (i, it)); last first.
  { apply list_find_Some_not_earlier. split; last split; [done|..].
    - split; [|done].
      destruct kind; [by apply grants_access_all|by apply grants_write_all, IW].
    - intros ?? Lt Eq GR. destruct (Lti _ _ Lt Eq) as [[Eq1|NEq1] NEq2].
      { move : GR. rewrite /matched_grant Eq1 /=. naive_solver. }
      destruct kind; [by apply NEq1, GR|]. destruct NEq1 as [OR|OR].
      + move : GR. rewrite /matched_grant OR /=. naive_solver.
      + by apply OR, GR. } simpl.
  have ?: (i ≤ length stk)%nat. { by eapply Nat.lt_le_incl, lookup_lt_Some. }
  destruct kind.
  - destruct (replace_check_is_Some cids (take i stk)) as [? Eq2];
      [|rewrite Eq2 /=; by eexists].
    intros jt [j Eqj]%elem_of_list_lookup_1 IU.
    have ?: (j < i)%nat.
    { rewrite -(length_take_le stk i); [|done]. by eapply lookup_lt_Some. }
    destruct (Lti j jt) as [Eq1 PR]; [done|..].
    + symmetry. by rewrite -Eqj lookup_take.
    + move : PR. by rewrite /= IU.
  - destruct (find_first_write_incompatible_is_Some (take i stk) it.(perm))
      as [idx Eqx]; [done|by apply IW|]. rewrite Eqx /=.
    destruct (remove_check_is_Some cids (take i stk) idx) as [stk' Eq'];
      [..|rewrite Eq'; by eexists].
    + move : Eqx. apply find_first_write_incompatible_length.
    + intros j jt Lt Eqj.
      have ?: (j < i)%nat.
      { rewrite -(length_take_le stk i); [|done]. by eapply lookup_lt_Some. }
      destruct (Lti j jt) as [Eq1 PR]; [done|..].
      * symmetry. by rewrite -Eqj lookup_take.
      * move : PR. by rewrite /= Eqx decide_True.
Qed.

Lemma access1_read_is_Some cids stk bor
  (BOR: access1_read_pre cids stk bor) :
  is_Some (access1 stk AccessRead bor cids).
Proof.
  destruct BOR as (i & it & Eqi & Eqit & ND &  Lti).
  apply access1_is_Some. exists i, it. do 4 (split; [done|]).
  intros j jt Lt Eq. by destruct (Lti _ _ Lt Eq).
Qed.
 *)

(*
Lemma memory_read_is_Some α cids l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom α) →
  (∀ (m: nat) stk, (m < n)%nat →
    α !! (l +ₗ m) = Some stk → access1_read_pre cids stk bor) →
  is_Some (memory_read α cids l bor n).
Proof.
  intros IN STK. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply IN.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq.
    specialize (STK _ _ Lt Eq).
    destruct (access1_read_is_Some _ _ _ STK) as [? Eq2]. rewrite Eq2. by eexists.
Qed.
 *)

Lemma apply_within_trees_unchanged fn blk trs trs' :
      (∀ tr, trs !! blk = Some tr → fn tr = Some tr) →
      apply_within_trees fn blk trs = Some trs' →
      trs' = trs.
Proof.
  intros Hsame (x&Hx&(y&Hy&[= <-])%bind_Some)%bind_Some.
  specialize (Hsame _ Hx). assert (y = x) as -> by congruence.
  rewrite insert_id //.
Qed.

Lemma copy_base_step' P (σ: state) l tg sz v trs' (WF: state_wf σ) :
  trees_contain tg σ.(strs) l.1 →
  read_mem l sz σ.(shp) = Some v →
  apply_within_trees (memory_access AccessRead σ.(scs) tg (l.2, sz)) l.1 σ.(strs) = Some trs' →
  let σ' := mkState σ.(shp) trs' σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Copy (Place l tg sz)) σ (Val v) σ' [].
Proof.
  intros TC RM Happly. destruct l. destruct sz.
  - simpl. econstructor. 1: by econstructor. assert (trs' = σ.(strs)) as ->.
    2: by eapply ZeroCopyIS.
    eapply apply_within_trees_unchanged in Happly; first done.
    intros tr Htr. simpl in Htr|-*. eapply (zero_sized_memory_access_unchanged false).
  - do 2 econstructor. all: eauto.
Qed.

Lemma write_base_step' P (σ: state) l bor sz v trs'
  (LEN: length v = sz)
  (BLK: ∀ n, (n < sz)%nat → l +ₗ n ∈ dom σ.(shp)) 
  (INTREE: trees_contain bor σ.(strs) l.1)
  (APPLY: apply_within_trees (memory_access AccessWrite (scs σ) bor (l.2, sz)) l.1 σ.(strs) = Some trs') :
  let σ' := mkState (write_mem l v σ.(shp)) trs' σ.(scs) σ.(snp) σ.(snc) in
  base_step P (Write (Place l bor sz) (Val v)) σ #[☠] σ' [].
Proof.
  intros σ'. destruct l. destruct sz.
  - destruct v; last done. econstructor; first econstructor. 1-2: done.
    assert (trs' = σ.(strs)) as ->. 2: by econstructor.
    eapply apply_within_trees_unchanged. 2: eassumption.
    intros tr Htr. eapply (zero_sized_memory_access_unchanged false).
  - econstructor 2; econstructor; eauto. by rewrite LEN.
Qed.

Lemma call_base_step P σ name e r fn :
  P !! name = Some fn →
  to_result e = Some r →
  base_step P (Call #[ScFnPtr name] e) σ (apply_func fn r) σ [].
Proof. by econstructor; econstructor. Qed.


Lemma init_call_base_step P σ :
  let c := σ.(snc) in
  let σ' := mkState σ.(shp) σ.(strs) ({[σ.(snc)]} ∪ σ.(scs)) σ.(snp) (S σ.(snc)) in
  base_step P InitCall σ (#[ScCallId (σ.(snc))]) σ' [].
Proof. by econstructor; econstructor. Qed.

Lemma end_call_base_step P (σ: state) trs' c :
  c ∈ σ.(scs) →
  trees_access_all_protected_initialized (scs σ) c (strs σ) = Some trs' →
  let σ' := mkState σ.(shp) trs' (σ.(scs) ∖ {[c]}) σ.(snp) σ.(snc) in
  base_step P (EndCall #[ScCallId c]) σ #[☠] σ' [].
Proof. intros ??. by econstructor; econstructor. Qed.

