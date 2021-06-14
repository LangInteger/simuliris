From stdpp Require Import prelude gmap.
From simuliris.simulation Require Import language lifting.
From simuliris.simplang Require Import class_instances.
From simuliris.simplang Require Export lang notation.
From iris.prelude Require Import options.

(** * Pure reasoning for exploiting UB of dataraces

This file contains the pure reasoning that is necessary to exploit UB
of non-atomic accesses. The main definition is [na_locs_wf], which
keeps track of the alternaive executions which are used to justify the
optimizations. *)

(* TODO: move these two lemmas somewhere else? *)
Lemma reach_or_stuck_store P_s (l_s : loc) (v' : val) σ o Φ:
  o ≠ Na2Ord →
  reach_or_stuck P_s (Val #()) (state_upd_heap <[l_s:=(RSt 0, v')]> σ) Φ →
  reach_or_stuck P_s (Store o #l_s v') σ Φ.
Proof.
  move => ??.
  apply: reach_or_stuck_irred; [done|].
  move => [?[?[[<-]?]]]; simplify_eq.
  destruct o => //.
  - by apply: reach_or_stuck_head_step; [by econstructor|].
  - apply: reach_or_stuck_head_step; [by econstructor|].
    apply: reach_or_stuck_head_step; [econstructor; by rewrite lookup_insert|].
    destruct σ => /=. by rewrite insert_insert.
Qed.

Lemma reach_or_stuck_load P_s (l_s : loc) (v' : val) σ o Φ n:
  o ≠ Na2Ord →
  σ.(heap) !! l_s = Some (RSt n, v') →
  reach_or_stuck P_s (Val v') σ Φ →
  reach_or_stuck P_s (Load o #l_s) σ Φ.
Proof.
  move => ???.
  destruct o => //.
  - by apply: reach_or_stuck_head_step; [by econstructor|].
  - apply: reach_or_stuck_head_step; [by econstructor|].
    apply: reach_or_stuck_head_step; [econstructor; by rewrite lookup_insert|].
    destruct σ => /=. by rewrite insert_insert insert_id.
Qed.

Inductive na_locs_state :=
| NaExcl | NaRead (q : Qp).

Definition is_not_naexcl (ns : option (loc * na_locs_state)) : Prop :=
  (if ns is Some (_, NaExcl) then False else True).

Global Instance na_locs_state_eq_dec : EqDecision na_locs_state.
Proof. solve_decision. Qed.

Global Instance is_not_naexcl_dec ns : Decision (is_not_naexcl ns).
Proof. destruct ns as [[?[]]|] => /=; apply _. Qed.

Definition combine_na_locs (a b : option (option na_locs_state)) : option (option na_locs_state) :=
  match a, b with
  | None, _ => None
  | Some None, _ => b
  | Some (Some NaExcl), Some None => Some (Some NaExcl)
  | Some (Some NaExcl), Some _ => None
  | Some (Some (NaRead q1)), Some None => Some (Some (NaRead q1))
  | Some (Some (NaRead q1)), Some (Some NaExcl) => None
  | Some (Some (NaRead q1)), Some (Some (NaRead q2)) => Some (Some (NaRead (q1 + q2)))
  | _, None => None
  end.
Arguments combine_na_locs : simpl nomatch.

Fixpoint combine_na_locs_list (cols : list (gmap loc (loc * na_locs_state))) (l_s : loc) : option (option na_locs_state) :=
  match cols with
  | [] => Some None
  | col::cols =>
    combine_na_locs (Some (snd <$> (col !! l_s))) (combine_na_locs_list cols l_s)
  end.

Section combine_na_locs.
  Global Instance combine_na_locs_commute : Comm (=) combine_na_locs.
  Proof. rewrite /combine_na_locs. move => [?|] [?|] //=; repeat case_match => //. by rewrite (comm _ q). Qed.
  Global Instance combine_na_locs_assoc : Assoc (=) combine_na_locs.
  Proof.  rewrite /combine_na_locs. move => [?|] [?|] [?|] //=; repeat case_match => //=; simplify_eq => //. by rewrite assoc. Qed.

  Lemma combine_na_locs_list_None cols l:
    (∀ π col, cols !! π = Some col → col !! l = None) →
    combine_na_locs_list cols l = Some None.
  Proof.
    elim: cols => //= col cols IH Hπ.
    rewrite (Hπ 0 col) //. rewrite IH // => π col'.
    apply: (Hπ (S _)).
  Qed.

  Lemma combine_na_locs_list_not_excl cols l:
    (∀ π col, cols !! π = Some col → is_not_naexcl (col !! l)) →
    ∃ q, combine_na_locs_list cols l = Some (NaRead <$> q).
  Proof.
    elim: cols => //=. { by eexists None. }
    move => col cols IH Hπ.
    have [|q ->]:= IH.
    { move => ??. by apply: (Hπ (S _)). }
    destruct (col !! l) as [[?[|]]|] eqn: Heq => /=.
    - have := Hπ 0 col. rewrite Heq. naive_solver.
    - destruct q => /=; by eexists (Some _).
    - destruct q => /=; by [eexists (Some _) | eexists None].
  Qed.

  Lemma combine_na_locs_list_single cols col l π:
    cols !! π = Some col →
    (∀ π' col', π' ≠ π → cols !! π' = Some col' → col' !! l = None) →
    combine_na_locs_list cols l = Some (snd <$> (col !! l)).
  Proof.
    elim: cols π => // col' cols IH [|π]/=.
    - move => [->] Hπ. rewrite combine_na_locs_list_None.
      { rewrite /combine_na_locs. repeat case_match => //. }
      move => π col''. by apply: (Hπ (S _)).
    - move => Hcol Hπ. rewrite (Hπ 0) // (IH π) //.
      move => π' col'' ?. apply: (Hπ (S _)). lia.
  Qed.

  Lemma combine_na_locs_list_single_not_excl cols col l π:
    cols !! π = Some col →
    (∀ π' col', π' ≠ π → cols !! π' = Some col' → is_not_naexcl (col' !! l)) →
    ∃ q, combine_na_locs_list cols l = combine_na_locs (Some (snd <$> (col !! l))) (Some (NaRead <$> q)).
  Proof.
    elim: π cols.
    - move => [//|? cols] /= [->] Hπ.
      have [|q ->]:= (combine_na_locs_list_not_excl cols l).
      { move => π ??. by apply: (Hπ (S π)). }
      naive_solver.
    - move => π IH [//| col' cols] /= ? Hπ.
      have [//| | q -> ]:= (IH cols).
      { move => ???. apply: (Hπ (S _)). lia. }
      rewrite (assoc combine_na_locs) (comm _ (Some (snd <$> (col' !! l)))) -(assoc combine_na_locs).
      destruct (col' !! l) as [[?[|]]|] eqn: Heq => /=.
      + have := Hπ 0 col' => /=. rewrite Heq. naive_solver.
      + by destruct q; eexists (Some _).
      + by eexists _.
  Qed.

  Lemma combine_na_locs_list_partial_alter cols l π f col:
    cols !! π = Some col →
    combine_na_locs (Some (snd <$> f (col !! l))) (combine_na_locs_list cols l) =
    combine_na_locs (Some (snd <$> (col !! l))) (combine_na_locs_list (<[π:=(partial_alter f l col)]>cols) l).
  Proof.
    elim: π cols.
    - move => [//|??] /= [->]. rewrite lookup_partial_alter.
      by rewrite assoc (comm _ (Some (snd <$> f (col !! l)))) assoc.
    - move => n IH [//|col' cols] /= ?.
      rewrite assoc (comm _ (Some (snd <$> f (col !! l)))) -assoc IH //.
      by rewrite assoc (comm _ (Some (snd <$> (col' !! l)))) -assoc.
  Qed.

  Lemma combine_na_locs_list_insert cols l π p w col:
    col !! l = None →
    cols !! π = Some col →
    combine_na_locs_list (<[π:=(<[l := (p, w)]> col)]>cols) l = combine_na_locs (Some (Some w)) (combine_na_locs_list cols l).
  Proof.
    move => Hl Hc. have := (combine_na_locs_list_partial_alter _ l _ _ _ Hc).
    by rewrite Hl => /= <-.
  Qed.

  Lemma combine_na_locs_list_delete cols l π p w col:
    col !! l = Some (p, w) →
    cols !! π = Some col →
    combine_na_locs_list cols l = combine_na_locs (Some (Some w)) (combine_na_locs_list (<[π:=(delete l col)]>cols) l).
  Proof.
    move => Hl Hc. have := (combine_na_locs_list_partial_alter _ l _ _ _ Hc).
    by rewrite Hl => /= <-.
  Qed.

  Lemma combine_na_locs_list_partial_alter_ne cols l l' π f col:
    l ≠ l' →
    cols !! π = Some col →
    combine_na_locs_list (<[π:=(partial_alter f l' col)]>cols) l = combine_na_locs_list cols l.
  Proof.
    move => ?.
    elim: π cols.
    - move => [//|??] /= [->]. by rewrite lookup_partial_alter_ne.
    - move => ? IH [//|??] /= ?. by rewrite IH.
  Qed.

  Lemma combine_na_locs_list_snoc_empty cols l:
    combine_na_locs_list (cols ++ [∅]) l = combine_na_locs_list cols l.
  Proof. elim: cols => //= ?? ->. done. Qed.
End combine_na_locs.

Definition alloc_rel_pred (cols : list (gmap loc (loc * na_locs_state))) (l_s : loc) (q : option Qp) : Prop :=
  match combine_na_locs_list cols l_s with
  | None => False
  | Some (Some NaExcl) => q = None
  | Some (Some (NaRead q1)) => if q is Some q2 then q1 + q2 = 1 else False
  | Some None => q = Some 1
  end%Qp.

Definition heap_agree (σ1 σ2 : gmap loc (lock_state * val)) (ls : gset loc) : Prop :=
  ∀ l v v', l ∉ ls → σ1 !! l = Some v → σ2 !! l = Some v' → v = v'.

Definition na_alt_exec (P : prog) (σ : state) (T : list expr) (p : loc) (π : thread_id) (ns : na_locs_state) (excls : gset loc) : Prop :=
  ∃ (v' : val) σ' K ,
    pool_safe P (<[π := fill K (if ns is NaExcl then
                                        Store Na1Ord #p v'
                                          else Load Na1Ord #p) ]> T) σ' /\
    heap_agree σ.(heap) σ'.(heap) excls ∧
    heap_wf σ' ∧
    σ'.(used_blocks) ⊆ σ.(used_blocks).

Definition na_locs_wf (cols : list (gmap loc (loc * na_locs_state))) (P_s : prog) (σ_s : state) (T_s : list expr) : Prop :=
  ∀ (tid : nat) col, cols !! tid = Some col →
   ∃ (lcol : list (loc * na_locs_state)),
     (∀ (p_s : loc) p_t ns, col !! p_s = Some (p_t, ns) → (p_s, ns) ∈ lcol) ∧
     ∀ (p_s : loc) ns, (p_s, ns) ∈ lcol →
      na_alt_exec P_s σ_s T_s p_s tid ns (list_to_set (fst <$> filter (λ x, x.2 = NaExcl) lcol)).

Section na_alt_exec.

  Lemma na_alt_exec_intro ns (v' : val) σ_s' P_s σ_s T_s π K_s (l_s : loc) ls:
    heap_wf σ_s' →
    used_blocks σ_s' ⊆ used_blocks σ_s →
    (∀ l, l ∉ ls → σ_s.(heap) !! l = σ_s'.(heap) !! l) →
    pool_safe P_s (<[π:=fill K_s (if ns is NaExcl then (#l_s <- v') else (! #l_s))]> T_s) σ_s' →
    na_alt_exec P_s σ_s T_s l_s π ns ls.
  Proof.
    move => ?? Hh ?. eexists _, _, _.
    split_and!; [done | move => ????; rewrite Hh => *; by simplify_eq | done | done].
  Qed.

  Lemma na_alt_exec_mono P_s σ_s σ_s' T_s T_s' π (l_s : loc) ns ls ls':
    na_alt_exec P_s σ_s' T_s' l_s π ns ls' →
    (∀ σ', heap_wf σ' → used_blocks σ' ⊆ used_blocks σ_s' →
           heap_agree σ_s'.(heap) σ'.(heap) ls' → heap_agree σ_s.(heap) σ'.(heap) ls) →
    used_blocks σ_s' ⊆ used_blocks σ_s →
    (∀ e, <[π:=e]>T_s = <[π:=e]>T_s' ) →
    (ls' ⊆ ls) →
    na_alt_exec P_s σ_s T_s l_s π ns ls.
  Proof.
    move => [v[σ_s''[K_s' [Hsafe [Hl [??]]]]]] Hσ ? HT Hls.
    eexists _, _, _. split_and!.
    - by rewrite HT.
    - naive_solver.
    - done.
    - set_solver.
  Qed.

  Lemma na_alt_exec_load_stuck o P_s σ_s T_s π π' K_s e_s (l_s : loc) ls:
    na_alt_exec P_s σ_s T_s l_s π' NaExcl ls →
    T_s !! π = Some (fill K_s e_s) →
    π' < length T_s →
    o ≠ Na2Ord →
    π ≠ π' →
    (∀ P_s σ_s, reach_or_stuck P_s e_s σ_s (post_in_ectx (λ e' σ', e' = Load o #l_s ∧ σ' = σ_s))) →
    False.
  Proof.
    move => [v'[σ' [K [Hsafe Hσ]]]] HT ? ? ? Hsteps .
    apply: Hsafe.
    apply: pool_reach_stuck_reach_or_stuck.
    { by rewrite list_lookup_insert_ne. }
    { apply: fill_reach_or_stuck. by apply: Hsteps. }
    move => ?? [? [? [-> [-> ->]]]].
    eapply (pool_reach_stuck_irred).
    2: { rewrite list_lookup_insert_ne //. by apply: list_lookup_insert. }
    2: { done. }
    { apply _. }
    move => [?[?[??]]]; simplify_eq.
    apply: (pool_reach_stuck_no_forks π').
    { rewrite list_lookup_insert_ne //. by apply list_lookup_insert. }
    { apply: fill_no_forks. apply: no_forks_step; [|by apply: no_forks_refl].
        apply: head_prim_step. by constructor. }
    apply: pool_reach_stuck_reach_stuck.
    2: { rewrite list_lookup_insert_ne //. apply list_lookup_insert.
         rewrite insert_length. by apply: lookup_lt_Some. }
    apply: stuck_reach_stuck. apply: fill_stuck.
    apply: head_stuck_stuck; [|solve_sub_redexes_are_values].
    split; [done|] => ??? Hstep. inversion Hstep; simplify_map_eq/=.
  Qed.

  Lemma na_alt_exec_store_stuck o P_s σ_s T_s π π' K_s e_s (l_s : loc) ls ns:
    na_alt_exec P_s σ_s T_s l_s π' ns ls →
    T_s !! π = Some (fill K_s e_s) →
    π' < length T_s →
    o ≠ Na2Ord →
    π ≠ π' →
    (∀ P_s σ_s, reach_or_stuck P_s e_s σ_s (post_in_ectx (λ e' σ', ∃ v' : val, e' = Store o #l_s v' ∧ σ' = σ_s))) →
    False.
  Proof.
    move => [v'[σ' [K [Hsafe Hσ]]]] HT ? ? ? Hsteps .
    apply: Hsafe.
    apply: pool_reach_stuck_reach_or_stuck.
    { by rewrite list_lookup_insert_ne. }
    { apply: fill_reach_or_stuck. by apply: Hsteps. }
    move => ?? [? [? [-> [? [-> ->]]]]].
    destruct ns.
    - eapply (pool_reach_stuck_irred).
      2: { rewrite list_lookup_insert_ne //. by apply: list_lookup_insert. }
      2: { done. }
      { apply _. }
      move => [?[?[??]]]; simplify_eq.
      apply: (pool_reach_stuck_no_forks π').
      { rewrite list_lookup_insert_ne //. by apply list_lookup_insert. }
      { apply: fill_no_forks. apply: no_forks_step; [|by apply: no_forks_refl].
        apply: head_prim_step. by constructor. }
      apply: pool_reach_stuck_reach_stuck.
      2: { rewrite list_lookup_insert_ne //. apply list_lookup_insert.
           rewrite insert_length. by apply: lookup_lt_Some. }
      apply: stuck_reach_stuck. apply: fill_stuck.
      apply: head_stuck_stuck; [|solve_sub_redexes_are_values].
      split; [done|] => ??? Hstep. inversion Hstep; simplify_map_eq/=.
    - eapply (pool_reach_stuck_irred).
      2: { rewrite list_lookup_insert_ne //. by apply: list_lookup_insert. }
      2: { done. }
      { apply _. }
      move => [?[?[?[??]]]]; simplify_eq.
      apply: (pool_reach_stuck_no_forks π').
      { rewrite list_lookup_insert_ne //. by apply list_lookup_insert. }
      { apply: fill_no_forks. apply: no_forks_step; [|by apply: no_forks_refl].
        apply: head_prim_step. by constructor. }
      apply: pool_reach_stuck_reach_stuck.
      2: { rewrite list_lookup_insert_ne //. apply list_lookup_insert.
           rewrite insert_length. by apply: lookup_lt_Some. }
      apply: stuck_reach_stuck. apply: fill_stuck.
      apply: head_stuck_stuck; [|solve_sub_redexes_are_values].
      split; [done|] => ??? Hstep. inversion Hstep; simplify_map_eq/=.
  Qed.

  Lemma na_alt_exec_free_stuck P_s σ_s T_s π π' K_s e_s (n : Z) (l_s : loc) ls ns i:
    na_alt_exec P_s σ_s T_s (l_s +ₗ i) π' ns ls →
    T_s !! π = Some (fill K_s e_s) →
    π' < length T_s →
    π ≠ π' →
    (∀ P_s σ_s, reach_or_stuck P_s e_s σ_s (post_in_ectx (λ e' σ', e' = FreeN #n #l_s ∧ σ' = σ_s))) →
    False.
  Proof.
    move => [v'[σ' [K [Hsafe Hσ]]]] HT ? ? Hsteps .
    apply: Hsafe.
    apply: pool_reach_stuck_reach_or_stuck.
    { by rewrite list_lookup_insert_ne. }
    { apply: fill_reach_or_stuck. by apply: Hsteps. }
    move => ?? [? [? [-> [-> ->]]]].
    eapply (pool_reach_stuck_irred).
    2: { apply: list_lookup_insert. rewrite insert_length. by apply: lookup_lt_Some. }
    2: { done. }
    { apply _. }
    move => [?[?[?[?[? Hs]]]]]; simplify_eq.
    apply: pool_reach_stuck_no_forks.
    { apply: list_lookup_insert. rewrite insert_length. by apply: lookup_lt_Some. }
    { apply: no_forks_step; [|apply no_forks_refl]. apply: fill_no_fork.
      apply: head_prim_step. by econstructor. }
    rewrite list_insert_insert list_insert_commute //.
    apply: pool_reach_stuck_reach_stuck.
    2: { apply: list_lookup_insert. by rewrite insert_length. }
    apply: fill_reach_stuck.
    destruct ns; (apply: reach_stuck_irred; [done|]).
    - move => [?[?[? Hh]]]; simplify_eq/=.
      move: Hh => /lookup_free_mem_Some /= [/(mk_is_Some _ _) /Hs ?[//|?]]. lia.
    - move => [?[?[? [? Hh]]]]; simplify_eq/=.
      move: Hh => /lookup_free_mem_Some /= [/(mk_is_Some _ _) /Hs ?[//|?]]. lia.
  Qed.

  Lemma na_alt_exec_step P_s σ_s σ_s' T_s π π' ns ls e e' l_s K_s:
    na_alt_exec P_s σ_s T_s l_s π' ns ls →
    T_s !! π = Some (fill K_s e) →
    π ≠ π' →
    (∀ σ, heap_wf σ →
        used_blocks σ ⊆ used_blocks σ_s →
        (∀ l v1 v2, l∉ls → σ_s.(heap) !! l = Some v1 → σ.(heap) !! l = Some v2 → v1 = v2) →
        reach_or_stuck P_s e σ (λ e σ',
        e = e' ∧
        (∀ l v1 v2, l∉ls → σ_s'.(heap) !! l = Some v1 → σ'.(heap) !! l = Some v2 → v1 = v2) ∧
        heap_wf σ' ∧
        used_blocks σ' ⊆ used_blocks σ_s'
    )) →
    na_alt_exec P_s σ_s' (<[π := fill K_s e']>T_s) l_s π' ns ls.
  Proof.
    move => [v[σ_s''[K_s' [Hsafe [Hl [??]]]]]] HT Hπ Hsteps.
    have [|?[?[[? [Hh [??]]]?]]]:= (pool_safe_reach_or_stuck π _ _ _ _ _ K_s ltac:(done) _ ltac:(naive_solver)); simplify_eq.
    { by rewrite list_lookup_insert_ne. }
    eexists _, _, _. split_and!.
    - by rewrite list_insert_commute.
    - done.
    - done.
    - done.
  Qed.

  Lemma na_alt_exec_fork P σ π π' T e e' p ns ls efs:
    na_alt_exec P σ T p π' ns ls →
    T !! π = Some e →
    π ≠ π' →
    π' < length T →
    (∀ σ, prim_step P e σ e' σ efs) →
    na_alt_exec P σ (<[π:=e']> T ++ efs) p π' ns ls.
  Proof.
    move => [v'[σ' [K [? ?]]]] HT ? ? Hstep.
    move: (HT) => /(lookup_lt_Some _ _ _)?.
    rewrite -insert_app_l //.
    eexists _, _, _. split; [|done].
    rewrite list_insert_commute //.
    apply: pool_steps_safe; [|done].
    apply/pool_steps_single.
    rewrite !insert_app_l // ?insert_length //.
    apply: prim_step_pool_step; [ by apply Hstep |].
    by rewrite list_lookup_insert_ne.
  Qed.

  Lemma na_alt_exec_pure P σ π π' T e e' p ns ls:
    na_alt_exec P σ T p π' ns ls →
    T !! π = Some e →
    (∀ σ, prim_step P e σ e' σ []) →
    na_alt_exec P σ (<[π:=e']> T) p π' ns ls.
  Proof.
    move => [v'[σ' [K [? ?]]]] HT Hstep.
    eexists _, _, _. split; [|done].
    destruct (decide (π' = π)); subst.
    - by rewrite list_insert_insert.
    - rewrite list_insert_commute //.
      apply: pool_steps_safe; [|done].
      apply/pool_steps_single/no_fork_pool_step; [ by apply Hstep |].
      by rewrite list_lookup_insert_ne.
  Qed.
End na_alt_exec.

Section na_locs_wf.
  Lemma na_locs_wf_init P σ e:
    na_locs_wf [∅] P σ [e].
  Proof. move => ???. simplify_list_eq. eexists []. set_solver. Qed.

  Lemma na_locs_wf_combined_state_load cols P_s σ_s T_s π K_s e_s o (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s e_s) →
    o ≠ Na2Ord →
    length cols = length T_s →
    cols !! π = Some col →
    (∀ P_s σ_s, reach_or_stuck P_s e_s σ_s (post_in_ectx (λ e' σ', e' = Load o #l_s ∧ σ' = σ_s))) →
    ∃ q : option Qp, combine_na_locs_list cols l_s = combine_na_locs (Some (snd <$> (col !! l_s))) (Some (NaRead <$> q)).
  Proof.
    move => Hwf HT ? Hlen Hcols Hsteps.
    apply: combine_na_locs_list_single_not_excl; [done|].
    move => π' col' Hneq Hπ'. move: (Hπ') => /(lookup_lt_Some _ _ _)Hlt.
    rewrite Hlen in Hlt.
    destruct (col' !! l_s) as [[?[]]|] eqn:Hl_s; [exfalso|done..].
    have [lcol [Hlcol {}Hwf]]:= Hwf π' _ Hπ'.
    have {}Hl_s:= Hlcol _ _ _ Hl_s.
    apply: na_alt_exec_load_stuck; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_combined_state_store cols P_s σ_s T_s π K_s e_s o (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s e_s) →
    o ≠ Na2Ord →
    length cols = length T_s →
    cols !! π = Some col →
    (∀ P_s σ_s, reach_or_stuck P_s e_s σ_s (post_in_ectx (λ e' σ', ∃ v' : val, e' = Store o #l_s v' ∧ σ' = σ_s))) →
    combine_na_locs_list cols l_s = Some (snd <$> (col !! l_s)).
  Proof.
    move => Hwf HT ? Hlen Hcols Hsteps.
    apply: combine_na_locs_list_single; [done|].
    move => π' col' Hneq Hπ'. move: (Hπ') => /(lookup_lt_Some _ _ _)Hlt.
    rewrite Hlen in Hlt.
    destruct (col' !! l_s) as [[??]|] eqn:Hl_s; [exfalso|done].
    have [lcol [Hlcol {}Hwf]]:= Hwf π' _ Hπ'.
    have {}Hl_s:= Hlcol _ _ _ Hl_s.
    apply: na_alt_exec_store_stuck; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_combined_state_Free cols P_s σ_s T_s π K_s e_s (n : Z) (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s e_s) →
    length cols = length T_s →
    cols !! π = Some col →
    (∀ P_s σ_s, reach_or_stuck P_s e_s σ_s (post_in_ectx (λ e' σ', e' = FreeN #n #l_s ∧ σ' = σ_s))) →
    ∀ i, combine_na_locs_list cols (l_s +ₗ i) = Some (snd <$> (col !! (l_s +ₗ i))).
  Proof.
    move => Hwf HT Hlen Hcols Hsteps i.
    apply: combine_na_locs_list_single; [done|].
    move => π' col' Hneq Hπ'. move: (Hπ') => /(lookup_lt_Some _ _ _)Hlt.
    rewrite Hlen in Hlt.
    destruct (col' !! (l_s +ₗ i)) as [[??]|] eqn:Hl_s; [exfalso|done].
    have [lcol [Hlcol {}Hwf]]:= Hwf π' _ Hπ'.
    have {}Hl_s:= Hlcol _ _ _ Hl_s.
    apply: na_alt_exec_free_stuck; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_insert_store cols P_s σ_s T_s π K_s (l_s : loc) l_t (v' : val) col:
    na_locs_wf cols P_s σ_s T_s →
    heap_wf σ_s →
    cols !! π = Some col →
    pool_safe P_s (<[π:=fill K_s (#l_s <- v')]> T_s) σ_s →
    na_locs_wf (<[π:=<[l_s := (l_t, NaExcl)]>col]>cols) P_s σ_s T_s.
  Proof.
    move => Hwf ? Hcols Hnfs π' col' Hlookup.
    destruct (decide (π' = π)); simplify_eq.
    - rewrite list_lookup_insert in Hlookup; [|by apply: lookup_lt_Some]; simplify_eq.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcols.
      eexists ((l_s, NaExcl)::lcol).
      split.
      + move => ??? /lookup_insert_Some. set_solver.
      + move => p_s ws. rewrite filter_cons_True //; csimpl.
        move => /elem_of_cons[?|Hp]; simplify_eq.
        * by apply: na_alt_exec_intro.
        * apply: na_alt_exec_mono; [naive_solver| |done|done|set_solver].
          move => ? ?? Ha ????. apply: Ha. set_solver.
    - rewrite list_lookup_insert_ne // in Hlookup.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hlookup.
      eexists lcol. naive_solver.
  Qed.

  Lemma na_locs_wf_insert_load cols P_s σ_s T_s π K_s (l_s : loc) l_t col q:
    na_locs_wf cols P_s σ_s T_s →
    heap_wf σ_s →
    cols !! π = Some col →
    pool_safe P_s (<[π:=fill K_s (! #l_s)]> T_s) σ_s →
    na_locs_wf (<[π:=<[l_s := (l_t, NaRead q)]>col]>cols) P_s σ_s T_s.
  Proof.
    move => Hwf ? Hcols Hnfs π' col' Hlookup.
    destruct (decide (π' = π)); simplify_eq.
    - rewrite list_lookup_insert in Hlookup; [|by apply: lookup_lt_Some]; simplify_eq.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcols.
      eexists ((l_s, NaRead q)::lcol).
      split.
      + move => ??? /lookup_insert_Some. set_solver.
      + move => p_s ws. rewrite filter_cons_False //=.
        move => /elem_of_cons[?|Hp]; simplify_eq.
        * by apply: (na_alt_exec_intro _ #()).
        * naive_solver.
    - rewrite list_lookup_insert_ne // in Hlookup.
      have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hlookup.
      eexists lcol. naive_solver.
  Qed.

  Lemma na_locs_wf_delete cols P_s σ_s T_s π (l_s : loc) col:
    na_locs_wf cols P_s σ_s T_s →
    cols !! π = Some col →
    na_locs_wf (<[π:=delete l_s col]>cols) P_s σ_s T_s.
  Proof.
    move => Hwf Hcol π' col' Hcol'.
    move: (Hcol) => /(lookup_lt_Some _ _ _)?.
    destruct (decide (π = π')); subst.
    2: { apply: Hwf. by rewrite list_lookup_insert_ne in Hcol'. }
    rewrite list_lookup_insert // in Hcol'; simplify_eq.
    have [lcol [? {}Hwf]]:= Hwf _ _ Hcol.
    eexists lcol. split; [|done].
    move => ??? /lookup_delete_Some[??]. naive_solver.
  Qed.

  Lemma na_locs_wf_pure cols P_s σ_s T π e_s e_s':
    na_locs_wf cols P_s σ_s T →
    T !! π = Some e_s →
    (∀ σ_s, prim_step P_s e_s σ_s e_s' σ_s []) →
    na_locs_wf cols P_s σ_s (<[π:=e_s']> T).
  Proof.
    move => Hwf HT Hstep tid col Hcol.
    have [lcol [Hlcol {}Hwf]]:= Hwf tid col Hcol.
    eexists lcol. split; [done|]. move => p_s ws Hp.
    apply: na_alt_exec_pure; [naive_solver| done..].
  Qed.

  Lemma na_locs_wf_store σ_s (l_s : loc) (v v' : val) T_s π K_s P_s cols col o:
    na_locs_wf cols P_s σ_s T_s →
    cols !! π = Some col →
    o = Na1Ord ∨ (o = ScOrd ∧ col = ∅) →
    heap σ_s !! l_s = Some (RSt 0, v) →
    T_s !! π = Some (fill K_s (Store o #l_s v')) →
    pool_safe P_s T_s σ_s →
    heap_wf σ_s →
    length cols = length T_s →
    na_locs_wf cols P_s (state_upd_heap <[l_s:=(RSt 0, v')]> σ_s) (<[π:=fill K_s #()]> T_s).
  Proof.
    move => Hwf Hcols Hexcl ? ? ? ? Hlen π' col' Hcol'.
    have ? : o ≠ Na2Ord by naive_solver.
    move: (Hcol') => /(lookup_lt_Some _ _ _)Hlt. rewrite Hlen in Hlt.
    destruct (decide (π = π')); simplify_eq.
    - have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcols.
      destruct Hexcl as [?|]; simplify_map_eq.
      2: { eexists []. split; [set_solver| set_solver]. }
      eexists ((l_s, NaExcl)::lcol).
      split; [set_solver|].
      move => p_s ws. rewrite filter_cons_True //; csimpl.
      move => /elem_of_cons[?|Hp]; simplify_eq.
      + apply: na_alt_exec_intro; [done|done| |].
        * move => l ?. have ? : l ≠ l_s by set_solver.
          by rewrite lookup_insert_ne.
        * by rewrite list_insert_insert list_insert_id.
      + apply: na_alt_exec_mono; [naive_solver| |done| |set_solver].
        * move => σ' ?? Ha l ???. have ? : l ≠ l_s by set_solver.
          rewrite lookup_insert_ne //. apply: Ha. set_solver.
        * move => ?. by rewrite list_insert_insert.
    - have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
      eexists lcol. split; [done|] => p_s ws Hp.
      destruct (decide (l_s = p_s)); subst.
      + exfalso. apply: (na_alt_exec_store_stuck o); [naive_solver | done | done | naive_solver |done | ].
        move => ??. apply: reach_or_stuck_refl. apply: post_in_ectx_intro. naive_solver.
      + apply: na_alt_exec_step; [naive_solver |done |done |].
        move => ????.
        apply: reach_or_stuck_irred; [done|]. move => [?[?[[<-]?]]]; simplify_eq.
        apply: reach_or_stuck_store; [done|].
        apply: reach_or_stuck_refl. split_and!; [done| | by apply: heap_wf_insert; eauto |done].
        move => l' ?? /= ???. destruct (decide (l' = l_s)); simplify_map_eq => //. naive_solver.
  Qed.

  Lemma na_locs_wf_load σ_s (l_s : loc) n (v : val) T_s π K_s P_s cols o:
    na_locs_wf cols P_s σ_s T_s →
    heap σ_s !! l_s = Some (RSt n, v) →
    T_s !! π = Some (fill K_s (Load o #l_s)) →
    o ≠ Na2Ord →
    pool_safe P_s T_s σ_s →
    length cols = length T_s →
    na_locs_wf cols P_s σ_s (<[π:=fill K_s v]> T_s).
  Proof.
    move => Hwf ? ? ? ? Hlen π' col' Hcol'.
    move: (Hcol') => /(lookup_lt_Some _ _ _)Hlt. rewrite Hlen in Hlt.
    destruct (decide (π = π')); subst.
    { unfold na_alt_exec. setoid_rewrite list_insert_insert. by apply: Hwf. }
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    eexists lcol. split; [done|] => p_s ws Hp.
    destruct (decide ((l_s, NaExcl) ∈ lcol)) as [Hin|Hin].
    - exfalso. apply: (na_alt_exec_load_stuck o); [naive_solver | done |done|done | done |].
      move => ??. apply: reach_or_stuck_refl. apply: post_in_ectx_intro. naive_solver.
    - apply: na_alt_exec_step; [naive_solver |done |done |].
      move => ??? Heq.
      apply: reach_or_stuck_irred; [done|]. move => [?[?[?[??]]]]; simplify_eq.
      apply: reach_or_stuck_load; [done..|].
      apply: reach_or_stuck_refl. split_and!; [|done|done|done].
      efeed pose proof Heq; [|done|done|naive_solver].
      rewrite not_elem_of_list_to_set elem_of_list_fmap.
      move => [[??][?]]. rewrite elem_of_list_filter. naive_solver.
  Qed.

  Lemma na_locs_wf_alloc cols P_s σ_s n T_s π (v : val) K_s:
    na_locs_wf cols P_s σ_s T_s →
    (0 < n)%Z →
    T_s !! π = Some (fill K_s (AllocN #n v)) →
    na_locs_wf cols P_s
    {|
      heap :=
        heap_array (Loc (fresh_block (heap σ_s) (used_blocks σ_s)) 0) (replicate (Z.to_nat n) v)
        ∪ heap σ_s;
      used_blocks := {[fresh_block (heap σ_s) (used_blocks σ_s)]} ∪ used_blocks σ_s
    |} (<[π:=fill K_s #(Loc (fresh_block (heap σ_s) (used_blocks σ_s)) 0)]> T_s).
  Proof.
    move => Hwf ? HT π' col' Hcol'.
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    eexists lcol. split; [done|] => p_s ws Hp.
    destruct (decide (π = π')); simplify_eq.
    - apply: na_alt_exec_mono; [naive_solver | | set_solver | |done].
      2: { move => ?. by rewrite list_insert_insert. }
      move => ? Hhwf Hsub Ha ???? /lookup_union_Some [|/heap_array_lookup [?[?[?[?[??]]]]]|]; simplify_eq.
      { apply heap_array_map_disjoint => ???. apply is_fresh_block. }
      + by move => /Hhwf /Hsub /is_fresh_block_blocks.
      + by apply: Ha.
    - apply: na_alt_exec_step; [naive_solver |done |done |].
      move => σ' Hhwf Hsub Heq.
      apply: reach_or_stuck_head_step.
      2: apply: reach_or_stuck_refl; split; [done|].
      { econstructor; [done| |].
        - move => Hx. apply: is_fresh_block_blocks. by apply: Hsub.
        - move => i.
          destruct (heap σ' !! Loc (fresh_block (heap σ_s) (used_blocks σ_s)) i) eqn: Hn => //.
          by move: Hn => /Hhwf/Hsub/is_fresh_block_blocks ?.
      }
      split_and!.
      + move => ???? /lookup_union_Some_raw[/heap_array_lookup[?[?[?[?[??]]]]]|[??]]
                    /lookup_union_Some_raw[/heap_array_lookup[?[?[?[?[??]]]]]|[??]]; simplify_eq => //.
        * exfalso. apply: eq_None_ne_Some; [done|]. apply heap_array_lookup. naive_solver.
        * exfalso. apply: eq_None_ne_Some; [done|]. apply heap_array_lookup. naive_solver.
        * by apply: Heq.
      + by apply: heap_wf_init_mem.
      + set_solver.
  Qed.

  Lemma na_locs_wf_free cols P_s σ_s T_s π (n : Z) (l : loc) K_s:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s (FreeN #n #l)) →
    na_locs_wf cols P_s (state_upd_heap (free_mem l (Z.to_nat n)) σ_s) (<[π:=fill K_s #()]> T_s).
  Proof.
    move => Hwf HT π' col' Hcol'.
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    eexists lcol. split; [done|] => p_s ws Hp.
    destruct (decide (π = π')); simplify_eq.
    - apply: na_alt_exec_mono; [naive_solver | | set_solver | |done].
      2: { move => ?. by rewrite list_insert_insert. }
      move => /= ??? Hl???? /lookup_free_mem_Some[??]. by apply: Hl.
    - apply: na_alt_exec_step; [naive_solver |done |done |].
      move => σ' Hhwf Hsub Heq.
      eapply reach_or_stuck_irred; [apply _|done|].
      move => [?[?[?[?[??]]]]]; simplify_eq.
      apply: reach_or_stuck_head_step; [by econstructor|].
      apply: reach_or_stuck_refl; split_and!; [done| | by apply: heap_wf_free_mem |done].
      move => ???? /lookup_free_mem_Some[??] /lookup_free_mem_Some[??]. by apply: Heq.
  Qed.

  Lemma na_locs_wf_fork cols P_s σ_s T_s K_s e_s π:
    na_locs_wf cols P_s σ_s T_s →
    T_s !! π = Some (fill K_s (Fork e_s)) →
    cols !! π = Some ∅ →
    length T_s = length cols →
    na_locs_wf (cols ++ [∅]) P_s σ_s (<[π:=fill K_s #()]> T_s ++ [e_s]).
  Proof.
    move => Hwf HT ? Hlen π' col' /lookup_app_Some[Hcol'|[?/(elem_of_list_split_length _ _ _) [[|?[|??]][?[??]]]]]; simplify_eq.
    2: { eexists []. split; [by simplify_list_eq|set_solver]. }
    have [lcol [Hlcol {}Hwf]]:= Hwf _ _ Hcol'.
    destruct (decide (π = π')); simplify_map_eq.
    { eexists []. split; [by simplify_list_eq|set_solver]. }
    eexists lcol. split; [done|] => p_s ws Hp; simplify_eq/=.
    apply: na_alt_exec_fork; [naive_solver|done.. | |].
    { rewrite Hlen. by apply: lookup_lt_Some. }
    move => ?. apply: fill_prim_step. apply: head_prim_step. econstructor.
  Qed.
End na_locs_wf.


Definition na_locs_in_L (cols : list (gmap loc (loc * na_locs_state))) (L : gset (block * block)) : Prop :=
  ∀ π col l x, cols !! π = Some col → col !! l = Some x → ∃ b1, (b1, loc_block l) ∈ L.

Section na_locs_in_L.
  Lemma na_locs_in_L_init:
    na_locs_in_L [∅] ∅.
  Proof. move => ??????. simplify_list_eq. Qed.

  Lemma na_locs_in_L_extend cols L b_t b_s:
    na_locs_in_L cols L →
    na_locs_in_L cols ({[(b_t, b_s)]} ∪ L).
  Proof. move => Hwf π col l x Hcol Hx. have [??]:= Hwf π col l x Hcol Hx. set_solver. Qed.
End na_locs_in_L.
