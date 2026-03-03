From stdpp Require Import gmap.
From simuliris.simulation Require Import language .
From simuliris.simulang Require Import lang notation tactics class_instances.
From simuliris.simulation Require Import slsls lifting .
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

From simuliris.simulang Require Import hoare behavior.
From simuliris.simulang.simple_inv Require Import inv adequacy.

Lemma union_empty_inv `{Countable A} (X Y : gset A) :
  X ∪ Y = ∅ → X = ∅ ∧ Y = ∅.
Proof. intros H1; set_solver. Qed.

Definition hl_halted (e: expr) : option val := to_val e.

Definition hl_at_external (e: expr) : option (string * val) :=
  match (decompose_expr [] e) with
  | Some (K, Call e1 e2) => 
      match ((to_val e1), (to_val e2)) with
      (* and the parameter has been a value *)
      | (Some (LitV (LitFn f)), Some argv) => Some (f, argv)
      | _ => None
      end
  | _ => None
  end.

Definition hl_after_external (vret: option val) (e: expr) : option expr :=
  match vret with
  | Some v => 
      match (decompose_expr [] e) with
      | Some (K, Call e1 e2) => 
          match ((to_val e1), (to_val e2)) with
          | (Some (LitV (LitFn f)), Some argv) => Some (fill K (of_val v))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Notation uobj_id := nat.
(* how to support pointer to pointer *)
Definition closed (locs : list loc) (m : state) : Prop :=
  forall (l: loc) (l': loc) (ls: lock_state),
    In l locs ->
    m.(heap) !! l = Some (ls, LitV (LitLoc l')) ->
    In l' locs.

Definition sublist (l1 l2 : list loc) : Prop :=
  forall x, In x l1 -> In x l2.

Section specs.

  (* =====================================================================================
                                    source level definition 
     ===================================================================================== *)
  Variable functions : prog.
  Inductive hl_prim_step : expr -> state -> expr -> state -> Prop :=
    | hl_prim_step_base : 
        forall e σ σ' e' efs,
          prim_step functions e σ e' σ' efs ->
          hl_prim_step e σ e' σ'.

  Notation uobj_id := nat.
  (* compartmentally pre-allocated heap space for uids *)
  Variable heap_by_uid : uobj_id -> list loc.  
  (* fname -> (isCasm func * (pre-cond, post-cond)) *)
  Variable ext_funcs : string -> option (bool * ((state -> Prop) * (state -> Prop))). 

  Definition R_relation (uid: uobj_id) (m: state) (m': state) (modified: bool) : Prop :=
    closed (heap_by_uid uid) m' 
    /\ subseteq (dom m.(heap)) (dom m'.(heap))
    /\ (not modified -> forall l, In l (heap_by_uid uid) -> m.(heap) !! l = m'.(heap) !! l).

  Inductive respecting_the_specs (uid: uobj_id) (e : expr) (m : state) (Q : state -> Prop) : Prop :=
    | rts_base : 
      forall m', R_relation uid m m' false ->
      (* internal steps *)
      ((forall (e' : expr) (m'' : state), hl_prim_step e m' e' m'' -> respecting_the_specs uid e' m'' Q )
        (* halted case *)
        /\ (not (eq (hl_halted e) None) -> Q m')
        (* external call case *)
        /\ (forall fname argv is_casm (pre_spec : state -> Prop) m'' (post_spec : state -> Prop) vret e',
          (* m_extra satisfied the pre_sped of the external call *)
          hl_at_external e = Some (fname, argv)
          -> Some (is_casm, (pre_spec, post_spec) ) = ext_funcs fname
          -> pre_spec m'
          -> R_relation uid m' m'' is_casm
          -> post_spec m''
          -> hl_after_external (Some vret) e = Some e'
          -> respecting_the_specs uid e' m Q) 
      ) -> respecting_the_specs uid e m Q.

  (* =====================================================================================
                                    memory mapping 
     ===================================================================================== *)
  Variable mapping: gmap loc loc.
  Variable heap_s: gset loc.
  Variable heap_t: gset loc.

  Definition wf_mapping : Prop :=
    heap_s ⊆ dom mapping.

  Definition equivalence (s_mem : state) (t_mem : state): Prop :=
    wf_mapping ->
    (forall add_s, add_s ∈ heap_s ->
      match mapping !! add_s with
      | Some add_t => s_mem.(heap) !! add_s = t_mem.(heap) !! add_t
      | None => False
      end).

  (* =====================================================================================
                                   spec preservation 
     ===================================================================================== *)
  Definition build_target_specification (Q : state -> Prop) : state -> Prop :=
    fun t_mem =>
      exists s_mem,
        equivalence s_mem t_mem /\ Q s_mem.

  Context `{!simpleGS Σ}.
  Context {Λ : language}.

  Fixpoint do_mem_points_to_t (mem : list (loc * (lock_state * val))) : iProp Σ :=
    match mem with
    | [] => emp
    | (l, (ls, v)) :: xs => l ↦t v ∗ do_mem_points_to_t xs
    end.
  Fixpoint do_mem_points_to_s (mem : list (loc * (lock_state * val))) : iProp Σ :=
    match mem with
    | [] => emp
    | (l, (ls, v)) :: xs => l ↦s v ∗ do_mem_points_to_s xs
    end.

  Definition mem_points_to_t (mem : gmap loc (lock_state * val)) : iProp Σ :=
    do_mem_points_to_t (map_to_list mem).
  Definition mem_points_to_s (mem : gmap loc (lock_state * val)) : iProp Σ :=
    do_mem_points_to_s (map_to_list mem).

  Definition mem_equiv_rel s_mem t_mem :=
    (⌜equivalence s_mem t_mem⌝ 
      ∗ (mem_points_to_s s_mem.(heap)) 
      ∗ (mem_points_to_t t_mem.(heap)))%I.

  Definition mem_equiv_post_rel :=
    (λ e_t e_s, ∃ v_t v_s, ∃ s_mem t_mem, 
      ⌜e_t = of_val v_t⌝ ∗ ⌜e_s = of_val v_s⌝ ∗ val_rel v_t v_s
      ∗ ⌜equivalence s_mem t_mem⌝ 
      ∗ (mem_points_to_s s_mem.(heap)) 
      ∗ (mem_points_to_t t_mem.(heap)))%I.

  Lemma subst_map_with_no_free_vars :
    forall e map,
      free_vars e = ∅ ->
      subst_map map e = e.
  Proof.
    intros e map HNoFreeVars.
    induction e.
    - simpl. reflexivity.
    - unfold free_vars in HNoFreeVars. inversion HNoFreeVars.
    - simpl. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. admit.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
      rewrite H1. rewrite H2. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
      rewrite H1. rewrite H2. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H12 H3].
      apply union_empty_inv in H12. destruct H12 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2. apply IHe3 in H3.
      rewrite H1. rewrite H2. rewrite H3. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
      rewrite H1. rewrite H2. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
      rewrite H1. rewrite H2. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H12 H3].
      apply union_empty_inv in H12. destruct H12 as [H1 H2].
      apply IHe1 in H1. rewrite H1. admit.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
      rewrite H1. rewrite H2. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
      rewrite H1. rewrite H2. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply IHe in H0. rewrite H0. reflexivity.
    - simpl. inversion HNoFreeVars.
      apply union_empty_inv in H0. destruct H0 as [H1 H2].
      apply IHe1 in H1. apply IHe2 in H2.
  Admitted.

  Locate sim_expr.
  Locate sim.
  Locate unseal.
  Search sim_expr.
  Search sim_expr_stutter.
  Locate "{{".
  Print sim.
  Locate subst_map_rel.
  Locate free_vars.
  Locate val_rel.
  Locate "[{".
  Print state.
  Search "sim_expr".
  Print state.
  Locate log_rel.
  Locate sim_def.
  Locate prog.
  Print func.
  Lemma preservation_of_respecting_the_specs :
    forall Q_s Q_t,
      Q_t = build_target_specification Q_s ->
      forall s_exp t_exp (s_mem : state) (t_mem : state),
        (* there should be no dynamic heap of state.used_dyn_blocks (as we do not support dynamic allocations).
           but only paired global static heap of state.globals which is initialized at the begining of the program *)
        equivalence s_mem t_mem /\ s_mem.(used_dyn_blocks) = ∅ /\ t_mem.(used_dyn_blocks) = ∅
        (* well-formedness of the program, there should be no free variables, e.g., variables introduced by let *)
        /\ free_vars t_exp = ∅ /\ free_vars s_exp = ∅
        -> forall uid,
            (⊢ ∀ uid (map : gmap string (val * val)), 
              {{{ mem_equiv_rel s_mem t_mem }}} 
                t_exp ⪯[uid] s_exp
              {{{ mem_equiv_post_rel }}})
        -> respecting_the_specs uid s_exp s_mem Q_s
        -> respecting_the_specs uid t_exp t_mem Q_t.
  Proof.
    intros Q_s Q_t HQt s_exp t_exp s_mem t_mem 
          (HEquiv & HDynHeapEmpty_s & HDynHeapEmpty_t & HNoFreeVars_t & HNoFreeVars_s).
    intros uid HQuadruple HResp_s.

    assert (⊢ log_rel t_exp s_exp) as HLog_rel. {
      unfold log_rel.
      unfold sim.
      simpl.
      unfold sim_stutter.
      unfold sim_def.
 
      iModIntro.
      iIntros (t_id map1).
      unfold hoareSim in HQuadruple.
      rewrite HNoFreeVars_s.
      rewrite HNoFreeVars_t.
      iIntros "HVal_rel".
      iIntros "HTrue".

      assert (subst_map (fst <$> map1) t_exp = t_exp) as HSubst_t. {
        apply subst_map_with_no_free_vars. apply HNoFreeVars_t.
      }
      assert (subst_map (snd <$> map1) s_exp = s_exp) as HSubst_s. {
        apply subst_map_with_no_free_vars. apply HNoFreeVars_s.
      }
      rewrite HSubst_t. rewrite HSubst_s.

      unfold gen_log_rel.subst_map_rel.

      iSpecialize (HQuadruple t_id).

      (* sim_expr_decompose:
        ∀ {PROP : bi} {BiBUpd0 : BiBUpd PROP} {BiAffine0 : BiAffine PROP} {BiPureForall0 : BiPureForall
          PROP} {Λ : language} {s : simulirisGS PROPΛ} 
          (e_t e_s : language.exprΛ) 
          (Φ Ψ : language.expr Λ → language.expr Λ → PROP) (π : thread_id),
          e_t ⪯{π} e_s [{ Ψ }] -∗
          (∀ e_t0 e_s0 : language.expr Λ, Ψ e_t0 e_s0 -∗ e_t0 ⪯{π} e_s0 [{ Φ }]) -∗
          e_t ⪯{π} e_s [{ Φ }] *)
      
      iSpecialize (HQuadruple t_id).
     
      admit.
     }
    destruct HResp_s as [s_mem' HR_relation_s HResp_s].
    apply rts_base with (m' := t_mem).
    - admit.
    - repeat split.
      + unfold hoareSim in HQuadruple.
        unfold log_rel in HLog_rel.

  Admitted.
End specs.
