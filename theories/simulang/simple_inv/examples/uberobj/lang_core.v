From stdpp Require Import gmap.
From simuliris.simulation Require Import language .
From simuliris.simulang Require Import lang notation tactics class_instances.
From simuliris.simulation Require Import slsls lifting .
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

From simuliris.simulang Require Import hoare behavior.
From simuliris.simulang.simple_inv Require Import inv adequacy.

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

  (* compartmentally pre-allocated heap space for uids *)
  Variable heap_by_uid : uobj_id -> list loc.  
  Variable uid : uobj_id.
  (* fname -> (isCasm func * (pre-cond, post-cond)) *)
  Variable ext_funcs : string -> option (bool * ((state -> Prop) * (state -> Prop))). 

  Definition R_relation (m: state) (m': state) (modified: bool) : Prop :=
    closed (heap_by_uid uid) m' 
    /\ subseteq (dom m.(heap)) (dom m'.(heap))
    /\ (not modified -> forall l, In l (heap_by_uid uid) -> m.(heap) !! l = m'.(heap) !! l).

  Inductive respecting_the_specs (e : expr) (m : state) (Q : state -> Prop) : Prop :=
    | rts_base : 
      forall m', R_relation m m' false ->
      (* internal steps *)
      ((forall (e' : expr) (m'' : state), hl_prim_step e m' e' m'' -> respecting_the_specs e' m'' Q )
        (* halted case *)
        /\ (not (eq (hl_halted e) None) -> Q m')
        (* external call case *)
        /\ (forall fname argv is_casm (pre_spec : state -> Prop) m'' (post_spec : state -> Prop) vret e',
          (* m_extra satisfied the pre_sped of the external call *)
          hl_at_external e = Some (fname, argv)
          -> Some (is_casm, (pre_spec, post_spec) ) = ext_funcs fname
          -> pre_spec m'
          -> R_relation m' m'' is_casm
          -> post_spec m''
          -> hl_after_external (Some vret) e = Some e'
          -> respecting_the_specs e' m Q) 
      ) -> respecting_the_specs e m Q.

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

  Lemma preservation_of_respecting_the_specs Q_s Q_t :
    Q_t = build_target_specification Q_s ->
    forall s_exp t_exp (s_mem : state) (t_mem : state),
      (⊢ {{{ mem_equiv_rel s_mem t_mem }}} 
          t_exp ⪯[uid] s_exp
        {{{ mem_equiv_post_rel }}})
      -> respecting_the_specs s_exp s_mem Q_s
      -> respecting_the_specs t_exp t_mem Q_t.
  Proof.
  Admitted.
End specs.
