From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst gen_log_rel gen_refl pure_refl wf.
From simuliris.simplang.na_inv Require Export inv.

(** * Reflexivity theorem for read only expressions *)

Definition readonly_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => val_wf v
  (* Na2Ord is an intermediate ordering that should only arise during
  execution and programs should not use it directly. *)
  | LoadHead o => o ≠ Na2Ord
  | FreeNHead | ForkHead | CallHead | StoreHead _ | CmpXchgHead | FAAHead => False
  | _ => True
  end.

Section refl.
  Context `{naGS Σ}.

  Definition mapsto_list (ms : list (loc * loc * val * val * Qp)) : iProp Σ :=
    [∗ list] m∈ms, let '(l_t, l_s, v_t, v_s, q) := m in
     l_t↦t{#q}v_t ∗ l_s↦s{#q}v_s ∗ val_rel v_t v_s ∗ heapbij.loc_rel l_t l_s.

  Definition na_locs_in_mapsto_list (ms : list (loc * loc * val * val * Qp)) (col : gmap loc (loc * na_locs_state)) : Prop :=
    ∀ l_s l_t ns, col !! l_s = Some (l_t, ns) →
      ∃ i v_t v_s, ms !! i = Some (l_t, l_s, v_t, v_s, if ns is NaRead q then q else 1%Qp).

  Definition readonly_thread_own ms col (π : thread_id) : iProp Σ :=
    ⌜na_locs_in_mapsto_list ms col⌝ ∗ na_locs π col ∗ mapsto_list ms.

  Theorem readonly_log_rel_structural ms col : log_rel_structural heapbij.loc_rel (readonly_thread_own ms col) readonly_wf.
  Proof.
    intros e_t e_s ?? Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try by iApply pure_log_rel_structural; unfold loc_rel_func_law, loc_rel_inj_law, loc_rel_offset_law; eauto using heap_bij_loc_func, heap_bij_loc_inj, heap_bij_loc_shift.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* AllocN *)
      iApply (log_rel_allocN with "IH IH1").
      iIntros (??????) "Ht Hv Hcont".
      target_alloc l_t as "Hl_t" "Ha_t"; first done.
      source_alloc l_s as "Hl_s" "Ha_s"; first done.
      iApply (sim_bij_insertN with "Ha_t Ha_s Hl_t Hl_s [Hv]"); [lia | by rewrite replicate_length.. | | ].
      { iDestruct "Hv" as "#Hv".
        rewrite big_sepL2_replicate_l; last by rewrite replicate_length.
        generalize (Z.to_nat n) => n'.
        iInduction n' as [] "IHn"; cbn; first done. iFrame "Hv IHn".
      }
      by iApply "Hcont".
    - (* Load *)
      simpl in Hwf. iApply (log_rel_load with "IH").
      iIntros (????) "(%Hin & Hc & Hms) Hv Hcont".
      destruct (col !! l_s) as [[??]|] eqn:Heq.
      + move: (Hin _ _ _ Heq) => [i [v_t [v_s Hms]]].
        iDestruct (big_sepL_lookup_acc with "Hms") as "[Hl Hms]"; [done|].
        iDestruct "Hl" as "(Hl_t & Hl_s & #Hv' & Hl')".
        iDestruct (heap_bij_loc_inj with "Hv Hl'") as %?; subst.
        to_source. iApply (source_red_load with "Hl_s"); [destruct o0; naive_solver|]. iIntros "Hl_s".
        to_target. iApply (target_red_load with "Hl_t"); [destruct o0; naive_solver|]. iIntros "Hl_t".
        to_sim. iApply ("Hcont" with "[-] Hv'"). iFrame.
        by iDestruct ("Hms" with "[$Hl_s $Hl_t $Hv' $Hl']") as "$".
      + iApply (sim_bij_load with "Hv Hc"); [done..|].
        iIntros (??) "H Hc". iApply ("Hcont" with "[Hc Hms] H").
        by iFrame.
  Qed.
End refl.
