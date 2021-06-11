From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst gen_log_rel gen_refl pure_refl wf.
From simuliris.simplang.na_inv Require Export inv.

(** * Reflexivity theorem for the heap bijection value relation *)

Definition expr_head_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => val_wf v
  (* Na2Ord is an intermediate ordering that should only arise during
  execution and programs should not use it directly. *)
  | LoadHead o => o ≠ Na2Ord
  | StoreHead o => o ≠ Na2Ord
  | CmpXchgHead => False   (* currently not supported *)
  | FAAHead => False       (* currently not supported *)
  | _ => True
  end.

Notation expr_wf := (gen_expr_wf expr_head_wf).
Notation ectx_wf := (gen_ectx_wf expr_head_wf).
Notation ctx_wf := (gen_ctx_wf expr_head_wf).

Section refl.
  Context `{naGS Σ}.

  Theorem na_log_rel_structural : log_rel_structural heapbij.loc_rel (λ π, na_locs π ∅) expr_head_wf.
  Proof.
    intros e_t e_s ?? Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try by iApply pure_log_rel_structural; unfold loc_rel_func_law, loc_rel_inj_law, loc_rel_offset_law; eauto using heap_bij_loc_func, heap_bij_loc_inj, heap_bij_loc_shift.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Call *)
      iApply (log_rel_call with "IH IH1").
      by iIntros (???).
    - (* Fork *)
      iApply (log_rel_fork with "IH").
      iIntros (????) "Ht Hsim Hfork". by iApply (sim_bij_fork with "Ht Hsim").
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
    - (* FreeN *)
      iApply (log_rel_freeN with "IH IH1").
      iIntros (??????) "Ht Hv Hcont". by iApply (sim_bij_free with "Hv Ht").
    - (* Load *)
      iApply (log_rel_load with "IH").
      iIntros (????) "Ht Hv Hcont". iApply (sim_bij_load with "Hv Ht"); [done..|].
      iIntros (??) "H ?". by iApply ("Hcont" with "[$]").
    - (* Store *)
      iApply (log_rel_store with "IH IH1").
      iIntros (??????) "Ht Hl Hv Hcont".
      match goal with | o : order |- _ => destruct o => // end.
      + by iApply (sim_bij_store_sc with "Hl Ht Hv").
      + by iApply (sim_bij_store_na with "Hl Ht Hv").
  Qed.

  Corollary log_rel_refl e :
    expr_wf e →
    ⊢ log_rel e e.
  Proof.
    intros ?. iApply gen_log_rel_refl; first by apply na_log_rel_structural. done.
  Qed.

  Corollary log_rel_ctx C e_t e_s :
    ctx_wf C →
    log_rel e_t e_s -∗ log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros ?. iApply gen_log_rel_ctx; first by apply na_log_rel_structural. done.
  Qed.

  Corollary log_rel_ectx K e_t e_s :
    ectx_wf K →
    log_rel e_t e_s -∗ log_rel (fill K e_t) (fill K e_s).
  Proof.
    intros ?. iApply gen_log_rel_ectx; first by apply na_log_rel_structural. done.
  Qed.

  Lemma log_rel_closed_1 e_t e_s π :
    free_vars e_t ∪ free_vars e_s = ∅ →
    log_rel e_t e_s -∗ na_locs π ∅ -∗ e_t ⪯{π} e_s {{ λ v_t v_s, na_locs π ∅ ∗ val_rel v_t v_s }}.
  Proof.
    iIntros (?) "#Hrel Hc".
    iApply sim_mono; last iApply (gen_log_rel_closed_1 with "Hrel Hc"); [|done].
    iIntros (v_t v_s) "[$ $]".
  Qed.
End refl.
