From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst log_rel ctx.
From simuliris.simplang.simple_inv Require Import simple_inv.

(** * Reflexivity theorem for the heap bijection value relation *)

(** We will only be able to show reflexivity for "well-formed" terms.
This is basically our 'type system'. Indeed, "no types" really just means
"everything has the same type". *)

Definition expr_wf (e : expr) : Prop :=
  match e with
  | Val v => val_wf v
  | CmpXchg e1 e2 e3 => False   (* currently not supported *)
  | FAA e1 e2 => False          (* currently not supported *)
  | _ => True
  end.

Section refl.
  Context `{heapbijG Σ}.
  Notation log_rel := (log_rel val_rel (const True%I)) (only parsing).

  Theorem expr_wf_sound : log_rel_exprs expr_wf val_rel (const True%I).
  Proof.
    intros e_t e_s Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //; simpl in Hs; simplify_eq.
    all: try by iApply pure_expr_wf_sound.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Call *)
      iApply (log_rel_call with "IH IH1").
      iIntros (???). by rewrite left_id.
    - (* Fork *)
      iApply (log_rel_fork with "IH").
      iIntros (?????) "Hsim Hfork". iApply (sim_fork with "(Hsim [//])").
      iIntros (?). iApply (sim_wand with "[Hfork]"). { by iApply "Hfork". }
      iIntros (??) "[_ $]".
    - (* AllocN *)
      iApply (log_rel_allocN with "IH IH1").
      iIntros (???????) "Hv Hcont".
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
      iIntros (???????) "Hv Hcont". sim_free. by iApply "Hcont".
    - (* Load *)
      iApply (log_rel_load with "IH").
      iIntros (?????) "Hv Hcont". iApply (sim_bij_load with "Hv"). iIntros (??). by iApply "Hcont".
    - (* Store *)
      iApply (log_rel_store with "IH IH1").
      iIntros (???????) "Hl Hv Hcont". iApply (sim_bij_store with "Hl Hv"). by iApply "Hcont".
  Qed.

End refl.
