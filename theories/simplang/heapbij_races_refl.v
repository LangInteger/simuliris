From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij_races log_rel ctx.

(** * Reflexivity theorem for the heap bijection value relation *)

(** We will only be able to show reflexivity for "well-formed" terms.
This is basically our 'type system'. Indeed, "no types" really just means
"everything has the same type". *)

Definition expr_wf (e : expr) : Prop :=
  match e with
  | Val v => val_wf v
  | Load o e => o ≠ Na2Ord
  | Store o e1 e2 => o ≠ Na2Ord
  | CmpXchg e1 e2 e3 => False   (* currently not supported *)
  | FAA e1 e2 => False          (* currently not supported *)
  | _ => True
  end.

Section refl.
  Context `{nabijG Σ}.

  Theorem expr_wf_sound : log_rel_exprs expr_wf val_rel (λ π, na_locs π ∅).
  Proof.
    intros e_t e_s Hwf Hs. iIntros "IH".
    destruct e_s, e_t => //=; simpl in Hs; simplify_eq.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Val *) iApply log_rel_val. by iApply val_wf_sound.
    - (* Var *) by iApply log_rel_var.
    - (* Let *) by iApply (log_rel_let with "IH IH1").
    - (* Call *)
      iApply (log_rel_call with "IH IH1").
      by iIntros (???).
    - (* UnOp *) by iApply (log_rel_unop with "IH").
    - (* BinOp *) by iApply (log_rel_binop with "IH IH1").
    - (* If *) by iApply (log_rel_if with "IH IH1 IH2").
    - (* While *) by iApply (log_rel_while with "IH IH1").
    - (* Pairs *) by iApply (log_rel_pair with "IH IH1").
    - (* Fst *) by iApply (log_rel_fst with "IH").
    - (* Snd *) by iApply (log_rel_snd with "IH").
    - (* InjL *) by iApply (log_rel_injl with "IH").
    - (* InjR *) by iApply (log_rel_injr with "IH").
    - (* Match *) destruct_and!; simplify_eq. by iApply (log_rel_match with "IH IH1 IH2").
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
      destruct o => //.
      + by iApply (sim_bij_store_sc with "Hl Ht Hv").
      + by iApply (sim_bij_store_na with "Hl Ht Hv").
  Qed.
End refl.
