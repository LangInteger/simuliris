From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import parallel_subst heap_bij_races log_rel.

(** * Reflexivity theorem for the heap bijection value relation *)

(** We will only be able to show reflexivity for "well-formed" terms.
This is basically our 'type system'. Indeed, "no types" really just means
"everything has the same type". *)
Fixpoint val_wf (v : val) : Prop :=
  match v with
  | LitV (LitLoc l) => False (* no literal locations allowed *)
  | LitV _ => True
  | PairV v1 v2 => val_wf v1 ∧ val_wf v2
  | InjLV v => val_wf v
  | InjRV v => val_wf v
  end.

Fixpoint expr_wf (e : expr) : Prop :=
  match e with
  | Val v => val_wf v
  | Var x => True
  | Let b e1 e2 => expr_wf e1 ∧ expr_wf e2
  | Call e1 e2 => expr_wf e1 ∧ expr_wf e2
  | UnOp op e => expr_wf e
  | BinOp op e1 e2 => expr_wf e1 ∧ expr_wf e2
  | If e1 e2 e3 => expr_wf e1 ∧ expr_wf e2 ∧ expr_wf e3
  | While e1 e2 => expr_wf e1 ∧ expr_wf e2
  | Pair e1 e2 => expr_wf e1 ∧ expr_wf e2
  | Fst e => expr_wf e
  | Snd e => expr_wf e
  | InjL e => expr_wf e
  | InjR e => expr_wf e
  | Match e x1 e1 x2 e2 => expr_wf e ∧ expr_wf e1 ∧ expr_wf e2
  | Fork e => expr_wf e
  | AllocN e1 e2 => expr_wf e1 ∧ expr_wf e2
  | FreeN e1 e2 => expr_wf e1 ∧ expr_wf e2
  | Load o e => o ≠ Na2Ord ∧ expr_wf e
  | Store o e1 e2 => o ≠ Na2Ord ∧ expr_wf e1 ∧ expr_wf e2
  | CmpXchg e1 e2 e3 => False   (* currently not supported *)
  | FAA e1 e2 => False          (* currently not supported *)
  end.

Section refl.
  Context `{nabijG Σ}.
  Notation log_rel := (log_rel val_rel (λ π, na_locs π ∅)) (only parsing).

  Lemma val_wf_sound v : val_wf v → ⊢ val_rel v v.
  Proof.
    intros Hv.
    iInduction v as [[] | | | ] "IH"; try by (simpl; try iApply "IH").
    simpl. destruct Hv as [H1 H2]. iSplit; [by iApply "IH" | by iApply "IH1"].
  Qed.

  Theorem expr_wf_sound e : expr_wf e → ⊢ log_rel e e.
  Proof.
    intros Hwf. iInduction e as [ ] "IH" forall (Hwf).
    - (* Val *) iApply log_rel_val. by iApply val_wf_sound.
    - (* Var *) by iApply log_rel_var.
    - (* Let *) destruct Hwf as [Hwf1 Hwf2]. by iApply (log_rel_let with "(IH [//]) (IH1 [//])").
    - (* Call *)
      destruct Hwf as [Hwf1 Hwf2]. iApply (log_rel_call with "(IH [//]) (IH1 [//])").
      by iIntros (???).
    - (* UnOp *) by iApply (log_rel_unop with "(IH [//])").
    - (* BinOp *) destruct Hwf as [Hwf1 Hwf2]. by iApply (log_rel_binop with "(IH [//]) (IH1 [//])").
    - (* If *) destruct Hwf as (Hwf1 & Hwf2 & Hwf3). by iApply (log_rel_if with "(IH [//]) (IH1 [//]) (IH2 [//])").
    - (* While *) destruct Hwf as (Hwf1 & Hwf2). by iApply (log_rel_while with "(IH [//]) (IH1 [//])").
    - (* Pairs *) destruct Hwf as (Hwf1 & Hwf2). by iApply (log_rel_pair with "(IH [//]) (IH1 [//])").
    - (* Fst *) by iApply (log_rel_fst with "(IH [//])").
    - (* Snd *) by iApply (log_rel_snd with "(IH [//])").
    - (* InjL *) by iApply (log_rel_injl with "(IH [//])").
    - (* InjR *) by iApply (log_rel_injr with "(IH [//])").
    - (* Match *) destruct Hwf as (Hwf1 & Hwf2 & Hwf3).
      by iApply (log_rel_match with "(IH [//]) (IH1 [//]) (IH2 [//])").
    - (* Fork *)
      iApply (log_rel_fork with "(IH [//])").
      iIntros (????) "Ht Hsim Hfork". by iApply (sim_bij_fork with "Ht Hsim").
    - (* AllocN *)
      destruct Hwf as (Hwf1 & Hwf2). iApply (log_rel_allocN with "(IH [//]) (IH1 [//])").
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
      destruct Hwf as (Hwf1 & Hwf2). iApply (log_rel_freeN with "(IH [//]) (IH1 [//])").
      iIntros (??????) "Ht Hv Hcont". by iApply (sim_bij_free with "Hv Ht").
    - (* Load *)
      destruct Hwf as (? & Hwf2).
      iApply (log_rel_load with "(IH [//])").
      iIntros (????) "Ht Hv Hcont". iApply (sim_bij_load with "Hv Ht"); [done..|].
      iIntros (??) "H ?". by iApply ("Hcont" with "[$]").
    - (* Store *)
      destruct Hwf as (? & Hwf1 & Hwf2). iApply (log_rel_store with "(IH [//]) (IH1 [//])").
      iIntros (??????) "Ht Hl Hv Hcont".
      destruct o => //.
      + by iApply (sim_bij_store_sc with "Hl Ht Hv").
      + by iApply (sim_bij_store_na with "Hl Ht Hv").
    - done.
    - done.
  Qed.
End refl.
