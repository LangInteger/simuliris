(** Contextual refinement soundness result. *)

From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import heap_bij open_expr_rel heapbij_refl.

(** First we need to define a notion of "contexts"
(more general than the 'evaluation contexts' that the language comes with) *)
Inductive ctx_item :=
  | LetLCtx (x : binder) (e2 : expr)
  | LetRCtx (x : binder) (e1 : expr)
  | CallLCtx (v2 : val)
  | CallRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : expr)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfLCtx (e1 e2 : expr)
  | IfMCtx (e0 e2 : expr)
  | IfRCtx (e0 e1 : expr)
  | WhileLCtx (e1 : expr)
  | WhileRCtx (e0 : expr)
  | PairLCtx (v2 : expr)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | MatchLCtx (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | MatchMCtx (e0 : expr) (x1 : binder) (x2 : binder) (e2 : expr)
  | MatchRCtx (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder)
  | ForkCtx
  | AllocNLCtx (v2 : expr)
  | AllocNRCtx (e1 : expr)
  | FreeNLCtx (v2 : expr)
  | FreeNRCtx (e1 : expr)
  | LoadCtx (o : order)
  | StoreLCtx (o : order) (v2 : expr)
  | StoreRCtx (o : order) (e1 : expr)
  | CmpXchgLCtx (v1 : expr) (v2 : expr)
  | CmpXchgMCtx (e0 : expr) (v2 : expr)
  | CmpXchgRCtx (e0 : expr) (e1 : expr)
  | FaaLCtx (v2 : expr)
  | FaaRCtx (e1 : expr).

Local Definition fill_item (Ci : ctx_item) (e : expr) : expr :=
  match Ci with
  | LetLCtx x e2 => Let x e e2
  | LetRCtx x e1 => Let x e1 e
  | CallLCtx e2 => Call e e2
  | CallRCtx e1 => Call e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfLCtx e1 e2 => If e e1 e2
  | IfMCtx e0 e2 => If e0 e e2
  | IfRCtx e0 e1 => If e0 e1 e
  | WhileLCtx e1 => While e e1
  | WhileRCtx e0 => While e0 e
  | PairLCtx e2 => Pair e e2
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | MatchLCtx x1 e1 x2 e2 => Match e x1 e1 x2 e2
  | MatchMCtx e0 x1 x2 e2 => Match e0 x1 e x2 e2
  | MatchRCtx e0 x1 e1 x2 => Match e0 x1 e1 x2 e
  | ForkCtx => Fork e
  | AllocNLCtx e2 => AllocN e e2
  | AllocNRCtx e1 => AllocN e1 e
  | FreeNLCtx e2 => FreeN e e2
  | FreeNRCtx e1 => FreeN e1 e
  | LoadCtx o => Load o e
  | StoreLCtx o e2 => Store o e e2
  | StoreRCtx o e1 => Store o e1 e
  | CmpXchgLCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCtx e0 e2 => CmpXchg e0 e e2
  | CmpXchgRCtx e0 e1 => CmpXchg e0 e1 e
  | FaaLCtx e2 => FAA e e2
  | FaaRCtx e1 => FAA e1 e
  end.

Definition ctx := list ctx_item.
Definition fill_ctx (C : ctx) (e : expr) : expr :=
  foldl (flip fill_item) e C.

Lemma fill_ctx_app C1 C2 e :
  fill_ctx (C1 ++ C2) e = fill_ctx C2 (fill_ctx C1 e).
Proof. apply foldl_app. Qed.

(** Lift our "type system" to contexts. *)
Definition ctxi_wf (Ci : ctx_item) : Prop :=
  match Ci with
  | LetLCtx _ e => expr_wf e
  | LetRCtx _ e => expr_wf e
  | CallLCtx e => expr_wf e
  | CallRCtx e => expr_wf e
  | UnOpCtx _ => True
  | BinOpLCtx _ e => expr_wf e
  | BinOpRCtx _ e => expr_wf e
  | IfLCtx e1 e2 => expr_wf e1 ∧ expr_wf e2
  | IfMCtx e0 e2 => expr_wf e0 ∧ expr_wf e2
  | IfRCtx e0 e1 => expr_wf e0 ∧ expr_wf e1
  | WhileLCtx e1 => expr_wf e1
  | WhileRCtx e0 => expr_wf e0
  | PairLCtx e => expr_wf e
  | PairRCtx e => expr_wf e
  | FstCtx | SndCtx | InjLCtx | InjRCtx => True
  | MatchLCtx _ e1 _ e2 => expr_wf e1 ∧ expr_wf e2
  | MatchMCtx e0 _ _ e2 => expr_wf e0 ∧ expr_wf e2
  | MatchRCtx e0 _ e1 _ => expr_wf e0 ∧ expr_wf e1
  | ForkCtx => True
  | AllocNLCtx e => expr_wf e
  | AllocNRCtx e => expr_wf e
  | FreeNLCtx e => expr_wf e
  | FreeNRCtx e => expr_wf e
  | LoadCtx _ => True
  | StoreLCtx _ e => expr_wf e
  | StoreRCtx _ e => expr_wf e
  | CmpXchgLCtx _ _ => False  (* unsupported *)
  | CmpXchgMCtx _ _ => False  (* unsupported *)
  | CmpXchgRCtx _ _ => False  (* unsupported *)
  | FaaLCtx _ => False  (* unsupported *)
  | FaaRCtx _ => False (* unsupported *)
  end.
Definition ctx_wf := Forall ctxi_wf.

Lemma ctx_wf_app C1 C2 :
  ctx_wf (C1 ++ C2) ↔ ctx_wf C1 ∧ ctx_wf C2.
Proof. apply Forall_app. Qed.
Lemma ctx_wf_snoc C Ci :
  ctx_wf (C ++ [Ci]) ↔ ctx_wf C ∧ ctxi_wf Ci.
Proof. rewrite ctx_wf_app /ctx_wf Forall_singleton //. Qed.

Section ctx.
  Context `{sbijG Σ}.

  Theorem expr_rel_ctx C e_t e_s :
    ctx_wf C → expr_rel e_t e_s -∗ expr_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros Hwf. iInduction (C) as [ | Ci C] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->ctx_wf_snoc in Hwf. destruct Hwf as [Kwf Hiwf].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_ctx_app /=.
    destruct Ci; simpl.
    - iApply (expr_rel_let with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_let with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_call with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_call with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_unop with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_binop with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_binop with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_if with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_if with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_if with "[] [] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_while with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_while with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_pair with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_pair with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_fst with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_snd with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_injl with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_injr with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_match with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_match with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_match with "[] [] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_fork with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_allocN with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_allocN with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_freeN with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_freeN with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_load with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_store with "IH"); iApply expr_wf_sound; apply Hiwf.
    - iApply (expr_rel_store with "[] IH"); iApply expr_wf_sound; apply Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
    - by destruct Hiwf.
  Qed.

End ctx.
