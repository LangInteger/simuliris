(** Contextual refinement soundness result. *)

From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import log_rel.

(** First we need to define a notion of "contexts"
(more general than the 'evaluation contexts' that the language comes with) *)
Inductive ctx_item :=
  | LetLCCtx (x : binder) (e2 : expr)
  | LetRCCtx (x : binder) (e1 : expr)
  | CallLCCtx (v2 : val)
  | CallRCCtx (e1 : expr)
  | UnOpCCtx (op : un_op)
  | BinOpLCCtx (op : bin_op) (v2 : expr)
  | BinOpRCCtx (op : bin_op) (e1 : expr)
  | IfLCCtx (e1 e2 : expr)
  | IfMCCtx (e0 e2 : expr)
  | IfRCCtx (e0 e1 : expr)
  | WhileLCCtx (e1 : expr)
  | WhileRCCtx (e0 : expr)
  | PairLCCtx (v2 : expr)
  | PairRCCtx (e1 : expr)
  | FstCCtx
  | SndCCtx
  | InjLCCtx
  | InjRCCtx
  | MatchLCCtx (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | MatchMCCtx (e0 : expr) (x1 : binder) (x2 : binder) (e2 : expr)
  | MatchRCCtx (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder)
  | ForkCCtx
  | AllocNLCCtx (v2 : expr)
  | AllocNRCCtx (e1 : expr)
  | FreeNLCCtx (v2 : expr)
  | FreeNRCCtx (e1 : expr)
  | LoadCCtx (o : order)
  | StoreLCCtx (o : order) (v2 : expr)
  | StoreRCCtx (o : order) (e1 : expr)
  | CmpXchgLCCtx (v1 : expr) (v2 : expr)
  | CmpXchgMCCtx (e0 : expr) (v2 : expr)
  | CmpXchgRCCtx (e0 : expr) (e1 : expr)
  | FaaLCCtx (v2 : expr)
  | FaaRCCtx (e1 : expr).

Local Definition fill_ctx_item (Ci : ctx_item) (e : expr) : expr :=
  match Ci with
  | LetLCCtx x e2 => Let x e e2
  | LetRCCtx x e1 => Let x e1 e
  | CallLCCtx e2 => Call e e2
  | CallRCCtx e1 => Call e1 e
  | UnOpCCtx op => UnOp op e
  | BinOpLCCtx op e2 => BinOp op e e2
  | BinOpRCCtx op e1 => BinOp op e1 e
  | IfLCCtx e1 e2 => If e e1 e2
  | IfMCCtx e0 e2 => If e0 e e2
  | IfRCCtx e0 e1 => If e0 e1 e
  | WhileLCCtx e1 => While e e1
  | WhileRCCtx e0 => While e0 e
  | PairLCCtx e2 => Pair e e2
  | PairRCCtx e1 => Pair e1 e
  | FstCCtx => Fst e
  | SndCCtx => Snd e
  | InjLCCtx => InjL e
  | InjRCCtx => InjR e
  | MatchLCCtx x1 e1 x2 e2 => Match e x1 e1 x2 e2
  | MatchMCCtx e0 x1 x2 e2 => Match e0 x1 e x2 e2
  | MatchRCCtx e0 x1 e1 x2 => Match e0 x1 e1 x2 e
  | ForkCCtx => Fork e
  | AllocNLCCtx e2 => AllocN e e2
  | AllocNRCCtx e1 => AllocN e1 e
  | FreeNLCCtx e2 => FreeN e e2
  | FreeNRCCtx e1 => FreeN e1 e
  | LoadCCtx o => Load o e
  | StoreLCCtx o e2 => Store o e e2
  | StoreRCCtx o e1 => Store o e1 e
  | CmpXchgLCCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCCtx e0 e2 => CmpXchg e0 e e2
  | CmpXchgRCCtx e0 e1 => CmpXchg e0 e1 e
  | FaaLCCtx e2 => FAA e e2
  | FaaRCCtx e1 => FAA e1 e
  end.

Definition ctx := list ctx_item.
Definition fill_ctx (C : ctx) (e : expr) : expr :=
  foldl (flip fill_ctx_item) e C.

Lemma fill_ctx_app C1 C2 e :
  fill_ctx (C1 ++ C2) e = fill_ctx C2 (fill_ctx C1 e).
Proof. apply foldl_app. Qed.

Definition sub_exprs (e : expr) : list expr :=
  match e with
  | Val v => []
  | Var x => []
  | Let x e1 e2 => [e1; e2]
  | Call e1 e2 => [e1; e2]
  | UnOp op e => [e]
  | BinOp op e1 e2 => [e1; e2]
  | If e0 e1 e2 => [e0;e1;e2]
  | While e0 e1 => [e0; e1]
  | Pair e1 e2 => [e1; e2]
  | Fst e => [e]
  | Snd e => [e]
  | InjL e => [e]
  | InjR e => [e]
  | Match e0 x1 e1 x2 e2 => [e0;e1;e2]
  | Fork e => [e]
  | AllocN e1 e2 => [e1; e2]
  | FreeN e1 e2 => [e1; e2]
  | Load o e => [e]
  | Store o e1 e2 => [e1; e2]
  | CmpXchg e0 e1 e2 => [e0;e1;e2]
  | FAA e1 e2 => [e1; e2]
  end.

Definition expr_same_shape (e1 e2 : expr) : Prop :=
  match e1, e2 with
  | Val v1, Val v2 => v1 = v2
  | Var x1, Var x2 => x1 = x2
  | Let x1 _ _, Let x2 _ _ => x1 = x2
  | Call _ _, Call _ _ =>  True
  | UnOp op1 _, UnOp op2 _ => op1 = op2
  | BinOp op1 _ _, BinOp op2 _ _ => op1 = op2
  | If _ _ _, If _ _ _ => True
  | While _ _, While _ _ => True
  | Pair _ _, Pair _ _ => True
  | Fst _, Fst _ => True
  | Snd _, Snd _ => True
  | InjL _, InjL _ => True
  | InjR _, InjR _ => True
  | Match _ x1 _ y1 _, Match _ x2 _ y2 _ => x1 = x2 ∧ y1 = y2
  | Fork _, Fork _ => True
  | AllocN _ _, AllocN _ _ => True
  | FreeN _ _, FreeN _ _ => True
  | Load o1 _, Load o2 _ => o1 = o2
  | Store o1 _ _, Store o2 _ _ => o1 = o2
  | CmpXchg _ _ _, CmpXchg _ _ _ => True
  | FAA _ _, FAA _ _ => True
  | _, _ => False
  end.

Fixpoint val_wf (v : val) : Prop :=
  match v with
  | LitV (LitLoc l) => False (* no literal locations allowed *)
  | LitV _ => True
  | PairV v1 v2 => val_wf v1 ∧ val_wf v2
  | InjLV v => val_wf v
  | InjRV v => val_wf v
  end.
Section expr_wf.
  Context (expr_wf : expr → Prop).
  Fixpoint struct_expr_wf (e : expr) : Prop :=
    expr_wf e ∧
    match e with
    | Val v => True
    | Var x => True
    | Let b e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | Call e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | UnOp op e => struct_expr_wf e
    | BinOp op e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | If e1 e2 e3 => struct_expr_wf e1 ∧ struct_expr_wf e2 ∧ struct_expr_wf e3
    | While e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | Pair e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | Fst e => struct_expr_wf e
    | Snd e => struct_expr_wf e
    | InjL e => struct_expr_wf e
    | InjR e => struct_expr_wf e
    | Match e x1 e1 x2 e2 => struct_expr_wf e ∧ struct_expr_wf e1 ∧ struct_expr_wf e2
    | Fork e => struct_expr_wf e
    | AllocN e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | FreeN e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | Load o e => struct_expr_wf e
    | Store o e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | CmpXchg e1 e2 e3 => struct_expr_wf e1 ∧ struct_expr_wf e2 ∧ struct_expr_wf e3
    | FAA e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    end.

  Definition ectxi_wf (Ki : ectx_item) : Prop :=
    (∀ e, expr_wf (fill_item Ki e)) ∧
    match Ki with
    | LetCtx _ e => struct_expr_wf e
    | CallLCtx v => struct_expr_wf v
    | CallRCtx e => struct_expr_wf e
    | UnOpCtx _ => True
    | BinOpLCtx _ v => struct_expr_wf v
    | BinOpRCtx _ e => struct_expr_wf e
    | IfCtx e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | PairLCtx v => struct_expr_wf v
    | PairRCtx e => struct_expr_wf e
    | FstCtx | SndCtx | InjLCtx | InjRCtx | LoadCtx _ => True
    | MatchCtx _ e1 _ e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | AllocNLCtx v => struct_expr_wf v
    | AllocNRCtx e => struct_expr_wf e
    | FreeNLCtx v => struct_expr_wf v
    | FreeNRCtx e => struct_expr_wf e
    | StoreLCtx _ v => struct_expr_wf v
    | StoreRCtx _ e => struct_expr_wf e
    | CmpXchgLCtx v1 v2 => struct_expr_wf v1 ∧ struct_expr_wf v2
    | CmpXchgMCtx e1 v2 => struct_expr_wf e1 ∧ struct_expr_wf v2
    | CmpXchgRCtx e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | FaaLCtx v => struct_expr_wf v
    | FaaRCtx e => struct_expr_wf e
    end.
  Definition ectx_wf : ectx → Prop := Forall ectxi_wf.

  Lemma ectx_wf_app C1 C2 :
    ectx_wf (C1 ++ C2) ↔ ectx_wf C1 ∧ ectx_wf C2.
  Proof. apply Forall_app. Qed.
  Lemma ectx_wf_snoc C Ci :
    ectx_wf (C ++ [Ci]) ↔ ectx_wf C ∧ ectxi_wf Ci.
  Proof. rewrite ectx_wf_app /ectx_wf Forall_singleton //. Qed.

  (** Lift our "type system" to contexts. *)
  Definition ctxi_wf (Ci : ctx_item) : Prop :=
    (∀ e, expr_wf (fill_ctx_item Ci e)) ∧
    match Ci with
    | LetLCCtx _ e => struct_expr_wf e
    | LetRCCtx _ e => struct_expr_wf e
    | CallLCCtx e => struct_expr_wf e
    | CallRCCtx e => struct_expr_wf e
    | UnOpCCtx _ => True
    | BinOpLCCtx _ e => struct_expr_wf e
    | BinOpRCCtx _ e => struct_expr_wf e
    | IfLCCtx e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | IfMCCtx e0 e2 => struct_expr_wf e0 ∧ struct_expr_wf e2
    | IfRCCtx e0 e1 => struct_expr_wf e0 ∧ struct_expr_wf e1
    | WhileLCCtx e1 => struct_expr_wf e1
    | WhileRCCtx e0 => struct_expr_wf e0
    | PairLCCtx e => struct_expr_wf e
    | PairRCCtx e => struct_expr_wf e
    | FstCCtx | SndCCtx | InjLCCtx | InjRCCtx => True
    | MatchLCCtx _ e1 _ e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | MatchMCCtx e0 _ _ e2 => struct_expr_wf e0 ∧ struct_expr_wf e2
    | MatchRCCtx e0 _ e1 _ => struct_expr_wf e0 ∧ struct_expr_wf e1
    | ForkCCtx => True
    | AllocNLCCtx e => struct_expr_wf e
    | AllocNRCCtx e => struct_expr_wf e
    | FreeNLCCtx e => struct_expr_wf e
    | FreeNRCCtx e => struct_expr_wf e
    | LoadCCtx _ => True
    | StoreLCCtx _ e => struct_expr_wf e
    | StoreRCCtx _ e => struct_expr_wf e
    | CmpXchgLCCtx e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | CmpXchgMCCtx e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | CmpXchgRCCtx e1 e2 => struct_expr_wf e1 ∧ struct_expr_wf e2
    | FaaLCCtx e => struct_expr_wf e
    | FaaRCCtx e => struct_expr_wf e
    end.
  Definition ctx_wf : ctx → Prop := Forall ctxi_wf.

  Lemma ctx_wf_app C1 C2 :
    ctx_wf (C1 ++ C2) ↔ ctx_wf C1 ∧ ctx_wf C2.
  Proof. apply Forall_app. Qed.
  Lemma ctx_wf_snoc C Ci :
    ctx_wf (C ++ [Ci]) ↔ ctx_wf C ∧ ctxi_wf Ci.
  Proof. rewrite ctx_wf_app /ctx_wf Forall_singleton //. Qed.

  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (val_rel : val → val → iProp Σ).
  Context (thread_own : thread_id → iProp Σ).
  Notation log_rel := (log_rel val_rel thread_own).

  (* TODO: What is a good name for this? *)
  Definition log_rel_exprs : Prop :=
    (∀ e_t e_s, expr_wf e_s → expr_same_shape e_t e_s → ([∗list]e_t'; e_s'∈sub_exprs e_t; sub_exprs e_s, log_rel e_t' e_s') -∗ log_rel e_t e_s).

  Theorem log_rel_refl e :
    log_rel_exprs →
    struct_expr_wf e → ⊢ log_rel e e.
  Proof.
    intros He Hwf.
    iInduction e as [ ] "IH" forall (Hwf); destruct Hwf; iApply He; try done; simpl.
    all: try iDestruct ("IH" with "[%]") as "$".
    all: try iDestruct ("IH1" with "[%]") as "$".
    all: try iDestruct ("IH2" with "[%]") as "$".
    all: naive_solver.
  Qed.

  Theorem log_rel_ectx K e_t e_s :
    log_rel_exprs →
    ectx_wf K → log_rel e_t e_s -∗ log_rel (fill K e_t) (fill K e_s).
  Proof.
    intros He Hwf. iInduction (K) as [ | Ki K] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->ectx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_app /=. specialize (Hewf (fill K e_s)).
    destruct Ki; simpl; iApply He => //=; iFrame "IH".
    all: repeat iSplit; try done.
    all: iApply log_rel_refl; [done|].
    all: naive_solver.
  Qed.

  Theorem log_rel_ctx C e_t e_s :
    log_rel_exprs →
    ctx_wf C → log_rel e_t e_s -∗ log_rel (fill_ctx C e_t) (fill_ctx C e_s).
  Proof.
    intros He Hwf. iInduction (C) as [ | Ci C] "IH" using rev_ind; first by eauto.
    iIntros "Hrel".
    rewrite ->ctx_wf_snoc in Hwf. destruct Hwf as [Kwf [Hewf Hiwf]].
    iSpecialize ("IH" with "[//] Hrel").
    rewrite !fill_ctx_app /=. specialize (Hewf (fill_ctx C e_s)).
    destruct Ci; simpl; iApply He => //=; iFrame "IH".
    all: repeat iSplit; try done.
    all: iApply log_rel_refl; [done|].
    all: naive_solver.
  Qed.

End expr_wf.
