(** Contextual refinement soundness result. *)
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang Require Import proofmode tactics.
From simuliris.simplang Require Import heapbij_refl.

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
