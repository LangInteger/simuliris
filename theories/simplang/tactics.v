From simuliris.simplang Require Import lang.
From stdpp Require Import fin_maps.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (AppLCtx v) K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | Pair ?e (Val ?v)                => add_item (PairLCtx v) K e
    | Pair ?e1 ?e2                    => add_item (PairRCtx e1) K e2
    | Fst ?e                          => add_item FstCtx K e
    | Snd ?e                          => add_item SndCtx K e
    | InjL ?e                         => add_item InjLCtx K e
    | InjR ?e                         => add_item InjRCtx K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) K e
    | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) K e2
    | Free ?e                         => add_item FreeCtx K e
    | Load ?e                         => add_item LoadCtx K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) K e2
    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLCtx v1 v2) K e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMCtx e0 v2) K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgRCtx e0 e1) K e2
    | FAA ?e (Val ?v)                 => add_item (FaaLCtx v) K e
    | FAA ?e1 ?e2                     => add_item (FaaRCtx e1) K e2
    | Call ?f ?e                      => add_item (CallCtx f) K e
    end
  with add_item Ki K e :=
      go (Ki :: K) e
  in
  go (@nil ectx_item) e.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?P ?e ?σ ?e2 ?σ2 |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _ _) => eexists _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 0 (head_step _ (CmpXchg _ _ _) _ _ _) => eapply CmpXchgS : head_step.
Global Hint Extern 0 (head_step _ (AllocN _ _) _ _ _) => apply alloc_fresh : head_step.
