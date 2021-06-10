From simuliris.simplang Require Import lang.
From stdpp Require Import fin_maps.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | Let ?x ?e1 ?e2                  => add_item (LetEctx x e2) K e1
    | UnOp ?op ?e                     => add_item (UnOpEctx op) K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLEctx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpREctx op e1) K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfEctx e1 e2) K e0
    | Pair ?e (Val ?v)                => add_item (PairLEctx v) K e
    | Pair ?e1 ?e2                    => add_item (PairREctx e1) K e2
    | Fst ?e                          => add_item FstEctx K e
    | Snd ?e                          => add_item SndEctx K e
    | InjL ?e                         => add_item InjLEctx K e
    | InjR ?e                         => add_item InjREctx K e
    | Match ?e0 ?x1 ?e1 ?x2 ?e2       => add_item (MatchEctx x1 e1 x2 e2) K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLEctx v) K e
    | AllocN ?e1 ?e2                  => add_item (AllocNREctx e1) K e2
    | FreeN ?e1 (Val ?v)              => add_item (FreeNLEctx v) K e1
    | FreeN ?e1 ?e2                   => add_item (FreeNREctx e1) K e2
    | Load ?o ?e                      => add_item (LoadEctx o) K e
    | Store ?o ?e (Val ?v)            => add_item (StoreLEctx o v) K e
    | Store ?o ?e1 ?e2                => add_item (StoreREctx o e1) K e2
    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLEctx v1 v2) K e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMEctx e0 v2) K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgREctx e0 e1) K e2
    | FAA ?e (Val ?v)                 => add_item (FaaLEctx v) K e
    | FAA ?e1 ?e2                     => add_item (FaaREctx e1) K e2
    | Call ?e (Val ?v)                => add_item (CallLEctx v) K e
    | Call ?e1 ?e2                    => add_item (CallREctx e1) K e2
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
  | H : head_step ?P ?e ?σ ?e2 ?σ2 ?efs |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _ _) => eexists _, _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : head_step.
(*Global Hint Extern 0 (head_step _ (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : head_step.*)
Global Hint Extern 0 (head_step _ (AllocN _ _) _ _ _ _) => apply alloc_fresh : head_step.
