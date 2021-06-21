From simuliris.stacked_borrows Require Import lang.
From stdpp Require Import fin_maps.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | Call ?e (Val ?v)                => add_item (CallLCtx (ValR v)) K e
    | Call ?e (Place ?l ?t ?T)        => add_item (CallLCtx (PlaceR l t T)) K e
    | Call ?e1 ?e2                    => add_item (CallRCtx e1) K e2
    | EndCall ?e                      => add_item (EndCallCtx) K e
    | Proj ?e1 (Val ?v)               => add_item (ProjLCtx (ValR v)) K e1
    | Proj ?e1 (Place ?l ?t ?T)       => add_item (ProjLCtx (PlaceR l t T)) K e1
    | Proj ?e1 ?e2                    => add_item (ProjRCtx e1) K e2
    | Conc ?e1 (Val ?v)               => add_item (ProjLCtx (ValR v)) K e1
    | Conc ?e1 (Place ?l ?t ?T)       => add_item (ProjLCtx (PlaceR l t T)) K e1 
    | Conc ?e1 ?e2                    => add_item (ConcRCtx e1) K e2
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op (ValR v)) K e
    | BinOp ?op ?e (Place ?l ?t ?T)   => add_item (BinOpLCtx op (PlaceR l t T)) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) K e2
    | Deref ?e ?T                     => add_item (DerefCtx T) K e
    | Ref ?e                          => add_item RefCtx K e
    | Copy ?e                         => add_item CopyCtx K e
    | Write ?e (Val ?v)               => add_item (WriteLCtx (ValR v)) K e
    | Write ?e (Place ?l ?t ?T)       => add_item (WriteLCtx (PlaceR l t T)) K e
    | Write ?e1 ?e2                   => add_item (WriteRCtx e1) K e2 
    | Free ?e                         => add_item FreeCtx K e
    | Retag ?e (Val ?v) ?pk ?T ?rk    => add_item (RetagLCtx (ValR v) pk T rk) K e
    | Retag ?e (Place ?l ?t ?T) ?pk ?T ?rk    => add_item (RetagLCtx (PlaceR l t T) pk T rk) K e
    | Retag ?e1 ?e2 ?pk ?T ?rk        => add_item (RetagRCtx e1 pk T rk) K e2
    | Let ?x ?e1 ?e2                  => add_item (LetCtx x e2) K e1
    | Case ?e ?el                     => add_item (CaseCtx el) K e 
    end
  with add_item Ki K e :=
      go (Ki :: K) e
  in
  go (@nil ectx_item) e.

Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step _ ?e _ _ _ _ |- _  =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  | H : mem_expr_step _ _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : pure_expr_step _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : bor_step _ _ _ _ _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : bin_op_eval _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _ _) => eexists _, _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : head_step.
