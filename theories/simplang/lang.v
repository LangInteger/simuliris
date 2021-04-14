From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From simuliris.simulation Require Export language.
From simuliris.simplang Require Export locations.
From iris.prelude Require Import options.

(** heap_lang.  A fairly simple language used for common Iris examples.

Noteworthy design choices:

- This is a right-to-left evaluated language, like CakeML and OCaml.  The reason
  for this is that it makes curried functions usable: Given a WP for [f a b], we
  know that any effects [f] might have do not matter until after *both* [a] and
  [b] are evaluated.  With left-to-right evaluation, that triple is basically
  useless unless the user let-expands [b].

- Even after deallocating a location, the heap remembers that these locations
  were previously allocated and makes sure they do not get reused. This is
  necessary to ensure soundness of the [meta] feature provided by [gen_heap].
  Also, unlike in languages like C, allocated and deallocated "blocks" do not
  have to match up: you can allocate a large array of locations and then
  deallocate a hole out of it in the middle.
*)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module simp_lang.

(** Expressions and vals. *)

(** We have a notion of "poison" as a variant of unit that may not be compared
with anything. This is useful for erasure proofs: if we erased things to unit,
[<erased> == unit] would evaluate to true after erasure, changing program
behavior. So we erase to the poison value instead, making sure that no legal
comparisons could be affected. *)
Definition fname := string.
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitFn (fn : fname).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
    (* instead of lambda abstractions, we have let expressions and calls *)
  | Var (x : string)
  | Let (x : binder) (e1 e2 : expr)
  | Call (e1 : expr) (e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | While (e0 e1 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Match (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
with val :=
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition to_fname (e : expr) : option fname :=
  match to_val e with
  | Some (LitV (LitFn fn)) => Some fn
  | _ => None
  end.
Definition of_fname (fn : fname) := Val $ LitV $ LitFn fn.

Definition of_call f v := Call (of_fname f) (of_val v).
Definition to_call (e : expr) : option (fname * val) :=
  match e with
  | Call e1 e2 =>
      match to_fname e1 with
      | Some fn => option_map (pair fn) (to_val e2)
      | _ => None
      end
  | _ => None
  end.


(** We assume the following encoding of values to 64-bit words: The least 3
significant bits of every word are a "tag", and we have 61 bits of payload,
which is enough if all pointers are 8-byte-aligned (common on 64bit
architectures). The tags have the following meaning:

0: Payload is the data for a LitV (LitInt _).
1: Payload is the data for a InjLV (LitV (LitInt _)).
2: Payload is the data for a InjRV (LitV (LitInt _)).
3: Payload is the data for a LitV (LitLoc _).
4: Payload is the data for a InjLV (LitV (LitLoc _)).
4: Payload is the data for a InjRV (LitV (LitLoc _)).
6: Payload is one of the following finitely many values, which 61 bits are more
   than enough to encode:
   LitV LitUnit, InjLV (LitV LitUnit), InjRV (LitV LitUnit),
   LitV LitPoison, InjLV (LitV LitPoison), InjRV (LitV LitPoison),
   LitV (LitBool _), InjLV (LitV (LitBool _)), InjRV (LitV (LitBool _)).
7: Value is boxed, i.e., payload is a pointer to some read-only memory area on
   the heap which stores whether this is a RecV, PairV, InjLV or InjRV and the
   relevant data for those cases. However, the boxed representation is never
   used if any of the above representations could be used.

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  | LitPoison => False
  | LitInt _ | LitBool _  | LitLoc _ | LitFn _ | LitUnit => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(** The state: heaps of [option val]s, with [None] representing deallocated locations. *)
Record state : Type := {
  heap: gmap loc (option val);
}.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Lemma to_of_call f v : to_call (of_call f v) = Some (f, v).
Proof. reflexivity. Qed.

Lemma of_to_call e f v : to_call e = Some (f, v) → of_call f v = e.
Proof.
  destruct e => //=. destruct e1 => //=.
  match goal with |- context[Val ?v] => destruct v as [[] | | |] => //= end.
  destruct e2 => //=. by intros [= <- <-].
Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Let x e1 e2, Let x' e1' e2' =>
        cast_if_and3 (decide (x = x')) (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | While e0 e1, While e0' e1' =>
        cast_if_and (decide (e0 = e0')) (decide (e1 = e1'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Match e0 x1 e1 x2 e2, Match e0' x1' e1' x2' e2' =>
        cast_if_and5 (decide (e0 = e0')) (decide (x1 = x1')) (decide (e1 = e1')) (decide (x2 = x2')) (decide (e2 = e2'))
     | Fork e, Fork e' => cast_if (decide (e = e'))
     | AllocN e1 e2, AllocN e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Free e, Free e' =>
        cast_if (decide (e = e'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | CmpXchg e0 e1 e2, CmpXchg e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | FAA e1 e2, FAA e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Call f1 e1, Call f2 e2 =>
        cast_if_and (decide (f1 = f2)) (decide (e1 = e2))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for go); try (clear go gov; abstract intuition congruence).
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl n))
  | LitBool b => (inl (inr b))
  | LitUnit => (inr (inl false))
  | LitPoison => (inr (inl true))
  | LitLoc l => (inr (inr (inr l)))
  | LitFn fn => (inr (inr (inl fn)))
  end) (λ l, match l with
  | (inl (inl n)) => LitInt n
  | (inl (inr b)) => LitBool b
  | (inr (inl false)) => LitUnit
  | (inr (inl true)) => LitPoison
  | (inr (inr (inr l))) => LitLoc l
  | (inr (inr (inl fn))) => LitFn fn
  end) _); by intros [].
Qed.
Global Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.
Global Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Let x e1 e2 => GenNode 1 [GenLeaf (inl (inr x)); go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Match e0 x1 e1 x2 e2 => GenNode 11 [go e0; GenLeaf (inl (inr x1)); go e1; GenLeaf (inl (inr x2)); go e2]
     | Fork e => GenNode 12 [go e]
     | AllocN e1 e2 => GenNode 13 [go e1; go e2]
     | Free e => GenNode 14 [go e]
     | Load e => GenNode 15 [go e]
     | Store e1 e2 => GenNode 16 [go e1; go e2]
     | CmpXchg e0 e1 e2 => GenNode 17 [go e0; go e1; go e2]
     | FAA e1 e2 => GenNode 18 [go e1; go e2]
     | Call e1 e2 => GenNode 19 [go e1; go e2]
     | While e0 e1 => GenNode 20 [go e0; go e1]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr x)); e1; e2] => Let x (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; GenLeaf (inl (inr x1)); e1; GenLeaf (inl (inr x2)); e2] => Match (go e0) x1 (go e1) x2 (go e2)
     | GenNode 12 [e] => Fork (go e)
     | GenNode 13 [e1; e2] => AllocN (go e1) (go e2)
     | GenNode 14 [e] => Free (go e)
     | GenNode 15 [e] => Load (go e)
     | GenNode 16 [e1; e2] => Store (go e1) (go e2)
     | GenNode 17 [e0; e1; e2] => CmpXchg (go e0) (go e1) (go e2)
     | GenNode 18 [e1; e2] => FAA (go e1) (go e2)
     | GenNode 19 [e1; e2] => Call (go e1) (go e2)
     | GenNode 20 [e0; e1] => While (go e0) (go e1)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v| | | | | | | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Evaluation contexts *)
Inductive ectx_item :=
  (* we can evaluate the expression that x will be bound to *)
  | LetCtx (x : binder) (e2 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | MatchCtx (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | FreeCtx
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | CmpXchgLCtx (v1 : val) (v2 : val)
  | CmpXchgMCtx (e0 : expr) (v2 : val)
  | CmpXchgRCtx (e0 : expr) (e1 : expr)
  | FaaLCtx (v2 : val)
  | FaaRCtx (e1 : expr)
  | CallLCtx (v2 : val)
  | CallRCtx (e1 : expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | LetCtx x e2 => Let x e e2
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | MatchCtx x1 e1 x2 e2 => Match e x1 e1 x2 e2
  | AllocNLCtx v2 => AllocN e (Val v2)
  | AllocNRCtx e1 => AllocN e1 e
  | FreeCtx => Free e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | CmpXchgLCtx v1 v2 => CmpXchg e (Val v1) (Val v2)
  | CmpXchgMCtx e0 v2 => CmpXchg e0 e (Val v2)
  | CmpXchgRCtx e0 e1 => CmpXchg e0 e1 e
  | FaaLCtx v2 => FAA e (Val v2)
  | FaaRCtx e1 => FAA e1 e
  | CallLCtx v2 => Call e (Val v2)
  | CallRCtx e1 => Call e1 e
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Let y e1 e2 =>
     Let y (subst x v e1) (if decide (BNamed x ≠ y) then subst x v e2 else e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | While e0 e1 => While (subst x v e0) (subst x v e1)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Match e0 x1 e1 x2 e2 => Match (subst x v e0) x1 (if decide (BNamed x ≠ x1) then subst x v e1 else e1)
      x2 (if decide (BNamed x ≠ x2) then subst x v e2 else e2)
  | Fork e => Fork (subst x v e)
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Free e => Free (subst x v e)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  | Call e1 e2 => Call (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

Definition state_upd_heap (f: gmap loc (option val) → gmap loc (option val)) (σ: state) : state :=
  {| heap := f σ.(heap) |}.
Global Arguments state_upd_heap _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc (option val) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := Some v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := Some v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = Some w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc (option val)) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=Some v]> σ.
Proof.
  destruct σ as [h]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Definition free_chunk (l:positive) (σ:gmap loc (option val)) : gmap loc (option val) :=
  filter (λ '(l', _), loc_chunk l' ≠ l) σ.

(** Building actual evaluation contexts out of ectx_items *)
Definition ectx := list ectx_item.
Definition empty_ectx : ectx := [].
Definition ectx_compose : ectx → ectx → ectx := flip (++).

Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.

Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

(** Programs *)
Definition prog := gmap fname ectx.

Notation "e1 ;; e2" := (Let BAnon e1%E e2%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.
Inductive head_step (P : prog) : expr → state → expr → state → Prop :=
  | PairS v1 v2 σ :
     head_step P (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
  | InjLS v σ :
     head_step P (InjL $ Val v) σ (Val $ InjLV v) σ
  | InjRS v σ :
     head_step P (InjR $ Val v) σ (Val $ InjRV v) σ
  | LetS x v1 e2 e' σ :
     e' = subst' x v1 e2 →
     head_step P (Let x (Val $ v1) e2) σ e' σ
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step P (UnOp op (Val v)) σ (Val v') σ
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step P (BinOp op (Val v1) (Val v2)) σ (Val v') σ
  | IfTrueS e1 e2 σ :
     head_step P (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
  | IfFalseS e1 e2 σ :
     head_step P (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
  | WhileS e0 e1 σ :
      head_step P (While e0 e1) σ (If e0 (e1 ;; While e0 e1) (Val $ LitV $ LitUnit)) σ
  | FstS v1 v2 σ :
     head_step P (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
  | SndS v1 v2 σ :
     head_step P (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
  | MatchLS v x1 e1 x2 e2 e' σ :
      e' = subst' x1 v e1 →
     head_step P (Match (Val $ InjLV v) x1 e1 x2 e2) σ e' σ
  | MatchRS v x1 e1 x2 e2 e' σ :
      e' = subst' x2 v e2 →
     head_step P (Match (Val $ InjRV v) x1 e1 x2 e2) σ e' σ
  | ForkS e σ:
      (* TODO: for now, this is just a NOP -- maybe we want to change this later and add concurrency?*)
     head_step P (Fork e) σ (Val $ LitV LitUnit) σ
  | AllocNS n v σ l :
     (0 < n)%Z →
     (∃ b, l = Build_loc b 0) →
     (∀ i, σ.(heap) !! (l +ₗ i) = None) →
     head_step P (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               (Val $ LitV $ LitLoc l) (state_init_heap l n v σ)
  | FreeS l v σ :
     σ.(heap) !! l = Some $ Some v →
     head_step P (Free (Val $ LitV $ LitLoc l)) σ
               (Val $ LitV LitUnit) (state_upd_heap (free_chunk (loc_chunk l)) σ)
  | LoadS l v σ :
     σ.(heap) !! l = Some $ Some v →
     head_step P (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
  | StoreS l v w σ :
     σ.(heap) !! l = Some $ Some v →
     head_step P (Store (Val $ LitV $ LitLoc l) (Val w)) σ
               (Val $ LitV LitUnit) (state_upd_heap <[l:=Some w]> σ)
  | CmpXchgS l v1 v2 vl σ b :
     σ.(heap) !! l = Some $ Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     head_step P (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               (Val $ PairV vl (LitV $ LitBool b)) (if b then state_upd_heap <[l:=Some v2]> σ else σ)
  | FaaS l i1 i2 σ :
     σ.(heap) !! l = Some $ Some (LitV (LitInt i1)) →
     head_step P (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) σ
               (Val $ LitV $ LitInt i1) (state_upd_heap <[l:=Some $ LitV (LitInt (i1 + i2))]>σ)
  | CallS f v K σ :
     P !! f = Some K →
     head_step P (Call (Val $ LitV $ LitFn f) (Val v)) σ (fill K (Val v)) σ.


Definition of_class (m : mixin_expr_class val) : expr :=
  match m with
  | ExprVal v => of_val v
  | ExprCall f v => of_call f v
  end.
Definition to_class (e : expr) : option (mixin_expr_class val) :=
  match to_val e with
  | Some v => Some (ExprVal v)
  | None => option_map (λ '(fn, v), ExprCall fn v) (to_call e)
  end.

Lemma to_of_class m : to_class (of_class m) = Some m.
Proof. destruct m; done. Qed.
Lemma of_to_class e m : to_class e = Some m → of_class m = e.
Proof.
  destruct m.
  + destruct e; try discriminate 1; first by inversion 1.
    rewrite /to_class; simpl. destruct to_fname, to_val; simpl; congruence.
  + destruct e; try discriminate 1. rewrite /to_class; simpl.
    destruct e1; simpl.
    { destruct v as [[ | | | | |fn] | | | ]; simpl; try congruence.
      destruct e2; try discriminate 1. by inversion 1. }
    all: congruence.
Qed.

Lemma to_class_val e v : to_class e = Some (ExprVal v) → to_val e = Some v.
Proof.
  destruct e; simpl; try discriminate 1.
  - by inversion 1.
  - destruct e1; rewrite /to_class; simpl.
    { destruct to_fname; destruct e2; try discriminate 1. }
    all: discriminate 1.
Qed.
Lemma to_class_call e f v : to_class e = Some (ExprCall f v) → to_call e = Some (f, v).
Proof.
  destruct e; rewrite /to_class; simpl; try discriminate 1.
  destruct to_fname; simpl; try discriminate 1.
  destruct e2; simpl; try discriminate 1. by inversion 1.
Qed.

Lemma to_val_class e v : to_val e = Some v → to_class e = Some (ExprVal v).
Proof. destruct e; cbn; try discriminate 1. by inversion 1. Qed.
Lemma to_call_class e f v : to_call e = Some (f, v) → to_class e = Some (ExprCall f v).
Proof.
  destruct e; rewrite /to_call /to_class; simpl; try discriminate 1.
  destruct to_fname; try discriminate 1.
  destruct to_val; try discriminate 1. by inversion 1.
Qed.

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Global Instance fill_inj K : Inj (=) (=) (fill K).
Proof. induction K; intros ???; by simplify_eq/=. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.
Lemma fill_item_val_none Ki e :
  to_val e = None → to_val (fill_item Ki e) = None.
Proof.
  destruct (to_val (fill_item Ki e)) eqn:H.
  - edestruct (fill_item_val) as [v' ?]; [ eauto | congruence].
  - done.
Qed.

Lemma fill_val K e :
  is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  induction K in e |-*; intros [v ?].
  - simplify_option_eq; eauto.
  - eapply fill_item_val, IHK, mk_is_Some, H.
Qed.
Lemma fill_val_none K e :
  to_val e = None → to_val (fill K e) = None.
Proof.
  destruct (to_val (fill K e)) eqn:H.
  - edestruct (fill_val) as [v' ?]; [ eauto | congruence].
  - done.
Qed.

Lemma val_head_stuck P e1 σ1 e2 σ2 : head_step P e1 σ1 e2 σ2 → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val P Ki e σ1 e2 σ2 :
  head_step P (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e).
Proof. revert e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma head_step_fill_no_val P Ki K e σ1 e2 σ2 :
  head_step P (fill K (fill_item Ki e)) σ1 e2 σ2 → is_Some (to_val e).
Proof.
  revert e Ki.
  induction K as [ | Ki' K IH]; simpl; intros e Ki.
  - by intros ?%head_ctx_step_val.
  - intros H. eapply IH in H. by eapply fill_item_val.
Qed.

Lemma head_ectx_step_val P K e σ1 e2 σ2 :
  to_val e = None → head_step P (fill K e) σ1 e2 σ2 → K = empty_ectx.
Proof.
  intros Hnoval H.
  destruct K as [ | Ki K]; first reflexivity.
  exfalso. apply head_step_fill_no_val in H.
  eapply is_Some_None; by rewrite <-Hnoval.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; naive_solver eauto with f_equal.
Qed.

Lemma alloc_fresh P v n σ :
  let l := {| loc_chunk := fresh_block σ.(heap); loc_idx := 0 |} in
  (0 < n)%Z →
  head_step P (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ
            (Val $ LitV $ LitLoc l) (state_init_heap l n v σ).
Proof.
  intros. apply AllocNS; first done; first by eauto. apply is_fresh_block.
Qed.

Lemma fill_eq P σ1 σ2 e1 e1' e2 K K' :
  to_val e1 = None →
  head_step P e1' σ1 e2 σ2 →
  fill K e1 = fill K' e1' →
  ∃ K'', K' = ectx_compose K K''.
Proof.
  intros Hval Hstep; revert K'.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill; first by apply fill_val_none.
    apply fill_val_none. eauto using val_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. unfold ectx_compose. cbn. by rewrite assoc.
Qed.

(* Proving the mixin *)

Lemma simp_lang_mixin : LanguageMixin of_class to_class empty_ectx ectx_compose fill head_step.
Proof.
  constructor.
  - apply to_of_class.
  - apply of_to_class.
  - intros p v ??? H%val_head_stuck. cbn in H. congruence.
  - intros p f v ???. split.
    + cbn. inversion 1; subst. exists K. eauto.
    + intros (K & ? & -> & ->). cbn. by constructor.
  - done.
  - intros ???. by rewrite -fill_app.
  - apply fill_inj.
  - intros K e H.
    destruct to_class as [[]|] eqn:Heq; last by apply is_Some_None in H.
    + right. apply to_class_val in Heq.
      edestruct (fill_val K e) as [v' Hval]; first by eauto.
      exists v'. by apply to_val_class.
    + destruct (to_val e) eqn:Hval. { right; eauto using to_val_class. }
      left. apply to_class_call in Heq. clear H.
      assert (K ≠ empty_ectx → to_call (fill K e) = None) as H.
      { clear Heq. destruct K as [ | Ki K]; first by destruct 1. intros _.
        revert Hval. revert Ki e.
        induction K as [ | ?? IH]; cbn; intros Ki e Hval.
        - destruct Ki; cbn; try reflexivity.
          { rewrite /to_fname. by rewrite Hval. }
          rewrite Hval. by destruct to_fname.
        - cbn in IH. by apply IH, fill_item_val_none.
      }
      rewrite Heq in H. destruct K; first done.
      enough (Some (fn_name, arg) = None) by congruence. by apply H.
  - intros p K K' e1' e1_redex σ1 e2 σ2 H. destruct to_class as [ [] | ] eqn:Heq; first done.
    + intros _ Hstep.
      eapply fill_eq; [ | apply Hstep | apply H].
      rewrite <-(of_to_class _ _ Heq). reflexivity.
    + intros _ Hstep. eapply fill_eq; [ | apply Hstep | apply H].
      destruct to_val eqn:Hval; last done. apply to_val_class in Hval; congruence.
  - intros ?????? H.
    destruct (to_val e) eqn:Heq. { right. exists v. by apply to_val_class. }
    left. by eapply head_ectx_step_val.
Qed.
End simp_lang.

Canonical Structure simp_lang := Language (simp_lang.simp_lang_mixin).
Export simp_lang.
