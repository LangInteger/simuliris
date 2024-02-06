(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From stdpp Require Export countable binders gmap.
From iris.prelude Require Import prelude options.
From iris.prelude Require Import options.

(*Global Open Scope general_if_scope.*)
From simuliris.tree_borrows Require Export locations tree.

Declare Scope expr_scope.
Declare Scope val_scope.
Declare Scope sc_scope.
Declare Scope result_scope.
Declare Scope pointer.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Delimit Scope sc_scope with S.
Delimit Scope result_scope with R.

Local Open Scope Z_scope.

(** Id to track calls *)
Notation call_id := nat (only parsing).
(* Set of active call ids *)
Definition call_id_set := gset call_id.

(** Tags for pointers *)
Notation tag := nat (only parsing).

Inductive interior_mut := InteriorMut | TyFrz.
Global Instance interior_mut_eq_dec : EqDecision interior_mut.
Proof. solve_decision. Defined.
Global Instance interior_mut_countable : Countable interior_mut.
Proof.
  refine (inj_countable
    (λ m, match m with
           | InteriorMut => true
           | TyFrz => false
           end)
    (λ b, Some match b with
           | true => InteriorMut
           | false => TyFrz
           end)
    _); by intros [].
Qed.


Inductive res_conflicted := ResConflicted | ResActivable.
Global Instance res_conflicted_eq_dec : EqDecision res_conflicted.
Proof. solve_decision. Defined.
Global Instance res_conflicted_countable : Countable res_conflicted.
Proof.
  refine (inj_countable
    (λ m, match m with
           | ResConflicted => true
           | ResActivable => false
           end)
    (λ b, Some match b with
           | true => ResConflicted
           | false => ResActivable
           end)
    _); by intros [].
Qed.


Inductive permission :=
  | Reserved (mut:interior_mut) (confl:res_conflicted)
  | Active | Frozen | Disabled.
Global Instance permission_eq_dec : EqDecision permission.
Proof. solve_decision. Defined.
Global Instance permission_countable : Countable permission.
Proof.
  refine (inj_countable
    (λ p,
      match p with
      | Reserved m c => inr (m, c)
      | Active => inl 0 | Frozen => inl 1 | Disabled => inl 2
      end)
    (λ s,
      Some match s with
      | inr (m, c) => Reserved m c
      | inl 0 => Active | inl 1 => Frozen | inl _ => Disabled
      end) _); by intros [].
Qed.

Inductive prot_strong :=
  | ProtStrong
  | ProtWeak
  .
Inductive access_strong :=
  | AllProt
  | OnlyStrong
  .

Global Instance prot_strong_eq_dec : EqDecision prot_strong.
Proof. solve_decision. Defined.
Global Instance prot_strong_countable : Countable prot_strong.
Proof.
  refine (inj_countable'
    (λ p:prot_strong, if p then true else false)
    (λ b:bool, if b then ProtStrong else ProtWeak) _); by intros [].
Qed.

Definition prot_relevant (pr:prot_strong) (acc:access_strong) : bool :=
  match pr, acc with
  | ProtWeak, OnlyStrong => false
  | _, _ => true
  end.

(** Tree of borrows. *)
Record protector := mkProtector {
  strong : prot_strong;
  call : call_id;
}.
Global Instance protector_eq_dec : EqDecision protector.
Proof. solve_decision. Defined.
Global Instance protector_countable : Countable protector.
Proof.
  refine (inj_countable'
    (λ p:protector, (p.(strong), p.(call)))
    (λ t, {| strong:=t.1; call:=t.2 |}) _); by intros [].
Qed.


Inductive perm_init :=
  | PermInit
  | PermLazy
  .

Global Instance perm_init_eq_dec : EqDecision perm_init.
Proof. solve_decision. Defined.
Definition most_init p p' :=
  match p with
  | PermInit => PermInit
  | PermLazy => p'
  end.

Record lazy_permission := mkPerm {
  initialized : perm_init;
  perm        : permission;
}.
Global Instance lazy_perm_eq_dec : EqDecision lazy_permission.
Proof. solve_decision. Defined.

(* Permissions for one tag *)
Definition permissions := gmap Z lazy_permission.

(* Data associated with one tag *)
(* Note: this is a substructure of the miri "Node" *)
Record item := mkItem {
  itag  : tag;
  iprot : option protector;
  initp : permission;
  iperm : permissions;
}.
Global Instance item_eq_dec : EqDecision item.
Proof. solve_decision. Defined.

(* Per-allocation borrow data *)
Definition trees := gmap block (tree item).

(** Retag kinds *)
(* FIXME: simplify related stuff *)
Inductive retag_kind := FnEntry | Default.

(** Language base constructs *)

(** Unary/Binary ops *)
Inductive bin_op :=
  | AddOp     (* + addition       *)
  | SubOp     (* - subtraction    *)
(* | MulOp     (* * multiplication *)
  | DivOp     (* / division       *)
  | RemOp     (* % modulus        *)
  | BitXorOp  (* ^ bit xor        *)
  | BitAndOp  (* & bit and        *)
  | BitOrOp   (* | bit or         *)
  | ShlOp     (* << shift left    *)
  | ShrOp     (* >> shift right   *) *)
  | EqOp      (* == equality      *)
  | LtOp      (* < less than      *)
  | LeOp      (* <= less than or equal to *)
(* | NeOp      (* != not equal to  *)
  | GeOp      (* >= greater than or equal to *)
  | GtOp      (* > greater than   *) *)
  | OffsetOp  (* . offset         *)
  .

(** Base values *)
Notation fname := string (only parsing).
Inductive scalar :=
  ScPoison | ScInt (n: Z) | ScPtr (l: loc) (tg: tag) | ScFnPtr (fn: fname) | ScCallId (c : call_id).
Bind Scope sc_scope with scalar.
Definition value := list scalar.
Bind Scope val_scope with value.

Inductive access_kind := AccessRead | AccessWrite.
Inductive access_visibility := VisibleAll | OnlyNonChildren.

Inductive rel_pos := This | Parent | Child | Cousin.
Definition foreign rel := match rel with Parent | Cousin => True | _ => False end.
Definition child rel := match rel with This | Child => True | _ => False end.

Global Instance access_kind_eq_dec : EqDecision access_kind.
Proof. solve_decision. Qed.
Global Instance access_visibility_eq_dec : EqDecision access_visibility.
Proof. solve_decision. Qed.
Global Instance rel_pos_eq_dec : EqDecision rel_pos.
Proof. solve_decision. Qed.
Global Instance foreign_rel_dec rel : Decision (foreign rel).
Proof. destruct rel; solve_decision. Qed.
Global Instance child_rel_dec rel : Decision (child rel).
Proof. destruct rel; solve_decision. Qed.

Record newperm := mkNewPerm {
  initial_state : permission;
  new_protector : option protector;
}.
Global Instance newperm_eq_dec : EqDecision newperm.
Proof. solve_decision. Qed.
Global Instance newperm_countable : Countable newperm.
Proof.
  refine (inj_countable'
    (λ newp, (newp.(initial_state), newp.(new_protector)))
    (λ t, {| initial_state:=t.1; new_protector:=t.2 |}) _); by intros [].
Qed.


(** Expressions *)
Inductive expr :=
(* base values *)
| Val (v : value)
(* variables *)
| Var (x : string)
(* function calls *)
| Call (e1 : expr) (e2 : expr)  (* Call a function through a FnPtr `e1` with argument `e2` *)
| InitCall                      (* Initializing a stack frame and return the ID *)
| EndCall (e : expr)               (* End the current call with ID `e` *)
(* operations on value *)
| Proj (e1 e2 : expr)             (* Projection out sub value *)
| Conc (e1 e2 : expr)             (* concatenate lists of scalars *)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* place operation *)
| Place (l : loc) (tg : tag) (sz : nat)
                                  (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e : expr) (sz : nat)       (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has the kind and size of `ptr`. *)
| Ref (e : expr)                   (* Turn a place `e` into a pointer value. *)
(* | Field (e: expr) (path: list nat)(* Create a place that points to a component
                                     of the place `e`. `path` defines the path
                                     through the type. *) *)
(* mem op *)
| Copy (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2 : expr)             (* Write the value `e2` to the place `e1` *)
| Alloc (sz : nat)                 (* Allocate a place of type `T` *)
| Free (e : expr)                 (* Free the place `e` *)
(* atomic mem op *)
(* | CAS (e0 e1 e2 : expr) *)     (* CAS the value `e2` for `e1` to the place `e0` *)
(* | AtomWrite (e1 e2: expr) *)
(* | AtomRead (e: expr) *)
(* retag *) (* Retag the memory pointed to by `e1` of type (Reference pk T) with
  retag kind `kind`, for call_id `e2`. *)
| Retag (e1 : expr) (e2 : expr) (newp : newperm) (sz : nat) (kind : retag_kind)
(* let binding *)
| Let (x : binder) (e1 e2: expr)
(* case *)
| Case (e : expr) (el: list expr)
(* concurrency *)
| Fork (e : expr)
(* While *)
| While (e1 e2 : expr)
(* observable behavior *)
(* | SysCall (id: nat) *)
.

Bind Scope expr_scope with expr.

Arguments Val _%E.
Arguments BinOp _ _%E _%E.
Arguments Call _%E _%E.
Arguments EndCall _%E.
Arguments Proj _%E _%E.
Arguments Conc _%E _%E.
Arguments Deref _%E _%nat.
Arguments Ref _%E.
Arguments Copy _%E.
Arguments Write _%E _%E.
Arguments Alloc _%nat.
Arguments Free _%E.
Arguments Retag _%E _%E _%nat _.
Arguments Let _%binder _%E _%E.
Arguments Case _%E _%E.
Arguments While _%E _%E.

(** Closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ | Place _ _ _ | Alloc _ | InitCall (* | SysCall _ *) => true
  | Var x => bool_decide (x ∈ X)
  | BinOp _ e1 e2 | Write e1 e2 | While e1 e2 
      | Conc e1 e2 | Proj e1 e2 | Call e1 e2 | Retag e1 e2 _ _ _ => is_closed X e1 && is_closed X e2
  | Let x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Case e el 
      => is_closed X e && forallb (is_closed X) el
  | Fork e | Copy e | Deref e _ | Ref e (* | Field e _ *)
      | Free e | EndCall e (* | AtomRead e | Fork e *)
      => is_closed X e
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
#[global]
Hint Mode Closed + + : typeclass_instances.
Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Global Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

(** Irreducible (language values) *)
Inductive result :=
| ValR (v : value)
| PlaceR (l : loc) (tg : tag) (sz : nat)
.
Bind Scope result_scope with result.

Definition of_result (v : result) : expr :=
  match v with
  | ValR v => Val v
  | PlaceR l tag ptr => Place l tag ptr
  end.

Definition to_result (e : expr) : option result :=
  match e with
  | Val v => Some (ValR v)
  | Place l tag ptr => Some (PlaceR l tag ptr)
  | _ => None
  end.

Definition to_value (e : expr) : option value :=
  match e with
  | Val v => Some v
  | _ => None
  end.
Definition of_value (v : value) : expr := Val v.

Definition to_fname (e : expr) : option fname :=
  match to_value e with
  | Some ([ScFnPtr fn]) => Some fn
  | _ => None
  end.
Definition of_fname (fn : fname) := Val $ [ScFnPtr fn].

Definition of_call f r := Call (of_fname f) (of_result r).
Definition to_call (e : expr) : option (fname * result) :=
  match e with
  | Call e1 e2 =>
      match to_fname e1 with
      | Some fn => option_map (pair fn) (to_result e2)
      | _ => None
      end
  | _ => None
  end.


Lemma is_Some_to_value_result (e: expr):
  is_Some (to_value e) → is_Some (to_result e).
Proof. destruct e; simpl; intros []; naive_solver. Qed.

Lemma Val_to_value e v : to_value e = Some v → Val v = e.
Proof. destruct e; try discriminate. intros [= ->]. done. Qed.

Lemma list_Forall_to_value (es: list expr):
  Forall (λ ei, is_Some (to_value ei)) es ↔ (∃ vs, es = Val <$> vs).
Proof.
  induction es as [ | e es IH]; split.
  - intros _. exists []. done.
  - intros _. constructor.
  - intros [[v EQv] [vs EQvs]%IH]%Forall_cons. exists (v::vs).
    simpl. f_equal; last done.
    erewrite Val_to_value; done.
  - intros [[|v vs] EQ]; first discriminate.
    move:EQ=> [= -> EQ]. constructor; first by eauto.
    apply IH. eexists. done.
Qed.

(** Main state: a heap of scalars, each with an associated lock to detect data races. *)
Definition mem := gmap loc scalar.

(** Internal events *)

Inductive bor_local_event :=
  | AccessBLEvt (kind : access_kind) (tg : tag) (range : Z * nat)
  | InitCallBLEvt (cid : call_id)
  | EndCallBLEvt (cid : call_id)
  | RetagBLEvt (tgp tg : tag) (newp : newperm) (c : call_id)
  | SilentBLEvt.

(** Internal events *)
Inductive event :=
| AllocEvt (alloc : block) (lbor : tag) (range : Z * nat)
| DeallocEvt (alloc : block) (lbor: tag) (range : Z * nat)
| CopyEvt (alloc : block) (lbor : tag) (range : Z * nat) (v : value)
| FailedCopyEvt (alloc : block) (lbor : tag) (range : Z * nat)
| WriteEvt (alloc : block) (lbor : tag) (range : Z * nat) (v : value)
| InitCallEvt (c : call_id)
| EndCallEvt (c : call_id)
| RetagEvt (alloc : block) (otag ntag : tag) (newp : newperm) (c : call_id)
| SilentEvt.

