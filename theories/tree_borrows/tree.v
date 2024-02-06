From iris.prelude Require Import prelude options.
From iris.prelude Require Import options.

Implicit Type (V W X Y:Type).

Definition app X : Type := X -> option X.
Definition Tprop X : Type := X -> Prop.

(** General Preliminaries *)

Definition option_bind {X Y} (fn:X -> option Y)
  : option X -> option Y :=
  fun ox => x ← ox; fn x.

Definition option_join {X}
  : option (option X) -> option X :=
  fun oox => ox ← oox; ox.

(* Generic tree
   Note: we are using the "tilted" representation of n-ary trees
         where the binary children are the next n-ary sibling and
         the first n-ary child.
         This is motivated by the much nicer induction principles
         we get, but requires more careful definition of the
         parent-child relationship.
   *)
Inductive tree X :=
  | empty
  | branch (data:X) (sibling child:tree X)
  .
(* x
   |- y1
   |- y2
   |- y3
   |- y4

   branch x
    (branch y1
      (branch y2
        (branch y3
          (branch y4)
          empty
        empty
      empty
    empty
 *)

Arguments empty {X}.
Arguments branch {X} data sibling child.
Definition tbranch X : Type := X * tree X * tree X.

Definition of_branch {X} (br:tbranch X)
  : tree X :=
  let '(root, lt, rt) := br in branch root lt rt.

Definition fold_subtrees {X Y} (unit:Y) (combine:tbranch X -> Y -> Y -> Y)
  : tree X -> Y := fix aux tr : Y :=
  match tr with
  | empty => unit
  | branch data sibling child => combine (data, sibling, child) (aux sibling) (aux child)
  end.

Definition root {X} (br:tbranch X)
  : X := let '(r, _, _) := br in r.

Definition fold_nodes {X Y} (unit:Y) (combine:X -> Y -> Y -> Y)
  : tree X -> Y := fold_subtrees unit (fun subtree sibling child => combine (root subtree) sibling child).

Definition map_nodes {X Y} (fn:X -> Y) : tree X -> tree Y := fold_nodes empty (compose branch fn).

Definition join_nodes {X}
  : tree (option X) -> option (tree X) := fix aux tr {struct tr} : option (tree X) :=
  match tr with
  | empty => Some empty
  | branch data sibling child =>
    data ← data;
    sibling ← aux sibling;
    child ← aux child;
    Some $ branch data sibling child
  end.

Definition every_subtree {X} (prop:Tprop (tbranch X)) (tr:tree X)
  := fold_subtrees True (fun sub lt rt => prop sub /\ lt /\ rt) tr.
Global Instance every_subtree_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (every_subtree prop tr).
Proof. intro. induction tr; solve_decision. Qed.

Definition exists_subtree {X} (prop:Tprop (tbranch X)) (tr:tree X)
  := fold_subtrees False (fun sub lt rt => prop sub \/ lt \/ rt) tr.
Global Instance exists_subtree_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (exists_subtree prop tr).
Proof. intro. induction tr; solve_decision. Qed.

Definition every_node {X} (prop:Tprop X) (tr:tree X) := fold_nodes True (fun data lt rt => prop data /\ lt /\ rt) tr.
Global Instance every_node_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (every_node prop tr).
Proof. intro. induction tr; solve_decision. Qed.

Definition exists_node {X} (prop:Tprop X) (tr:tree X) := fold_nodes False (fun data lt rt => prop data \/ lt \/ rt) tr.
Global Instance exists_node_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (exists_node prop tr).
Proof. intro. induction tr; solve_decision. Qed.

Definition exists_strict_child {X} (prop:Tprop X)
  : Tprop (tbranch X) := fun '(_, _, child) => exists_node prop child.
Global Instance exists_strict_child_dec {X} prop (tr:tbranch X) :
  (forall u, Decision (prop u)) -> Decision (exists_strict_child prop tr).
Proof. intro. solve_decision. Qed.

Definition empty_children {X} (tr:tbranch X)
  : Prop :=
  let '(_, _, children) := tr in
  children = empty.

Definition insert_child_at {X} (tr:tree X) (ins:X) (search:Tprop X) {search_dec:forall x, Decision (search x)} : tree X :=
  (fix aux tr : tree X :=
    match tr with
    | empty => empty
    | branch data sibling child =>
      let sibling := aux sibling in
      let child := aux child in
      if decide (search data)
      then branch data sibling (branch ins child empty)
      else branch data sibling child
    end
  ) tr.


