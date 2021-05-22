From simuliris.stacked_borrows Require Import proofmode lang.
Set Default Proof Using "Type".

(** Moving read of mutable reference up across code not using that ref. *)


(* Assuming x : &mut i32 *)
Definition ex1_unopt : ectx :=
  (λ: "i",
    (* get related values i*)

    (* init with same new call id on both sides and obtain knowledge that [c] is active: active(c) *)
    (* c protects { } *)

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (&mut int) "i" in
    (* get a location l and ptr_id pid; (l, Tagged pid) ↦{tk_local} i;
       get authoritative knowledge of stack: l @s@ [mkItem Unique (Tagged pid) None]
    *)

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.  A [Default] retag is
      sufficient for this, we don't need the protector. *)
    retag_place "x" (RefPtr Mutable) int Default #[0];;
    (* obtain (through source UB) knowledge that i = #[ScPtr li ti], get  li_t ↔h li
        (l, Tagged pid) ↦{tk_local} ScPtr li ti' for new tag ti'; 
        get (li, ti') ↦{tk_mut} v0

    *)

    (* The unknown code is represented by a call to an unknown function "f" or
      "g". *)
    Call #[ScFnPtr "f"] #[] ;;

    (* Write 42 to the cell pointed to by the pointer in "x" *)
    *{int} "x" <- #[42] ;;
    (* just use the permissions we have *)

    Call #[ScFnPtr "g"] #[] ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    "v")%E
  .


Definition ex1_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int Default ;;
    Call #[ScFnPtr "f"] [] ;;
    (* *x : l, t *)
    *{int} "x" <- #[42] ;;    (* stack for *x: mkItem Unique t None :: ... *)

    (* TODO: for now, until we change read semantics, directly have 42 without a read *)
    let: "v" := #[42] in
    (*let: "v" := Copy *{int} "x" in [> stack for *x : mkItem Unique t None :: .... ?<]*)

    (* Question: 
        why do we retain knowledge about x here? Note: we are reading asymmetrically from the bijection here.
        Because: otherwise, we will reach UB in the source at a later point (in > 1 steps).
        Reasoning: do a case analysis on the shape of the target stack for li.
        If this is not what we need, use the bijection to transfer this knowledge to the source stack,
        then claim that we can reach source stuckness after the call. 
        But reaching source stuckness after the call seems really complicated!


        Does this get easier when we set a protector?
        Yes. 
    *)


    Call #[ScFnPtr "g"] [] ;;
    Free "x" ;;
    "v"


(* Where do protectors help me?

        c protects { ti' ↦ { li } }       means: there's an item in the stack which is protected by c 

   protectors help when: 
    * we can use source UB to find out that there's nothing un-poppable above the protector
    * we can otherwise maintain that the protected item can be used rn for accesses: if access mode is Unique or Shared, then we can use knowledge of the protector to gain knowledge of the full stack!
          (this is an invariant that needs to be held up by other threads, and thus makes this reasoning possible locally!)
*)
