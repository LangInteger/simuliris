From simuliris.stacked_borrows Require Import proofmode lang.
Set Default Proof Using "Type".

(** Moving read of shared ref up across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition ex2_unopt : ectx :=
  λ: "i",
    let: "c" := InitCall in
    (* c protects { } *)

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (& int) "i" in
    (* (x, Tagged pid_x) ↦{tk_local} i *)

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. A [Default] retag is
      sufficient for this, we don't need the protector. *)
    retag_place "x" (RefPtr Immutable) int Default "c";;
    (* (x, Tagged pid_x) ↦{tk_local} ScPtr l t 
       (l, Tagged npid) ↦{tk_shr} v
    *)

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] (Copy "x") ;;
    (* need to insert x into the bijection for the call.
        point: for this to work, we need to retain some knowledge about the value even beyond the bijection.
        i.e.: retain a fractional points-to!

        (l, Tagged npid) ↦{q, tk_shr} v
    *)

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    EndCall "c";;
    "v"
  .

Definition ex2_opt : ectx :=
  λ: "i",
    let: "c" := InitCall in
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int Default "c";;
    let: "v" := Copy *{int} "x" in
    (* NOTE: here we have the same problem as in opt1.v: we need to know that the stack has not changed. 
        moreover: might need to keep track of the type/type size somewhere?*)
    Call #[ScFnPtr "f"] (Copy "x") ;;
    Free "x" ;;
    EndCall "c";;
    "v"
  .


(* NOTE regarding allocation size: just weaken that to say that it either has a size or has been deallocated.
  Then we should be able to make that token persistent. 
  (we can rule out the "deallocated" case with a pointsto, if needed) 
*)


