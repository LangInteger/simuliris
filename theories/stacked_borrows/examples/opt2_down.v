From simuliris.stacked_borrows Require Import proofmode lang.
Set Default Proof Using "Type".

(** Moving a read of a shared reference down across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition ex2_down_unopt : ectx :=
  λ: "i",
    let: "c" := InitCall in
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (& int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. This relies on protectors,
      hence [FnEntry]. *)
    retag_place "x" (RefPtr Immutable) int FnEntry "c";;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] (Copy "x") ;;

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    EndCall "c";;
    "v"
  .

Definition ex2_down_opt : ectx :=
  λ: "i",
    let: "c" := InitCall in
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int FnEntry "c";;
    Call #[ScFnPtr "f"] (Copy "x") ;;
    let: "v" := Copy *{int} "x" in
    (* need to make sure that we are reading the same value! -- so take the same strategy of keeping a fraction outside.
      to be able to use that fraction, need to use the protector.
    *)
    Free "x" ;;
    EndCall "c";;
    "v"
  .


