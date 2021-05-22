From simuliris.stacked_borrows Require Import proofmode lang.
Set Default Proof Using "Type".

(** Moving a read of a mutable reference down across code that *may* use that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_down_unopt : ectx :=
  λ: "i",
    let: "c" := InitCall in 
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (&mut int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. This relies on protectors,
      hence [FnEntry]. *)
    retag_place "x" (RefPtr Mutable) int FnEntry "c";;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* The unknown code is represented by a call to an unknown function "f" *)
    Call #[ScFnPtr "f"] #[] ;;

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    EndCall "c";;
    "v"
  .

Definition ex1_down_opt : ectx :=
  λ: "i",
    let: "c" := InitCall in 
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry "c";;
    Call #[ScFnPtr "f"] #[] ;;
    let: "v" := Copy *{int} "x" in
    (* crucial point: need to know that we retain the permission to read *)

    Free "x" ;;
    EndCall "c";;
    "v"
  .


