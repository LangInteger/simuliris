From simuliris.stacked_borrows Require Import proofmode lang.
Set Default Proof Using "Type".

(** Moving a write to a mutable reference up across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3_unopt : ectx :=
  λ: "i",
    let: "c" := InitCall in
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (&mut int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. This relies on protectors,
      hence [FnEntry]. *)
    retag_place "x" (RefPtr Mutable) int FnEntry "c";;

    (* Write 42 to the cell pointed to by the pointer in "x" *)
    *{int} "x" <- #[42] ;;
    (* Challenge here: the bijection is running out of sync! 
        Point: the entry in the bijection should effectively be disabled, due to the unique tag + protector.

        the stack shape assertion is in the bijection. Point: it doesn't necessarily grant access. 
       (remember, the pointsto assertions are conditional -- the bijection does not contain the knowledge needed to use that; that has to be kept externally).
    *)

    (* The unknown code is represented by a call to an unknown function "f" *)
    let: "v" := Call #[ScFnPtr "f"] #[] in

    (* Write 13 to the cell pointed to by the pointer in "x" *)
    *{int} "x" <- #[13] ;;

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the value *)
    EndCall "c";;
    "v"
  .

Definition ex3_opt : ectx :=
  λ: "i",
    let: "c" := InitCall in
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry "c";;
    *{int} "x" <- #[13] ;;
    let: "v" := Call #[ScFnPtr "f"] #[] in
    Free "x" ;;
    EndCall "c";;
    "v"
  .

