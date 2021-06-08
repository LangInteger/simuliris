From simuliris.simulation Require Import lifting.
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
      then updates "x" with the new pointer value.
      Using a protector here.
    *)
    retag_place "x" (RefPtr Immutable) int FnEntry "c";;

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] (Copy "x") ;;

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
    retag_place "x" (RefPtr Immutable) int FnEntry "c";;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] (Copy "x") ;;
    Free "x" ;;
    EndCall "c";;
    "v"
  .

Lemma sim_opt2 `{sborG Σ} π :
  ⊢ sim_ectx rrel π ex2_opt ex2_unopt rrel.
Proof.
  iIntros (r_t r_s) "Hrel".
  sim_pures.
  sim_apply InitCall InitCall (sim_init_call) "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.

  sim_apply (Alloc _) (Alloc _) sim_alloc_local "". iIntros (t l_t l_s) "Htag Ht Hs".
  iApply sim_expr_base. sim_pures.

  source_bind (Write _ _).
  destruct r_s as [v_s | ]; first last.
  { iApply source_red_irred_unless; first done. by iIntros. }
  (* gain knowledge about the length *)
  iApply source_red_irred_unless; first done. iIntros (Hsize).
  iApply (source_write_local with "Htag Hs"); [by rewrite repeat_length | done | ].
  iIntros "Hs Htag". source_finish.
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen".
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [ by rewrite repeat_length | lia| ].
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first lia.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first lia.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_irred_unless; first done.
  iIntros ((_ & ot & i & -> & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t) "[-> Hscrel]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[-> Htagged]".
  iApply (sim_retag_fnentry with "Hscrel Hcall"); [cbn; lia|  ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "Hvrel Hcall Htag_i Hi_t Hi_s #Hsc_i".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  (* read in the target *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures. target_apply (Copy _) (target_copy_protected with "Hcall Htag_i Hi_t") "Hi_t Hcall Htag_i"; [done | | ].
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert. set_solver. }

  sim_pures. target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first done. sim_pures.
  sim_apply (Call _ _) (Call _ _) (sim_call _ _ (ValR [ScPtr i _]) (ValR [ScPtr i _])) "".
  { iApply big_sepL2_singleton. iApply "Hsc_i". }
  iIntros (r_t r_s) "_". sim_pures.

  (* read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_apply (Copy _) (source_copy_any with "Htag_i Hi_s") "Hi_s Htag_i"; first done.
  sim_pures.

  sim_bind (Free _) (Free _).
  (* TODO: need local free lemma that also removes the ghost state for that *)
Abort.




(* TODO: use LLVM read semantics for the following optimization *)
(* Assuming x : & i32 *)
Definition ex2_unopt' : ectx :=
  λ: "i",
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (& int) "i" in
    (* (x, Tagged pid_x) ↦{tk_local} i *)

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. A [Default] retag is
      sufficient for this, we don't need the protector. *)
    retag_place "x" (RefPtr Immutable) int Default #[ScCallId 0];;

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] (Copy "x") ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    EndCall "c";;
    "v"
  .

Definition ex2_opt' : ectx :=
  λ: "i",
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int Default #[ScCallId 0];;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] (Copy "x") ;;
    Free "x" ;;
    "v"
  .
