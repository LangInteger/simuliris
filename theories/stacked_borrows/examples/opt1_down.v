From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import proofmode defs lang heap.
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

Lemma sim_opt1_down `{sborG Σ} π :
  ⊢ sim_ectx rrel π ex1_down_opt ex1_down_unopt rrel.
Proof.
  iIntros (r_t r_s) "Hrel".
  sim_pures.
  sim_apply InitCall InitCall sim_initcall "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.
  sim_apply (Alloc _) (Alloc _) sim_alloc_local "". iIntros (t l_t l_s) "Htag Ht Hs".
  iApply sim_expr_base. sim_pures. simpl.

  source_bind (Write _ _).
  destruct r_s as [v_s | ]; first last.
  { iApply source_red_irred_unless; first done. by iIntros. }
  (* gain knowledge about the length *)
  iApply source_red_irred_unless; first done. iIntros (Hsize). simpl.
  iApply (source_write_local with "Htag Hs"); [ done | done | ].
  iIntros "Hs Htag". source_finish.
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen".
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [ done | lia| ].
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first lia.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first lia.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_irred_unless; first done.
  iIntros ((_ & ot & i & -> & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t) "[-> Hscrel]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[-> Htagged]". 
  iApply (sim_retag_fnentry with "Hscrel Hcall"); [cbn; lia| ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "Hvrel Hcall Htag_i Hi_t Hi_s _".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  (* do the source load *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_apply (Copy _) (source_copy_any with "Htag_i Hi_s") "Hi_s Htag_i"; first done. 
  sim_pures.

  sim_apply (Call _ _) (Call _ _) (sim_call _ _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t r_s) "_". sim_pures.

  (* do the target load *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures. target_apply (Copy _) (target_copy_protected with "Hcall Htag_i Hi_t") "Hi_t Hcall Htag_i"; first done.
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert.  set_solver. } 
  sim_pures. 

  sim_bind (Free _) (Free _).
  (* TODO: need local free lemma that also removes the ghost state for that *)
Abort.


