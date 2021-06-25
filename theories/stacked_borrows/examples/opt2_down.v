From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import proofmode lang.
From iris.prelude Require Import options.


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

Lemma sim_opt2_down `{sborGS Σ} π :
  ⊢ sim_ectx π ex2_down_opt ex2_down_unopt rrel.
Proof.
  iIntros (r_t r_s) "Hrel".
  sim_pures.
  sim_apply InitCall InitCall sim_init_call "". iIntros (c) "Hcall". iApply sim_expr_base. sim_pures.
  sim_apply (Alloc _) (Alloc _) sim_alloc_local "". iIntros (t l) "Htag Ht Hs".
  iApply sim_expr_base. sim_pures. simpl.

  source_bind (Write _ _). simpl.
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
  iApply (sim_retag_fnentry with "Hscrel Hcall"); [cbn; lia| done | ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "#Hvrel Hcall Htag_i Hi_t Hi_s #Hsc_i".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  (* do the source load *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_bind (Copy _).
  iApply (source_copy_any with "Htag_i Hi_s"); first done. iIntros (v_s' Hv_s') "Hi_s Htag_i". source_finish.
  sim_pures.

  (* do the call *)
  sim_pures. target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first done. sim_pures.
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR [ScPtr i _]) (ValR [ScPtr i _])) "".
  { iApply big_sepL2_singleton. iApply "Hsc_i". }
  iIntros (r_t r_s) "_". sim_pures.

  (* do the target load *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures. target_apply (Copy _) (target_copy_protected with "Hcall Htag_i Hi_t") "Hi_t Hcall Htag_i"; first done.
  { simpl. intros i0 Hi0. assert (i0 = O) as -> by lia. eexists. split; first apply lookup_insert.  set_solver. }
  sim_pures.

  (* cleanup: remove the protector ghost state, make the external locations public, free the local locations*)
  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  iApply (sim_protected_unprotectN with "Hcall Htag_i Hi_t Hi_s Hvrel"); [ | apply lookup_insert | ].
  { simpl. cbn in Hlen_t. intros i' Hi'. replace i' with O by lia. rewrite elem_of_union elem_of_singleton. eauto. }
  iIntros "Hcall Htag_i Hi_t Hi_s".
  iApply (sim_remove_empty_calls t_i with "Hcall").
  { rewrite lookup_insert. done. }
  { rewrite Hlen_t. set_solver. }
  iIntros "Hcall".
  sim_apply (EndCall _) (EndCall _) (sim_endcall_own with "[Hcall]") "".
  { replace (delete t_i _) with (∅ : gmap ptr_id (gset loc)); first done.
    apply map_eq. intros t'. rewrite delete_insert_delete delete_insert; done.
  }
  sim_pures.
  sim_val. iModIntro. destruct Hv_s' as [-> | ->]; first done.
  iApply big_sepL2_forall. iSplit. { rewrite replicate_length. iPureIntro. lia. }
  iIntros (k sc_t sc_s). rewrite lookup_replicate. iIntros "Hsc (-> & _)". destruct sc_t;done.
Qed.
