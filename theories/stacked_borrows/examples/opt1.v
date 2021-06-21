From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import primitive_laws proofmode.
Set Default Proof Using "Type".

(** Moving read of mutable reference up across code not using that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_unopt : ectx :=
  (λ: "i",
    (* get related values i*)
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (&mut int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
    *)
    retag_place "x" (RefPtr Mutable) int Default #[ScCallId 0];;

    (* The unknown code is represented by a call to an unknown function "f" or
      "g". *)
    Call #[ScFnPtr "f"] #[] ;;

    (* Write 42 to the cell pointed to by the pointer in "x" *)
    *{int} "x" <- #[42] ;;

    Call #[ScFnPtr "g"] #[] ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    "v")%E
  .


Definition ex1_opt : ectx :=
  λ: "i",
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int Default #[ScCallId 0];;
    Call #[ScFnPtr "f"] #[] ;;
    *{int} "x" <- #[42] ;;
    let: "v" := #[42] in
    Call #[ScFnPtr "g"] #[] ;;
    Free "x" ;;
    "v".

Lemma sim_new_place_local `{sborGS Σ} T v_t v_s π Φ :
  ⌜length v_t = length v_s⌝ -∗
  (∀ t l,
    ⌜length v_s = tsize T⌝ -∗
    ⌜length v_t = tsize T⌝ -∗
    t $$ tk_local -∗
    l ↦t∗[tk_local]{t} v_t -∗
    l ↦s∗[tk_local]{t} v_s -∗
    PlaceR l (Tagged t) T ⪯{π} PlaceR l (Tagged t) T [{ Φ }]) -∗
  new_place T #v_t ⪯{π} new_place T #v_s [{ Φ }].
Proof.
  iIntros (Hlen_eq) "Hsim".
  rewrite /new_place. sim_bind (Alloc _) (Alloc _).
  iApply sim_alloc_local. iIntros (t l) "Htag Ht Hs". iApply sim_expr_base.
  sim_pures.
  source_bind (Write _ _).
  (* gain knowledge about the length *)
  iApply source_red_irred_unless; first done. iIntros (Hsize).
  iApply (source_write_local with "Htag Hs"); [by rewrite replicate_length | done | ].
  iIntros "Hs Htag". source_finish.

  target_bind (Write _ _).
  iApply (target_write_local with "Htag Ht"); [ by rewrite replicate_length | lia| ].
  iIntros "Ht Htag". target_finish.

  sim_pures. iApply ("Hsim" with "[//] [] Htag Ht Hs").
  iPureIntro; lia.
Qed.

(* TODO: potentially have more modular lemmas for exploiting UB in order use the generic new_place lemma... *)

(*Lemma let_irred1 ϕ P x e1 e2 σ : *)
  (*IrredUnless ϕ P e1 σ →*)
  (*IrredUnless ϕ P (Let x e1 e2) σ.*)
(*Proof.*)
  (*intros He1 Hnirred. *)

(* TODO: maybe have nicer n-step irreducibility thing?
  then we could use the above generic lemma for [new_place].
   currently we don't use it since, in order to apply it, we'd need to use UB that happens during its execution...
*)
Lemma sim_opt1 `{sborGS Σ} π :
  ⊢ sim_ectx π ex1_opt ex1_unopt rrel.
Proof.
  iIntros (r_t r_s) "Hrel".
  sim_pures.
  sim_apply (Alloc _) (Alloc _) sim_alloc_local "". iIntros (t l) "Htag Ht Hs".
  iApply sim_expr_base. sim_pures.

  source_bind (Write _ _).
  destruct r_s as [v_s | ]; first last.
  { iApply source_red_irred_unless; first done. by iIntros. }
  (* gain knowledge about the length *)
  iApply source_red_irred_unless; first done. iIntros (Hsize).
  iApply (source_write_local with "Htag Hs"); [by rewrite replicate_length | done | ].
  iIntros "Hs Htag". source_finish.
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen".
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [ by rewrite replicate_length | lia| ].
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first lia.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first lia.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_irred_unless; first done.
  iIntros ((_ & ot & i & -> & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t) "[-> Hscrel]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[-> Htagged]".
  iApply (sim_retag_default with "Hscrel"); [cbn; lia| done | ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "_ Htag_i Hi_t Hi_s _".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t r_s) "_". sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  sim_pures.

  (* we need to do the writes symmetrically: we cannot know if the tag is still on top *)
  sim_apply (Write _ _) (Write _ _) (sim_write_unique_unprotected with "Htag_i Hi_t Hi_s") "Htag_i Hi_t Hi_s".
  sim_pures.

  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t' r_s') "_". sim_pures.

  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_bind (Copy _).
  iApply (source_copy_any with "Htag_i Hi_s"); first done. iIntros (v_s') "%Hv_s' Hi_s Htag_i". source_finish.
  sim_pures.

  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  sim_val. iModIntro. destruct Hv_s' as [-> | ->]; iApply big_sepL2_singleton; done.
Qed.


(** A variant of this optimization (actually the one from the original formalization)
  which uses deferred UB. *)
Definition ex1_opt' : ectx :=
  λ: "i",
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int Default #[ScCallId 0];;
    Call #[ScFnPtr "f"] #[] ;;
    *{int} "x" <- #[42] ;;
    (* using a read here: requires to use LLVM semantics for reads *)
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "g"] #[] ;;
    Free "x" ;;
    "v".

Lemma sim_opt1' `{sborGS Σ} π :
  ⊢ sim_ectx π ex1_opt' ex1_unopt rrel.
Proof.
  iIntros (r_t r_s) "Hrel".
  sim_pures.
  sim_apply (Alloc _) (Alloc _) sim_alloc_local "". iIntros (t l) "Htag Ht Hs".
  iApply sim_expr_base. sim_pures.

  source_bind (Write _ _).
  destruct r_s as [v_s | ]; first last.
  { iApply source_red_irred_unless; first done. by iIntros. }
  (* gain knowledge about the length *)
  iApply source_red_irred_unless; first done. iIntros (Hsize).
  iApply (source_write_local with "Htag Hs"); [by rewrite replicate_length | done | ].
  iIntros "Hs Htag". source_finish.
  iPoseProof (rrel_value_source with "Hrel") as (v_t) "(-> & #Hv)".
  iPoseProof (value_rel_length with "Hv") as "%Hlen".
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [ by rewrite replicate_length | lia| ].
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first lia.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first lia.

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_irred_unless; first done.
  iIntros ((_ & ot & i & -> & _)).
  iPoseProof (value_rel_singleton_source with "Hv") as (sc_t) "[-> Hscrel]".
  iPoseProof (sc_rel_ptr_source with "Hscrel") as "[-> Htagged]".
  iApply (sim_retag_default with "Hscrel"); [cbn; lia| done | ].
  iIntros (t_i v_t v_s Hlen_t Hlen_s) "_ Htag_i Hi_t Hi_s _".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Htag Ht") "Ht Htag"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Htag Hs") "Hs Htag"; [done | done | ].
  sim_pures.

  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t r_s) "_". sim_pures.

  target_apply (Copy _) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  source_apply (Copy _) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  sim_pures.

  (* we need to do the writes symmetrically: we cannot know if the tag is still on top *)
  sim_apply (Write _ _) (Write _ _) (sim_write_unique_unprotected with "Htag_i Hi_t Hi_s") "Htag_i Hi_t Hi_s".
  sim_pures.

  (* deferred read in the target *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Htag Ht") "Ht Htag"; first done.
  target_pures. target_bind (Copy _).
  iApply (target_copy_deferred with "Htag_i Hi_t"); first done. iIntros (v_t') "Hdeferred Hi_t Htag_i". target_finish.
  sim_pures.

  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR []) (ValR [])) ""; first by iApply value_rel_empty.
  iIntros (r_t' r_s') "_". sim_pures.

  (* resolve the deferred read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_bind (Copy _).
  iApply (source_copy_resolve_deferred with "Htag_i Hi_s Hdeferred"); first done.
  { iApply big_sepL2_singleton. done. }
  iIntros (v_s') "Hv' Hi_s Htag_i". source_finish.
  sim_pures.

  sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
  sim_val. iModIntro. done.
Qed.
