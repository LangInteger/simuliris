From simuliris.simulation Require Import lifting.
From simuliris.stacked_borrows Require Import primitive_laws proofmode.
From iris.prelude Require Import options.

(* Assuming p : (&shr i32, T) *)
Definition loop_unopt : ectx :=
  (λ: "p",
    let: "i" := Proj "p" #[0] in
    (* We do not retag "env" as we do not access it.
      For the purpose of this function, it is just "data". *)
    let: "env" := Proj "p" #[1] in

    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (&int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value.
    *)
    retag_place "x" (RefPtr Immutable) int Default #[ScCallId 0];;

    while: Call #[ScFnPtr "f"] (Conc "env" (Copy *{int} "x")) do
      #[42]
    od;;

    (* Free the local variable *)
    Free "x" ;;

    (* finally, return something *)
    #[42])%E
  .


Definition loop_opt : ectx :=
  (λ: "p",
    let: "i" := Proj "p" #[0] in
    let: "env" := Proj "p" #[1] in
    let: "x" := new_place (&int) "i" in
    retag_place "x" (RefPtr Immutable) int Default #[ScCallId 0];;
    let: "r" := Copy *{int} "x" in
    while: Call #[ScFnPtr "f"] (Conc "env" "r") do
      #[42]
    od;;
    Free "x" ;;
    #[42])%E
  .

(*
fn funky_loop(x : &mut i32, f, env) {
  retag x;
  while(f(env, *x)) {

  }
}

fn funky_loop(x : &mut i32, f, env) {
  retag x;
  let v = *x;
  while(f(env, v)) {

  }
}

*)



Lemma loop_opt1 `{sborGS Σ} π :
  ⊢ sim_ectx π loop_opt loop_unopt rrel.
Proof.
  iIntros (r_t r_s) "Hrel".
  sim_pures.

  (* do the projections *)
  source_bind (Proj _ _).
  destruct r_s; (iApply source_red_irred_unless; first done); last by iIntros "?".
  iIntros "(%i & %sc & %Heq & _ & %Hsc)". injection Heq as [= <-].
  destruct v as [ | sc_s0 v]; simpl in *; first done. injection Hsc as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  source_bind (Proj _ _).
  iApply source_red_irred_unless; first done.
  iIntros "(%i & %sc' & %Heq & _ & %Hsc')". injection Heq as [= <-].
  destruct v as [ | sc_s1 v]; simpl in *; first done. injection Hsc' as [= <-].
  source_proj. { simpl. done. }
  source_pures.

  iPoseProof (rrel_value_source with "Hrel") as (v_t) "[-> Hvrel]".
  iPoseProof (value_rel_length with "Hvrel") as "%Hlen".
  destruct v_t as [ | sc_t0 [ | sc_t1 v_t]]; simpl in Hlen; [ lia | lia | ].
  sim_pures.
  target_proj; first done. target_pures. target_proj; first done.
  sim_pures.

  (* create local location for x *)
  sim_apply (Alloc _) (Alloc _) sim_alloc_local "". iIntros (t_x l_x) "Hx Ht_x Hs_x".
  iApply sim_expr_base. sim_pures.

  source_apply (Write _ _) (source_write_local with "Hx Hs_x") "Hs_x Hx";
    [by rewrite replicate_length | done | ].
  target_apply (Write _ _) (target_write_local with "Hx Ht_x") "Ht_x Hx";
    [ by rewrite replicate_length | done | ].
  sim_pures.

  target_apply (Copy _) (target_copy_local with "Hx Ht_x") "Ht_x Hx"; first done.
  source_apply (Copy _) (source_copy_local with "Hx Hs_x") "Hs_x Hx"; first done.

  rewrite /value_rel. rewrite !big_sepL2_cons.
  iDestruct "Hvrel" as "(#Hsc0_rel & #Hsc1_rel & Hvrel)".

  (* do the retag *)
  sim_bind (Retag _ _ _ _ _) (Retag _ _ _ _ _).
  iApply sim_irred_unless; first done.
  iIntros ((_ & ot & i & Heq & _)). injection Heq as [= ->].
  iPoseProof (sc_rel_ptr_source with "Hsc0_rel") as "[-> Htagged]".
  iApply (sim_retag_default with "Hsc0_rel"); [cbn; lia| done | ].
  iIntros (t_i vx_t vx_s Hlen_t Hlen_s) "#Hvx Htag_i Hi_t Hi_s _".
  iApply sim_expr_base.
  target_apply (Write _ _) (target_write_local with "Hx Ht_x") "Ht_x Hx"; [done | done | ].
  source_apply (Write _ _) (source_write_local with "Hx Hs_x") "Hs_x Hx"; [done | done | ].
  sim_pures.

  (* do a deferred read.
     we will initiate coinduction with the deferred assertion and then resolve anew in each iteration.
   *)
  target_apply (Copy (Place _ _ _)) (target_copy_local with "Hx Ht_x") "Ht_x Hx"; first done.
  target_pures. target_bind (Copy _).
  iApply (target_copy_deferred with "Htag_i Hi_t"); first done. iIntros (v_t') "Hdeferred Hi_t Htag_i". target_finish.
  sim_pures.

  (* initiate coinduction *)
  sim_bind (While _ _) (While _ _).
  set (inv := (
    l_x ↦s∗[tk_local]{t_x} [ScPtr i (Tagged t_i)] ∗
    l_x ↦t∗[tk_local]{t_x} [ScPtr i (Tagged t_i)] ∗
    t_x $$ tk_local ∗
    deferred_read vx_t v_t' i t_i ∗
    i ↦s∗[tk_pub]{t_i} vx_s ∗
    i ↦t∗[tk_pub]{t_i} vx_t ∗
    t_i $$ tk_pub)%I).

  iApply (sim_while_while inv with "[$Hi_s $Hx $Hdeferred $Hi_t $Htag_i $Hs_x $Ht_x]").
  iModIntro. iIntros "(Hs & Ht & Htag & #Hdeferred & Hi_s & Hi_t & Htag_i)".

  (* resolve the deferred read in the source *)
  source_apply (Copy (Place _ _ _)) (source_copy_local with "Htag Hs") "Hs Htag"; first done.
  source_pures. source_bind (Copy _).
  iApply (source_copy_resolve_deferred with "Htag_i Hi_s Hdeferred"); [done | done | ].
  iIntros (v_s') "#Hv' Hi_s Htag_i". source_finish.
  sim_pures.

  (* do the call *)
  sim_apply (Call _ _) (Call _ _) (sim_call _ (ValR _) (ValR _)) "".
  { iApply big_sepL2_cons. iSplitR; done. }
  iIntros (r_t r_s) "#Hres".

  (* reduce the case *)
  source_bind (Case _ _).
  destruct r_s; (iApply source_red_irred_unless; first done); last by iIntros "?".
  iIntros "(%i'&  %e_s & -> & %Hi' & %He_s_l)".
  iPoseProof (rrel_value_source with "Hres") as (?) "(-> & Hvi')".
  iPoseProof (value_rel_singleton_source with "Hvi'") as (sci') "(-> & Hsci')".
  iPoseProof (sc_rel_int_source with "Hsci'") as "->".
  iClear "Hres Hvi' Hsci'".

  assert (Z.to_nat i' = 0%nat ∨ Z.to_nat i' = 1%nat) as Hzi'.
  { destruct (Z.to_nat i') as [ | ni]; first by left.
    destruct ni as [ | [ | ni]]; first by right. all: simpl in He_s_l; congruence.
  }
  clear He_s_l.
  assert (i' = 0 ∨ i' = 1) as [-> | ->] by lia.
  - (* exit the loop *)
    source_case. { done. }
    target_case. { done. }
    sim_pures. iApply sim_expr_base. iLeft.
    sim_pures.

    sim_apply (Free _) (Free _) (sim_free_local with "Htag Ht Hs") "Htag"; [done..|]. sim_pures.
    sim_val. iModIntro. iApply big_sepL2_singleton; done.
  - (* another round *)
    source_case. { done. }
    target_case. { done. }
    sim_pures.
    iApply sim_expr_base. iRight. iFrame "Ht Hi_t Hs Htag Hi_s Htag_i Hdeferred".
    done.
Qed.
