From simuliris.simplang Require Import lang notation tactics class_instances proofmode gen_log_rel parallel_subst wf.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simplang.na_inv Require Export inv.
From simuliris.simplang.na_inv Require Import refl.

Section remove_alloc.
  Context `{naGS Σ}.


  Definition remove_alloc_opt (e1 e2 e3 : expr) : expr :=
    e1;;
    let: "r" := e2 in
    e3;;
    "r".

  Definition remove_alloc (e1 e2 e3 : expr) : expr :=
    let: "x" := ref #0 in
    e1;;
    "x" <- e2;;
    e3;;
    let: "r" := !"x" in
    Free "x";;
    "r".

  Lemma remove_alloc_sim e1 e2 e3:
    free_vars e1 ⊆ list_to_set ["n"] →
    free_vars e2 ⊆ list_to_set ["n"] →
    free_vars e3 ⊆ list_to_set ["n"] →
    gen_expr_wf expr_head_wf e1 →
    gen_expr_wf expr_head_wf e2 →
    gen_expr_wf expr_head_wf e3 →
    ⊢ log_rel (remove_alloc_opt e1 e2 e3) (remove_alloc e1 e2 e3).
  Proof.
    move => He1 He2 He3 ???. log_rel.
    iIntros "%n_t %n_s #Hn !# %π Hc".
    source_alloc x as "Hmx" "Hfx". sim_pures.

    sim_bind (subst_map _ _) (subst_map _ _).
    iApply (sim_refl with "[] [Hc]");
      [compute_done | etrans; [eassumption|compute_done]
       | apply: na_log_rel_structural | done | | iFrame |]. {
        rewrite !dom_insert_L. iApply big_sepS_intro. iIntros "!#" (y Hin).
        rewrite map_lookup_zip_with.
        destruct (decide (y = "n")); [|exfalso; set_solver]; by simplify_map_eq.
    }
    iIntros (??) "Hc _". iApply lift_post_val. sim_pures.

    sim_bind (subst_map _ _) (subst_map _ _).
    iApply (sim_refl with "[] [Hc]");
      [compute_done | etrans; [eassumption|compute_done]
       | apply: na_log_rel_structural | done | | iFrame |]. {
        rewrite !dom_insert_L. iApply big_sepS_intro. iIntros "!#" (y Hin).
        rewrite map_lookup_zip_with.
        destruct (decide (y = "n")); [|exfalso; set_solver]; by simplify_map_eq.
    }
    iIntros (??) "Hc Hv". iApply lift_post_val. sim_pures.
    source_store. sim_pures.

    sim_bind (subst_map _ _) (subst_map _ _).
    iApply (sim_refl with "[] [Hc]");
      [compute_done | etrans; [eassumption|compute_done]
       | apply: na_log_rel_structural | done | | iFrame |]. {
        rewrite !dom_insert_L. iApply big_sepS_intro. iIntros "!#" (y Hin).
        rewrite map_lookup_zip_with.
        destruct (decide (y = "n")); [|exfalso; set_solver]; by simplify_map_eq.
    }
    iIntros (??) "Hc _". iApply lift_post_val. sim_pures.
    source_load. source_free. sim_pures. sim_val. by iFrame.
  Qed.
End remove_alloc.
