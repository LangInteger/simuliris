From simuliris.simplang Require Import lang notation tactics class_instances heap_bij.
From iris Require Import bi.bi.
Import bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.

Section fix_bi.
  Context `{sbijG Σ}.

  Fixpoint val_rel (v_t v_s : val) {struct v_s} :=
    (match v_t, v_s with
    | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
        l_t ↔h l_s
    | LitV l_t, LitV l_s =>
        ⌜l_t = l_s⌝
    | PairV v1_t v2_t, PairV v1_s v2_s =>
        val_rel v1_t v1_s ∧ val_rel v2_t v2_s
    | InjLV v_t, InjLV v_s =>
        val_rel v_t v_s
    | InjRV v_t, InjRV v_s =>
        val_rel v_t v_s
    | _,_ => False
    end)%I.
  Instance : sheapInv Σ := heap_bij_inv val_rel.
  Instance val_rel_pers v_t v_s : Persistent (val_rel v_t v_s).
  Proof.
    induction v_s as [[] | | | ] in v_t |-*; destruct v_t as [ [] | | | ]; apply _.
  Qed.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  Definition loop_test n : expr :=
    let: "n" := Alloc #n in
    While (#0 < ! "n") ("n" <- ! "n" - #1).

  Lemma loop (n : nat) :
    ⊢ loop_test n ⪯ #() {{ val_rel }}.
  Proof.
    rewrite /loop_test.
    target_alloc l as "Hl". sim_pures.
    iInduction n as [ | ] "IH" forall "Hl".
    - target_while. target_load. by sim_pures.
    - target_while. target_load. sim_pures. target_load. target_store. sim_pures.
      assert (Z.sub (Z.of_nat (S n)) (Zpos xH) = Z.of_nat n) as -> by lia.
      by iApply "IH".
  Qed.

  Definition mul_loop e1 e2 : expr :=
    let: "m" := e2 in
    let: "n" := Alloc e1 in
    let: "acc" := Alloc #0 in
    while: #0 < !"n" do "acc" <- !"acc" + "m";; "n" <- !"n" - #1 od ;;
    let: "mv" := !"acc" in
    Free "n";;
    Free "acc";;
    "mv".

  Lemma loop_lem (n0 n m : nat) (l_acc l_n : loc) :
    l_n ↦t #n -∗
    l_acc ↦t #((n0 - n) * m) -∗
    target_red (while: #0 < !#l_n do #l_acc <- !#l_acc + #m;; #l_n <- !#l_n - #1 od)%E
      (λ e_t', ⌜e_t' = #()⌝ ∗ l_n ↦t #0 ∗ l_acc ↦t #(n0 * m)).
  Proof.
    iIntros "Hn Hm". iInduction n as [ | ] "IH" forall "Hn Hm".
    - target_while. sim_pures. target_load. sim_pures.
      assert (n0 - 0%nat = n0)%Z as -> by lia.
      iModIntro. by iFrame.
    - target_while. target_load. sim_pures. target_load.
      target_store. target_load. target_store. sim_pures.
      iApply ("IH" with "[Hn] [Hm]").
      + by assert ((S n) - 1 = n)%Z as -> by lia.
      + by assert ((n0 - S n) * m + m = (n0 - n) * m)%Z as -> by lia.
  Qed.

  Lemma mul_sim (n m : nat) :
    ⊢ mul_loop #n #m ⪯ #n * #m {{ val_rel }}.
  Proof.
    rewrite /mul_loop.
    sim_pures. target_alloc l_n as "Hln". target_alloc l_acc as "Hlacc".
    sim_pures.
    target_bind (While _ _).
    iApply (target_red_wand (λ e_t',⌜e_t' = Val #()⌝ ∗ l_n ↦t #0 ∗ l_acc ↦t #(n * m))%I with "[Hln Hlacc]"). {
      (* generalize over n for the ind, but fix n0 *)
      iApply (loop_lem with "Hln [Hlacc]"). by assert ((n - n) * m = 0)%Z as -> by lia.
    }
    iIntros (e_t') "(-> & Hln & Hlacc)". sim_pures.
    target_load. sim_pures. target_free. target_free.
    by sim_pures.
  Qed.

  Definition diverging_loop : expr :=
    while: #true do #() od.

  Lemma diverge_sim :
    ⊢ diverging_loop ⪯ diverging_loop {{ val_rel }}.
  Proof.
    rewrite /diverging_loop.
    iApply (sim_while_while _ _ _ _ _ True%I); first done.
    iModIntro. sim_pures. iApply sim_expr_base. iRight; done.
  Qed.

  Definition input_loop : expr :=
    let: "cont" := Alloc #true in
    while: !"cont" do
      "cont" <- Call #f "external" #()
    od.

  Lemma val_rel_bool_source v_t b :
    val_rel v_t (LitV $ LitBool b) -∗ ⌜v_t = LitV $ LitBool b⌝.
  Proof.
    destruct v_t as [[] | | | ]; simpl; try iIntros "%Hv"; inversion Hv. done.
  Qed.

  Lemma input_sim :
    ⊢ input_loop ⪯ input_loop {{ val_rel }}.
  Proof.
    rewrite /input_loop. target_alloc lc_t as "Hlc_t". source_alloc lc_s as "Hlc_s".
    sim_pures.
    iApply (sim_bij_insert with "Hlc_t Hlc_s"); first done. iIntros "#Hrel".
    iApply (sim_while_while _ _ _ _ _ (lc_t ↔h lc_s)%I); first done.
    iModIntro.
    sim_load v_t v_s as "Ha".

    to_source.
    iApply source_red_irred_unless; first done.
    iIntros ((b & ->)); iPoseProof (val_rel_bool_source with "Ha") as "->"; sim_pures.
    destruct b; sim_pures.
    - sim_bind (Call _ _) (Call _ _).
      iApply sim_wand; first by iApply sim_call.
      iIntros (v_t v_s) "Hv". sim_store; first done.
      sim_pures. iApply sim_expr_base. iRight. eauto.
    - iApply sim_expr_base. iLeft. iExists #(), #(); eauto.
  Qed.

  Definition input_rec : ectx :=
    λ: "cont",
      if: "cont" then
        let: "cont" := Call #f "external" #() in
        Call #f "rec" "cont"
      else #().

  Lemma loop_rec :
    "rec" @s input_rec -∗
    input_loop ⪯ Call #f"rec" #true {{ val_rel }}.
  Proof.
    iIntros "Hs".
    (* TODO: add a general simulation lemma for this case *)
  Abort.

End fix_bi.
