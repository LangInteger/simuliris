From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From simuliris.base_logic Require Export gen_sim_heap gen_sim_prog.
From simuliris.simulation Require Import slsls lifting.
From iris.algebra.lib Require Import gset_bij.
From iris.base_logic.lib Require Import gset_bij.
From simuliris.simplang Require Export class_instances primitive_laws proofmode.

From iris.prelude Require Import options.

(** * Instance of the SimpLang program logic that provides a means of establishing bijections on the heap. *)

Class sbijG (Σ : gFunctors) := SBijG {
  sbijG_sheapG :> sheapG Σ;
  sbijG_bijG :> gset_bijG Σ block block;
  sbijG_bij_name : gname;
}.

Section definitions.
  Context `{sbijG Σ}.

  Definition heap_bij_auth (L : gset (block * block)) :=
    gset_bij_own_auth sbijG_bij_name (DfracOwn 1) L.
  Definition heap_bij_elem (l_t : block) (l_s : block) :=
    gset_bij_own_elem sbijG_bij_name l_t l_s.

  Definition heap_bij_inv (val_rel : val → val → iProp Σ) :=
    (∃ L, heap_bij_auth L ∗
      [∗ set] p ∈ L, 
        let '(b_t, b_s) := p in 
        ∃ (n : nat),
        Build_loc b_t 0 ==>t n ∗ Build_loc b_s 0 ==>s n ∗ 
        ([∗ list] i ∈ seq 0 n, ∃ v_t v_s, (Build_loc b_t (Z.of_nat i)) ↦t v_t ∗ (Build_loc b_s (Z.of_nat i)) ↦s v_s ∗ val_rel v_t v_s))%I. 
End definitions.

Notation "b_t '↔h' b_s" := (heap_bij_elem b_t b_s) (at level 30) : bi_scope.

Section laws.
  Context `{sbijG Σ}.

  Global Instance gen_heap_bij_elem_persistent l_t l_s :
    Persistent (l_t ↔h l_s).
  Proof. apply _. Qed.

  Lemma gen_heap_bij_agree l_t1 l_t2 l_s1 l_s2 :
    l_t1 ↔h l_s1 -∗ l_t2 ↔h l_s2 -∗ ⌜l_t1 = l_t2 ↔ l_s1 = l_s2⌝.
  Proof.
    iIntros "H1 H2". iApply (gset_bij_own_elem_agree with "H1 H2").
    apply gset_empty.
  Qed.
  Lemma gen_heap_bij_func l_t l_s1 l_s2 :
    l_t ↔h l_s1 -∗ l_t ↔h l_s2 -∗ ⌜l_s1 = l_s2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (gen_heap_bij_agree with "H1 H2") as "<-"; done.
  Qed.
  Lemma gen_heap_bij_inj l_s l_t1 l_t2 :
    l_t1 ↔h l_s -∗ l_t2 ↔h l_s -∗ ⌜l_t1 = l_t2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (gen_heap_bij_agree with "H1 H2") as "->"; done.
  Qed.

  Lemma gen_heap_bij_access val_rel l_t l_s :
    gen_heap_bij_inv val_rel -∗
    l_t ↔h l_s -∗
    ∃ v_t v_s, l_t ↦t v_t ∗ l_s ↦s v_s ∗ val_rel v_t v_s ∗
      (∀ v_t' v_s', l_t ↦t v_t' -∗
        l_s ↦s v_s' -∗
        val_rel v_t' v_s' -∗
        gen_heap_bij_inv val_rel).
  Proof.
    iIntros "Hinv Hrel". iDestruct "Hinv" as (L) "[Hauth Hheap]".
    iPoseProof (gset_bij_own_elem_auth_agree with "Hauth Hrel") as "%".
    iPoseProof (big_sepS_delete with "Hheap") as "[He Hheap]"; first done.
    iDestruct "He" as (v_t v_s) "(H_t & H_s & Hvrel)".
    iExists v_t, v_s. iFrame.
    iIntros (v_t' v_s') "H_t H_s Hvrel".
    iExists L. iFrame. iApply big_sepS_delete; first done.
    iFrame. iExists v_t', v_s'. iFrame.
  Qed.

  Lemma gen_heap_bij_insert val_rel l_t l_s v_t v_s :
    gen_heap_bij_inv val_rel -∗
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s ==∗
    gen_heap_bij_inv val_rel ∗ l_t ↔h l_s.
  Proof.
    iIntros "Hinv Ht Hs Hrel". iDestruct "Hinv" as (L) "[Hauth Hheap]".
    iAssert ((¬ ⌜set_Exists (λ '(l_t', l_s'), l_t = l_t') L⌝)%I) as "%Hext_t".
    { iIntros "%". destruct H3 as ([l_t' l_s'] & Hin & <-).
      iPoseProof (big_sepS_elem_of with "Hheap") as (v_t' v_s') "(Hcon & _ & _)"; first by apply Hin.
      iPoseProof (mapsto_valid_2  with "Ht Hcon") as "%Hcon"; exfalso.
      destruct Hcon as [Hcon _]. by apply dfrac_valid_own_r in Hcon.
    }
    iAssert ((¬ ⌜set_Exists (λ '(l_t', l_s'), l_s = l_s') L⌝)%I) as "%Hext_s".
    { iIntros (([l_t' l_s'] & Hin & <-)).
      iPoseProof (big_sepS_elem_of with "Hheap") as (v_t' v_s') "(_ & Hcon & _)"; first by apply Hin.
      iPoseProof (mapsto_valid_2 with "Hs Hcon") as "%Hcon"; exfalso.
      destruct Hcon as [Hcon _]. by apply dfrac_valid_own_r in Hcon.
    }

    iMod ((gset_bij_own_extend l_t l_s) with "Hauth") as "[Hinv #Helem]".
    - intros l_s' Hl_s'. apply Hext_t. by exists (l_t, l_s').
    - intros l_t' Hl_t'. apply Hext_s. by exists (l_t', l_s).
    - iModIntro. iSplitL; last done.
      iExists ({[(l_t, l_s)]} ∪ L)%I. iFrame.
      iApply big_sepS_insert. { contradict Hext_t. by exists (l_t, l_s). }
      iFrame. iExists v_t, v_s. iFrame.
  Qed.

End laws.



Section bij.

End bij.

Section fix_heap.
  Context `{sbijG Σ} (val_rel : val → val → iProp Σ).
  Context {val_rel_pers : ∀ v_t v_s, Persistent (val_rel v_t v_s)}.

  Definition oval_rel ov_t ov_s : iProp Σ :=
    (∃ v_t v_s, ⌜ov_t = Some v_t⌝ ∗ ⌜ov_s = Some v_s⌝ ∗ val_rel v_t v_s) ∨
    (⌜ov_t = None⌝ ∗ ⌜ov_s = None⌝).
  Instance heap_bij_inv : sheapInv Σ := {|
    sheap_inv := gen_heap_bij_inv oval_rel;
  |}.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.
  Local Notation "et '⪯' es [{ Φ }]" := (et ⪯{val_rel} es [{Φ}])%I (at level 40, Φ at level 200) : bi_scope.

  Lemma stuck_reach_stuck P (e : expr) σ:
    stuck P e σ → reach_stuck P e σ.
  Proof. intros Hs; exists e, σ. done. Qed.

  Lemma sim_bij_load l_t l_s Φ :
    l_t ↔h l_s -∗
    (∀ v_t v_s, val_rel v_t v_s -∗ Val v_t ⪯ Val v_s [{ Φ }]) -∗
    (Load (Val $ LitV $ LitLoc l_t)) ⪯ (Load (Val $ LitV $ LitLoc l_s)) [{ Φ }].
  Proof using val_rel_pers.
    iIntros "#Hbij Hsim". iApply sim_lift_head_step_both.
    iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) %Hnstuck]".
    iPoseProof (gen_heap_bij_access with "Hinv Hbij") as (v_t' v_s') "(Hl_t & Hl_s & He & Hclose)".
    iDestruct (gen_heap_valid with "Hσ_t Hl_t") as %?.
    iDestruct (gen_heap_valid with "Hσ_s Hl_s") as %?.
    iDestruct "He" as "[He | [-> ->]]".
    - iDestruct "He" as (v_t v_s) "(-> & -> & #Hv)".
      iModIntro; iSplit; first by eauto with head_step.
      iIntros (e_t' σ_t') "%"; inv_head_step.
      assert (head_step P_s (Load #l_s) σ_s (Val v_s) σ_s) as Hs.
      { eauto with head_step. }
      iModIntro. iExists (Val v_s), σ_s. iFrame.
      iSplitR. { by iPureIntro. }
      iSplitR "Hsim"; first last. { by iApply "Hsim". }
      iApply ("Hclose" with "Hl_t Hl_s []"). iLeft; eauto.
    - exfalso; contradict Hnstuck.
      apply stuck_reach_stuck. split; first done.
      apply sirreducible. source_stuck_sidecond_bt.
  Qed.

  Lemma sim_bij_store l_t l_s v_t v_s Φ :
    l_t ↔h l_s -∗
    val_rel v_t v_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Store (Val $ LitV (LitLoc l_t)) (Val v_t) ⪯ Store (Val $ LitV (LitLoc l_s)) (Val v_s) [{ Φ }].
  Proof.
    iIntros "Hbij Hval Hsim". iApply sim_lift_head_step_both.
    iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) %Hnstuck] !>".
    iPoseProof (gen_heap_bij_access with "Hinv Hbij") as (v_t'' v_s'') "(Hl_t & Hl_s & He & Hclose)".
    iDestruct (gen_heap_valid with "Hσ_t Hl_t") as %?.
    iDestruct (gen_heap_valid with "Hσ_s Hl_s") as %?.
    iDestruct "He" as "[He | [-> ->]]".
    - iDestruct "He" as (v_t' v_s') "(-> & -> & Hval')".
      iSplitR; first by eauto with head_step.
      iIntros (e_t' σ_t') "%"; inv_head_step.
      assert (head_step P_s (#l_s <- v_s) σ_s #() (state_upd_heap <[l_s:=Some v_s]> σ_s)) as Hs.
      { eauto with head_step. }

      iMod (gen_heap_update with "Hσ_t Hl_t") as "[$ Hl_t]".
      iMod (gen_heap_update with "Hσ_s Hl_s") as "[Ha Hl_s]".
      iModIntro. iExists #(),(state_upd_heap <[l_s:=Some v_s]> σ_s).
      iFrame. iSplitR; first by iPureIntro.
      iApply ("Hclose" with "Hl_t Hl_s [Hval]"). iLeft; eauto.
    - exfalso; contradict Hnstuck.
      apply stuck_reach_stuck. split; first done.
      apply sirreducible. source_stuck_sidecond_bt.
  Qed.

  Lemma sim_bij_free l_t l_s Φ :
    l_t ↔h l_s -∗
    #() ⪯ #() [{ Φ }] -∗
    Free (Val $ LitV $ LitLoc l_t) ⪯ Free (Val $ LitV $ LitLoc l_s) [{ Φ }].
  Proof.
    iIntros "Hbij Hsim". iApply sim_lift_head_step_both.
    iIntros (????) "[(HP_t & HP_s & Hσ_t & Hσ_s & Hinv) %Hnstuck]".
    iPoseProof (gen_heap_bij_access with "Hinv Hbij") as (v_t'' v_s'') "(Hl_t & Hl_s & He & Hclose)".
    iDestruct (gen_heap_valid with "Hσ_t Hl_t") as %?.
    iDestruct (gen_heap_valid with "Hσ_s Hl_s") as %?.
    iDestruct "He" as "[He | [-> ->]]".
    - iDestruct "He" as (v_t' v_s') "(-> & -> & Hval')".
      iSplitR; first by eauto with head_step. iModIntro.
      iIntros (e_t' σ_t') "%"; inv_head_step.
      assert (head_step P_s (Free #l_s) σ_s #() (state_upd_heap <[l_s:=None]> σ_s)) as Hs.
      { eauto with head_step. }

      iMod (gen_heap_update with "Hσ_t Hl_t") as "[$ Hl_t]".
      iMod (gen_heap_update with "Hσ_s Hl_s") as "[Ha Hl_s]".
      iModIntro. iExists #(),(state_upd_heap <[l_s:=None]> σ_s).
      iFrame. iSplitR; first by iPureIntro.
      iApply ("Hclose" with "Hl_t Hl_s"). iRight; eauto.
    - exfalso; contradict Hnstuck.
      apply stuck_reach_stuck. split; first done.
      apply sirreducible. source_stuck_sidecond_bt.
  Qed.

  Lemma sim_bij_insert l_t l_s v_t v_s e_t e_s Φ :
    l_t ↦t v_t -∗
    l_s ↦s v_s -∗
    val_rel v_t v_s -∗
    (l_t ↔h l_s -∗ e_t ⪯ e_s [{ Φ }]) -∗
    e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hl_t Hl_s Hval Hsim". iApply sim_update_si.
    iIntros (????) "(HP_t & HP_s & Hσ_t & Hσ_s & Hinv)".
    iMod (gen_heap_bij_insert with "Hinv Hl_t Hl_s [Hval]") as "[Hb #Ha]";
      first by iLeft; eauto.
    iModIntro. iSplitR "Hsim"; last by iApply "Hsim".
    iFrame.
  Qed.
End fix_heap.

(** ** Default value relation *)
Section val_rel.
  Context `{sbijG Σ}.
  Fixpoint val_rel (v_t v_s : val) {struct v_s} : iProp Σ :=
    match v_t, v_s with
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
    end.
  Global Instance : sheapInv Σ := heap_bij_inv val_rel.
  Global Instance val_rel_pers v_t v_s : Persistent (val_rel v_t v_s).
  Proof.
    induction v_s as [[] | | | ] in v_t |-*; destruct v_t as [ [] | | | ]; apply _.
  Qed.

  Lemma val_rel_pair_source v_t v_s1 v_s2 :
    val_rel v_t (v_s1, v_s2) -∗
    ∃ v_t1 v_t2, ⌜v_t = PairV v_t1 v_t2⌝ ∗
      val_rel v_t1 v_s1 ∗
      val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_t as [[] | v_t1 v_t2 | |]; simpl; try done.
    iExists v_t1, v_t2. iDestruct "H" as "[#H1 #H2]". eauto.
  Qed.
  Lemma val_rel_injl_source v_t v_s :
    val_rel v_t (InjLV v_s) -∗ ∃ v_t', ⌜v_t = InjLV v_t'⌝ ∗ val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma val_rel_injr_source v_t v_s :
    val_rel v_t (InjRV v_s) -∗ ∃ v_t', ⌜v_t = InjRV v_t'⌝ ∗ val_rel v_t' v_s.
  Proof. simpl. destruct v_t as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.


  Lemma val_rel_litfn_source v_t fn_s :
    val_rel v_t (LitV $ LitFn $ fn_s) -∗ ⌜v_t = LitV $ LitFn $ fn_s⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litint_source v_t n :
    val_rel v_t (LitV $ LitInt n) -∗ ⌜v_t = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litbool_source v_t b:
    val_rel v_t (LitV $ LitBool b) -∗ ⌜v_t = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litunit_source v_t :
    val_rel v_t (LitV $ LitUnit) -∗ ⌜v_t = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litpoison_source v_t :
    val_rel v_t (LitV $ LitPoison) -∗ ⌜v_t = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_t as [[] | v_t1 v_t2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_loc_source v_t l_s :
    val_rel v_t (LitV $ LitLoc l_s) -∗
    ∃ l_t, ⌜v_t = LitV $ LitLoc l_t⌝ ∗ l_t ↔h l_s.
  Proof.
    destruct v_t as [[ | | | | l_t | ] | | | ]; simpl;
        first [iIntros "%Ht"; congruence | iIntros "#Ht"; eauto].
  Qed.

  Lemma val_rel_pair_target v_s v_t1 v_t2 :
    val_rel (v_t1, v_t2) v_s -∗
    ∃ v_s1 v_s2, ⌜v_s = PairV v_s1 v_s2⌝ ∗
      val_rel v_t1 v_s1 ∗
      val_rel v_t2 v_s2.
  Proof.
    simpl. iIntros "H". destruct v_s as [[] | v_s1 v_s2 | |]; simpl; try done.
    iExists v_s1, v_s2. iDestruct "H" as "[#H1 #H2]". eauto.
  Qed.
  Lemma val_rel_injl_target v_t v_s :
    val_rel (InjLV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjLV v_s'⌝ ∗ val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma val_rel_injr_target v_t v_s :
    val_rel (InjRV v_t) v_s -∗ ∃ v_s', ⌜v_s = InjRV v_s'⌝ ∗ val_rel v_t v_s'.
  Proof. simpl. destruct v_s as [[] | | |]; (try by iIntros "%Hp"); eauto. Qed.
  Lemma val_rel_litfn_target v_s fn_t :
    val_rel (LitV $ LitFn $ fn_t) v_s -∗ ⌜v_s = LitV $ LitFn $ fn_t⌝.
  Proof. simpl. destruct v_s as [[] | v_s1 v_s2 | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litint_target v_s n :
    val_rel (LitV $ LitInt n) v_s -∗ ⌜v_s = LitV $ LitInt $ n⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litbool_target v_s b:
    val_rel (LitV $ LitBool b) v_s -∗ ⌜v_s = LitV $ LitBool b⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litunit_target v_s :
    val_rel (LitV $ LitUnit) v_s -∗ ⌜v_s = LitV $ LitUnit⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_litpoison_target v_s :
    val_rel (LitV $ LitPoison) v_s -∗ ⌜v_s = LitV $ LitPoison⌝.
  Proof. simpl. destruct v_s as [[] | | |]; iIntros "%Hp"; inversion Hp; subst; done. Qed.
  Lemma val_rel_loc_target v_s l_t :
    val_rel (LitV $ LitLoc l_t) v_s -∗
    ∃ l_s, ⌜v_s = LitV $ LitLoc l_s⌝ ∗ l_t ↔h l_s.
  Proof.
    destruct v_s as [[ | | | | l_s | ] | | | ]; simpl;
        first [iIntros "%Hs"; congruence | iIntros "#Hs"; eauto].
  Qed.
End val_rel.
Tactic Notation "val_discr_source" constr(H) :=
  first [iPoseProof (val_rel_litint_source with H) as "->" |
         iPoseProof (val_rel_litbool_source with H) as "->" |
         iPoseProof (val_rel_litfn_source with H) as "->" |
         iPoseProof (val_rel_litunit_source with H) as "->" |
         iPoseProof (val_rel_litpoison_source with H) as "->" |
         idtac].
Tactic Notation "val_discr_target" constr(H) :=
  first [iPoseProof (val_rel_litint_target with H) as "->" |
         iPoseProof (val_rel_litbool_target with H) as "->" |
         iPoseProof (val_rel_litfn_target with H) as "->" |
         iPoseProof (val_rel_litunit_target with H) as "->" |
         iPoseProof (val_rel_litpoison_target with H) as "->" |
         idtac].

Lemma val_rel_func `{sbijG Σ} v1 v2 v3 : val_rel v1 v2 -∗ val_rel v1 v3 -∗ ⌜v2 = v3⌝.
Proof.
  iIntros "Hv1 Hv2". iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); val_discr_source "Hv1"; val_discr_target "Hv2"; try done.
  - iPoseProof (val_rel_loc_source with "Hv1") as (?) "(-> & Hl1)".
    iPoseProof (val_rel_loc_target with "Hv2") as (?) "(-> & Hl2)".
    by iPoseProof (gen_heap_bij_func with "Hl1 Hl2") as "->".
  - iPoseProof (val_rel_pair_source with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
    iPoseProof (val_rel_pair_target with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
    iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
    by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
  - iPoseProof (val_rel_injl_source with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injl_target with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  - iPoseProof (val_rel_injr_source with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injr_target with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
Qed.
Lemma val_rel_inj `{sbijG Σ} v1 v2 v3 : val_rel v2 v1 -∗ val_rel v3 v1 -∗ ⌜v2 = v3⌝.
Proof.
  iIntros "Hv1 Hv2". iInduction v2 as [[n2 | b2 | | | l2 | f2 ] | v2_1 v2_2 | v2 | v2] "IH" forall (v1 v3); val_discr_target "Hv1"; val_discr_source "Hv2"; try done.
  - iPoseProof (val_rel_loc_target with "Hv1") as (?) "(-> & Hl1)".
    iPoseProof (val_rel_loc_source with "Hv2") as (?) "(-> & Hl2)".
    by iPoseProof (gen_heap_bij_inj with "Hl1 Hl2") as "->".
  - iPoseProof (val_rel_pair_target with "Hv1") as (??) "(-> & Hv1_1 & Hv1_2)".
    iPoseProof (val_rel_pair_source with "Hv2") as (??) "(-> & Hv2_1 & Hv2_2)".
    iPoseProof ("IH" with "Hv1_1 Hv2_1") as "->".
    by iPoseProof ("IH1" with "Hv1_2 Hv2_2") as "->".
  - iPoseProof (val_rel_injl_target with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injl_source with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
  - iPoseProof (val_rel_injr_target with "Hv1") as (?) "(-> & Hv1)".
    iPoseProof (val_rel_injr_source with "Hv2") as (?) "(-> & Hv2)".
    by iPoseProof ("IH" with "Hv1 Hv2") as "->".
Qed.
Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

(** ** Extension of the proofmode *)
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.bi Require Import bi.
Import bi.
From iris.bi Require Import derived_laws.
Import bi.
From simuliris.simplang Require Export proofmode.


(** New lemmas for the new tactics *)
Section sim.
  Context `{sbijG Σ} (val_rel : val → val → iProp Σ).
  Context {val_rel_pers : ∀ v_t v_s, Persistent (val_rel v_t v_s)}.
  Instance : sheapInv Σ := heap_bij_inv val_rel.

  Local Notation "et '⪯' es {{ Φ }}" := (et ⪯{val_rel} es {{Φ}})%I (at level 40, Φ at level 200) : bi_scope.

  Implicit Types
    (K_t K_s : ectx)
    (l_t l_s : loc)
    (v_t v_s : val)
    (e_t e_s : expr).

  Instance maybe_persistent b (P : iProp Σ) : Persistent P → Persistent (□?b P).
  Proof.
    intros Hp. destruct b; simpl; last by eauto.
    rewrite /Persistent. iIntros "#H"; eauto.
  Qed.

  Lemma tac_bij_load Δ i j b K_t K_s l_t l_s Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    (∀ v_t v_s,
      match envs_app true (Esnoc Enil j (val_rel v_t v_s)) Δ with
      | Some Δ' =>
          envs_entails Δ' (sim_expr val_rel (fill K_t (Val v_t)) (fill K_s (Val v_s)) Φ)
      | None => False
      end) →
    envs_entails Δ (sim_expr val_rel (fill K_t (Load (LitV l_t))) (fill K_s (Load (LitV l_s))) Φ)%I.
  Proof using val_rel_pers.
    rewrite envs_entails_eq=> ? Hi.
    rewrite -sim_expr_bind. eapply wand_apply; first exact: sim_bij_load.
    rewrite envs_lookup_split //; simpl.
    iIntros "[#Ha He]". iSpecialize ("He" with "Ha").
    rewrite intuitionistically_if_elim. iSplitR; first done.
    iIntros (v_t' v_s') "#Hv". specialize (Hi v_t' v_s').
    destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction].
    iApply sim_expr_base.
    iApply Hi. rewrite envs_app_sound //; simpl. iApply "He"; eauto.
  Qed.

  Lemma tac_bij_store Δ i K_t K_s b l_t l_s v_t' v_s' Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails Δ (val_rel v_t' v_s') →
    envs_entails Δ (sim_expr val_rel (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit)) Φ) →
    envs_entails Δ (sim_expr val_rel (fill K_t (Store (LitV l_t) (Val v_t'))) (fill K_s (Store (LitV l_s) (Val v_s'))) Φ).
  Proof using val_rel_pers.
    rewrite envs_entails_eq => HΔ.
    rewrite (persistent_persistently_2 (val_rel _ _)).
    intros Hv%persistently_entails_r Hi.
    rewrite -sim_expr_bind.
    iIntros "He". iPoseProof (Hv with "He") as "[He #Hv]".
    rewrite (envs_lookup_split Δ i b _ HΔ). iDestruct "He" as "[#Hbij He]".
    iSpecialize ("He" with "Hbij").
    iApply sim_bij_store; [ | done | ]. { by rewrite intuitionistically_if_elim. }
    iApply sim_expr_base. by iApply Hi.
  Qed.

  (* NOTE: we may want to actually keep the bijection assertion in context for some examples,
    where we need to use source stuckness for some runs of the target that access a deallocated location?
    In that case, change this lemma to not remove the fractional bijection assertion from the context.
    *)
  Lemma tac_bij_free Δ i K_t K_s b l_t l_s Φ :
    envs_lookup i Δ = Some (b, l_t ↔h l_s)%I →
    envs_entails (envs_delete true i b Δ) (sim_expr val_rel (fill K_t (Val $ LitV LitUnit)) (fill K_s (Val $ LitV LitUnit)) Φ) →
    envs_entails Δ (sim_expr val_rel (fill K_t (Free (LitV l_t))) (fill K_s (Free (LitV l_s))) Φ).
  Proof.
    rewrite envs_entails_eq => Hl HΔ.
    rewrite -sim_expr_bind. rewrite (envs_lookup_sound _ _ _ _ Hl).
    iIntros "[#bij He]". iPoseProof (HΔ with "He") as "He". rewrite intuitionistically_if_elim.
    iApply sim_bij_free; first done.
    iApply sim_expr_base. by iApply "He".
  Qed.
End sim.

Tactic Notation "sim_load" ident(v_t) ident(v_s) "as" constr(H) :=
  to_sim;
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
      iAssumptionCore || fail "sim_load: cannot find" l_t "↔h" l_s
    end in
  let finish _ :=
    first [intros v_t v_s | fail 1 "sim_load: " v_t " or " v_s " not fresh"];
    pm_reduce; sim_finish in
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?vrel ?e_t ?e_s ?Φ) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_load _ _ _ H _ K_t K_s _ _ _)))
      |fail 1 "sim_load: cannot find 'Load' in" e_t " or " e_s];
    [ solve_bij ()
    | finish () ]
  | _ => fail "sim_load: not a 'sim'"
  end.
Tactic Notation "sim_load" ident(v_t) ident(v_s) :=
  sim_load v_t v_s as "?".

Tactic Notation "sim_store" :=
  to_sim;
  let Htmp := iFresh in
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
    iAssumptionCore || fail "sim_store: cannot find" l_t "↔h" l_s end in
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?vrel ?e_t ?e_s ?Φ) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_store _ _ _ K_t K_s _ _ _ _ _)))
      |fail 1 "sim_store: cannot find 'Store' in" e_t " or " e_s];
    [solve_bij ()
    | pm_reduce
    |pm_reduce; sim_finish]
  | _ => fail "sim_store: not a 'sim'"
  end.

Tactic Notation "sim_free" :=
  to_sim;
  let solve_bij _ :=
    match goal with |- _ = Some (_, (?l_t ↔h ?l_s)%I) =>
    iAssumptionCore || fail "sim_free: cannot find" l_t "↔h" l_s end in
  sim_pures_int;
  lazymatch goal with
  | |- envs_entails _ (sim_expr ?vrel ?e_t ?e_s ?Φ) =>
    first
      [reshape_expr e_t ltac:(fun K_t e_t' =>
        reshape_expr e_s ltac:(fun K_s e_s' =>
          eapply (tac_bij_free _ _ _ K_t K_s _ _ _ _)))
      |fail 1 "sim_free: cannot find 'Free' in" e_t " or " e_s];
    [solve_bij ()
    |pm_reduce; sim_finish]
  | _ => fail "sim_free: not a 'sim'"
  end.
