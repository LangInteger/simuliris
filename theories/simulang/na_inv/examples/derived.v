From iris Require Import bi.bi.
From iris.proofmode Require Import tactics.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior.
From simuliris.simulang.na_inv Require Export inv.
From simuliris.simulang.na_inv Require Import readonly_refl adequacy.
From iris.prelude Require Import options.

(** * Derived stuff we show in the paper *)

Section derived.
  Context `{naGS Σ}.

  Lemma safe_reach_if e1 e2 v : safe_reach (∃ b, v = LitV $ LitBool b) (If (Val v) e1 e2).
  Proof. apply safe_reach_irred. apply _. Qed.
  Lemma safe_reach_div v1 v2 : safe_reach ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n ∧ n ≠ 0%Z))%V (BinOp QuotOp (Val v1) (Val v2)).
  Proof. apply safe_reach_irred. apply _. Qed.
  Lemma safe_reach_load o v_l : safe_reach (∃ l, v_l = LitV $ LitLoc l) (Load o $ Val v_l).
  Proof. apply safe_reach_irred. apply _. Qed.


  Implicit Types
    (P : iProp Σ) (Φ : expr → expr → iProp Σ) (Ψ : expr → iProp Σ)
    (e_t e_s : expr)
    (v_t v_s : val)
    (π : thread_id).

  Definition hoareSim P e_t e_s π Φ : iProp Σ := □ (P -∗ sim_expr Φ π e_t e_s).
  Definition hoareTgt P e_t Ψ : iProp Σ := □ (P -∗ target_red e_t Ψ).
  Definition hoareSrc P e_s π Ψ : iProp Σ := □ (P -∗ source_red e_s π Ψ).



  Notation "'{{{'  P  '}}}'  e_t  ⪯[  π  ] e_s   '{{{'  Φ  '}}}'" := (hoareSim P e_t e_s π Φ) (at level 10) : bi_scope.
  Notation "'[{{'  P  '}}]'  e_t  '[{{'  Ψ  '}}]t'" := (hoareTgt P e_t Ψ) (at level 20) : bi_scope.
  Notation "'[{{'  P  '}}]'  e_s  @  π  '[{{'  Ψ  '}}]s'" := (hoareSrc P e_s π Ψ) (at level 20) : bi_scope.

  Lemma sim_bind P e_t e_s K_t K_s π Φ Φ' :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ' }}}) →
    (∀ e_t' e_s', ⊢ {{{ Φ' e_t' e_s' }}} fill K_t e_t' ⪯[π] fill K_s e_s' {{{ Φ }}}) →
    ⊢ {{{ P }}} fill K_t e_t ⪯[π] fill K_s e_s {{{ Φ }}}.
  Proof.
    intros He HK. iModIntro. iIntros "HP". iPoseProof (He with "HP") as "Hs".
    iApply sim_expr_bind. iApply (sim_expr_wand with "Hs []").
    iIntros (e_t' e_s') "Hp". by iApply HK.
  Qed.

  Lemma sim_frame P e_t e_s π Φ R :
    (⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P ∗ R }}} e_t ⪯[π] e_s {{{ λ e_t' e_s', Φ e_t' e_s' ∗ R }}}.
  Proof.
    iIntros (Hs) "!> [HP HR]".
    iPoseProof (Hs with "HP") as "Hs".
    iApply (sim_expr_wand with "Hs [HR]"). eauto with iFrame.
  Qed.

  Lemma sim_base P e_t e_s π Φ :
    (⊢ P -∗ Φ e_t e_s) → ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hp) "!> HP". iApply sim_expr_base. by iApply Hp.
  Qed.

  Lemma sim_mono P Q e_t e_s π Φ Φ' :
    (⊢ P -∗ Q) →
    (∀ e_t e_s, ⊢ Φ' e_t e_s -∗ Φ e_t e_s) →
    (⊢ {{{ Q }}} e_t ⪯[π] e_s {{{ Φ' }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hpre Hpost Hs) "!>P".
    iApply (sim_expr_wand with "[P] []").
    - iApply Hs. by iApply Hpre.
    - iIntros (??) "Ha". by iApply Hpost.
  Qed.

  Lemma sim_src_safe P Q e_t e_s π Φ :
    safe_reach Q e_s →
    (⊢ {{{ P ∗ ⌜Q⌝ }}} e_t ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hsafe Hs) "!> P". iApply sim_irred_safe_reach; first done.
    iIntros "HQ". iApply Hs. iFrame.
  Qed.

  Lemma sim_paco I e_t e_s e_t' e_s' π Φ :
    PureExec True 1 e_t e_t' →
    PureExec True 1 e_s e_s' →
    (⊢ {{{ I }}} e_t' ⪯[π] e_s' {{{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ (⌜e_t'' = e_t⌝ ∗ ⌜e_s'' = e_s⌝ ∗ I)}}}) →
    ⊢ {{{ I }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hpt Hps Hs) "!> HI". iApply (sim_lift_coind_pure with "[] HI"); [ done | done | ].
    iModIntro. iIntros "HI". by iApply Hs.
  Qed.

  Lemma sim_while I c_t c_s b_t b_s π Φ :
    let w_t := (while: c_t do b_t od)%E in
    let w_s := (while: c_s do b_s od)%E in
    (⊢ {{{ I }}} if: c_t then b_t;; w_t else #() ⪯[π] if: c_s then b_s;; w_s else #()
        {{{ λ e_t'' e_s'', Φ e_t'' e_s'' ∨ (⌜e_t'' = w_t⌝ ∗ ⌜e_s'' = w_s⌝ ∗ I)}}}) →
    ⊢ {{{ I }}} w_t ⪯[π] w_s {{{ Φ }}}.
  Proof.
    intros w_t w_s Hs. iApply sim_paco; [ apply pure_while.. | apply Hs].
  Qed.

  Lemma sim_while_simple I c_t c_s b_t b_s π Q Φ :
    (⊢ {{{ I }}} c_t ⪯[π] c_s {{{ lift_post (λ v_t v_s, (∃ b : bool, ⌜v_s = #b⌝) →
          (⌜v_s = #true⌝ ∗ ⌜v_t = #true⌝ ∗ I) ∨ (⌜v_s = #false⌝ ∗ ⌜v_t = #false⌝ ∗ Q))}}}) →
    (⊢ {{{ I }}} b_t ⪯[π] b_s {{{ lift_post (λ _ _, I) }}}) →
    ⊢ {{{ I }}} while: c_t do b_t od ⪯[π] while: c_s do b_s od {{{ lift_post (λ _ _, Q) }}}.
  Proof.
    iIntros (Hc Hb). iApply sim_while. iIntros "!>HI".
    sim_bind c_t c_s. iApply (sim_wand with "[HI] []"). { by iApply Hc. }
    iIntros (v_t v_s) "Hc".
    iApply sim_irred_unless. iIntros "(%b & ->)".
    iDestruct ("Hc" with "[]") as "[(% & -> & HI) | (% & -> & HQ)]"; first by eauto.
    - simplify_eq. sim_pures.
      sim_bind b_t b_s. iApply (sim_wand with "[HI] []"). { by iApply Hb. }
      iIntros (? ?) "HI". sim_pures. iApply sim_expr_base. eauto with iFrame.
    - simplify_eq. sim_pures. iApply sim_expr_base. iLeft. iApply lift_post_val. done.
  Qed.


  (** Source triples *)
  Lemma source_sim P e_t e_s π Ψ Φ :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s) →
    (∀ e_s', ⊢ {{{ Ψ e_s' }}} e_t ⪯[π] e_s' {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Hsrc Hs) "!> HP". to_source.
    iApply (source_red_wand with "[HP] []"). { by iApply Hsrc. }
    iIntros (e_s') "Hpre". by iApply Hs.
  Qed.

  Lemma source_base P e_s π Ψ :
    (⊢ P -∗ Ψ e_s) →
    ⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s.
  Proof.
    iIntros (Hs) "!>HP". iApply source_red_base. iModIntro. by iApply Hs.
  Qed.

  Lemma source_bind P K_s e_s π Ψ Ψ' :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ' }}]s) →
    (∀ e_s', ⊢ [{{ Ψ' e_s' }}] fill K_s e_s' @ π [{{ Ψ }}]s) →
    ⊢ [{{ P }}] fill K_s e_s @ π [{{ Ψ }}]s.
  Proof.
    iIntros (He HK) "!> HP". iApply source_red_bind.
    iApply (source_red_wand with "[HP] []"). { by iApply He. }
    iIntros (e_s') "Hpre". by iApply HK.
  Qed.

  Lemma source_frame P R e_s π Ψ :
    (⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s) →
    ⊢ [{{ P ∗ R }}] e_s @ π [{{ λ e_s', Ψ e_s' ∗ R }}]s.
  Proof.
    iIntros (Hs) "!> [HP HR]". iApply (source_red_wand with "[HP] [HR]"). { by iApply Hs. }
    eauto with iFrame.
  Qed.

  Lemma source_pure P e_s e_s' n π Ψ :
    PureExec True n e_s e_s' →
    (⊢ [{{ P }}] e_s' @ π [{{ Ψ }}]s) →
    ⊢ [{{ P }}] e_s @ π [{{ Ψ }}]s.
  Proof.
    iIntros (Hpure Hs) "!> HP". iApply source_red_lift_pure; first done.
    by iApply Hs.
  Qed.

  (** Target triples *)
  Lemma target_sim P e_t e_s π Ψ Φ :
    (⊢ [{{ P }}] e_t [{{ Ψ }}]t) →
    (∀ e_t', ⊢ {{{ Ψ e_t' }}} e_t' ⪯[π] e_s {{{ Φ }}}) →
    ⊢ {{{ P }}} e_t ⪯[π] e_s {{{ Φ }}}.
  Proof.
    iIntros (Htgt Hs) "!> HP". to_target.
    iApply (target_red_wand with "[HP] []"). { by iApply Htgt. }
    iIntros (e_t') "Hpre". by iApply Hs.
  Qed.

  Lemma target_base P e_t Ψ :
    (⊢ P -∗ Ψ e_t) →
    ⊢ [{{ P }}] e_t [{{ Ψ }}]t.
  Proof.
    iIntros (Hs) "!>HP". iApply target_red_base. iModIntro. by iApply Hs.
  Qed.

  Lemma target_bind P K_t e_t π Ψ Ψ' :
    (⊢ [{{ P }}] e_t [{{ Ψ' }}]t) →
    (∀ e_t', ⊢ [{{ Ψ' e_t' }}] fill K_t e_t' [{{ Ψ }}]t) →
    ⊢ [{{ P }}] fill K_t e_t [{{ Ψ }}]t.
  Proof.
    iIntros (He HK) "!> HP". iApply target_red_bind.
    iApply (target_red_wand with "[HP] []"). { by iApply He. }
    iIntros (e_t') "Hpre". by iApply HK.
  Qed.

  Lemma target_frame P R e_t π Ψ :
    (⊢ [{{ P }}] e_t [{{ Ψ }}]t) →
    ⊢ [{{ P ∗ R }}] e_t [{{ λ e_t', Ψ e_t' ∗ R }}]t.
  Proof.
    iIntros (Hs) "!> [HP HR]". iApply (target_red_wand with "[HP] [HR]"). { by iApply Hs. }
    eauto with iFrame.
  Qed.

  Lemma target_pure P e_t e_t' n π Ψ :
    PureExec True n e_t e_t' →
    (⊢ [{{ P }}] e_t' [{{ Ψ }}]t) →
    ⊢ [{{ P }}] e_t [{{ Ψ }}]t.
  Proof.
    iIntros (Hpure Hs) "!> HP". iApply target_red_lift_pure; first done.
    by iApply Hs.
  Qed.

End derived.
