(* Derived from lambda-rust heap.v*)
From Coq Require Import Min.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export tactics.
From simuliris.simplang Require Export lang.
Set Default Proof Using "Type".
Import uPred.

Definition lock_stateR : cmra :=
  csumR (exclR unitO) natR.

Definition heapUR : ucmra :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (agreeR valO)).

Class heapGS Σ := HeapGS {
  heap_inG :> inG Σ (authR heapUR);
  heap_freeable_inG :> ghost_mapG Σ loc (option nat);
}.

Record heap_names := {
 heap_name : gname;
 heap_freeable_name : gname;
}.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.
Definition to_heap : gmap loc (lock_state * val) → heapUR :=
  fmap (λ v, (1%Qp, to_lock_stateR (v.1), to_agree (v.2))).
Definition heap_freeable_rel (σ : gmap loc (lock_state * val)) (bs : gset block) (hF : gmap loc (option nat)) : Prop :=
  ∀ l o, hF !! l = Some o →
   loc_chunk l ∈ bs ∧
   loc_idx l = 0 ∧
   0 < default 1 o ∧
   ∀ i, is_Some (σ !! (l +ₗ i)) ↔ (0 ≤ i < default O o)%Z.

Section definitions.
  Context `{!heapGS Σ} (γ : heap_names).

  Definition heap_mapsto_def (l : loc) (st : lock_state) (q : frac) (v: val) : iProp Σ :=
    own γ.(heap_name) (◯ {[ l := (q, to_lock_stateR st, to_agree v) ]}).
  Definition heap_mapsto_aux : seal (@heap_mapsto_def). by eexists. Qed.
  Definition heap_mapsto := unseal heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    seal_eq heap_mapsto_aux.

  Definition heap_mapsto_vec (l : loc) (q : frac) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, heap_mapsto (l +ₗ i) (RSt 0) q v)%I.

  Definition heap_mapsto_vec_st (l : loc) (sts : list lock_state) (q : frac) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ st; v ∈ sts; vl, heap_mapsto (l +ₗ i) st q v)%I.

  Definition heap_freeable_def (l : loc) (q : Qp) (n: option nat) : iProp Σ :=
    ⌜loc_idx l = 0⌝ ∗ l ↪[ γ.(heap_freeable_name) ]{# q } n.
  Definition heap_freeable_aux : seal (@heap_freeable_def). by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    seal_eq heap_freeable_aux.

  Definition heap_ctx (σ: gmap loc (lock_state * val)) (bs : gset block) : iProp Σ :=
    (∃ hF, own γ.(heap_name) (● to_heap σ)
         ∗ ghost_map_auth γ.(heap_freeable_name) 1 hF
         ∗ ⌜heap_freeable_rel σ bs hF⌝
         ∗ ⌜heap_wf σ bs⌝)%I.
End definitions.

Typeclasses Opaque heap_mapsto heap_freeable heap_mapsto_vec.
Instance: Params (@heap_mapsto) 4 := {}.
Instance: Params (@heap_freeable) 5 := {}.

(* Notation "l ↦{ q } v" := (heap_mapsto l q v) *)
(*   (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope. *)
(* Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : bi_scope. *)
(* Notation "l ↦∗{ q } vl" := (heap_mapsto_vec l q vl) *)
(*   (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope. *)
(* Notation "l ↦∗ vl" := (heap_mapsto_vec l 1 vl) (at level 20) : bi_scope. *)



(* Notation "†{ q } l … n" := (heap_freeable l q n) *)
  (* (at level 20, q at level 50, format "†{ q } l … n") : bi_scope. *)
(* Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope. *)

Section to_heap.
  Implicit Types σ : gmap loc (lock_state * val).

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. case (σ !! l)=> [[[|n] v]|] //=. Qed.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.

  Lemma to_heap_insert σ l x v :
    to_heap (<[l:=(x, v)]> σ)
    = <[l:=(1%Qp, to_lock_stateR x, to_agree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma to_heap_delete σ l : to_heap (delete l σ) = delete l (to_heap σ).
  Proof. by rewrite /to_heap fmap_delete. Qed.
End to_heap.

Section heap.
  Context `{!heapGS Σ} (γ : heap_names).
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : gmap loc (lock_state * val).
  Implicit Types E : coPset.

  Local Notation "l ↦[ st ]{ q } v" := (heap_mapsto γ l st q v)
     (at level 20, q at level 50, format "l  ↦[ st ]{ q }  v") : bi_scope.
  Local Notation "l ↦[ st ] v" := (heap_mapsto γ l st 1 v) (at level 20) : bi_scope.
  Local Notation "l ↦{ q } v" := (heap_mapsto γ l (RSt 0) q v)
     (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
  Local Notation "l ↦ v" := (heap_mapsto γ l (RSt 0) 1 v) (at level 20) : bi_scope.
  Local Notation "l ↦∗[ st ]{ q } vl" := (heap_mapsto_vec_st γ l st q vl)
      (at level 20, q at level 50, format "l  ↦∗[ st ]{ q }  vl") : bi_scope.
  Local Notation "l ↦∗[ st ] vl" := (heap_mapsto_vec_st γ l st 1 vl) (at level 20) : bi_scope.
  Local Notation "l ↦∗{ q } vl" := (heap_mapsto_vec γ l q vl)
      (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
  Local Notation "l ↦∗ vl" := (heap_mapsto_vec γ l 1 vl) (at level 20) : bi_scope.

  Local Notation "†{ q } l …? n" := (heap_freeable γ l q n)
  (at level 20, q at level 50, format "†{ q } l …? n") : bi_scope.
  Local Notation "† l …? n" := (heap_freeable γ l 1 n) (at level 20) : bi_scope.

  (** General properties of mapsto and freeable *)
  Global Instance heap_mapsto_timeless l st q v : Timeless (l↦[st]{q}v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Lemma heap_mapsto_split l n q n1 q1 n2 q2 v:
    n = n1 + n2 → q = (q1 + q2)%Qp →
    l ↦[RSt n]{q} v ⊣⊢ l ↦[RSt n1]{q1} v ∗ l ↦[RSt n2]{q2} v.
  Proof.
    intros -> ->.
    rewrite heap_mapsto_eq -own_op -auth_frag_op singleton_op -!pair_op agree_idemp /= //.
  Qed.

  Lemma heap_mapsto_combine_0 l q1 q2 v st:
    l ↦{q1} v -∗ l ↦[st]{q2} v -∗
    l ↦[st]{q1 + q2} v.
  Proof.
    apply: wand_intro_r.
    rewrite heap_mapsto_eq -own_op -auth_frag_op singleton_op -!pair_op agree_idemp /= //.
    destruct st; [|done]. etrans; [apply: own_valid|].
    by iIntros ([[??]%pair_valid?]%auth_frag_valid_1%singleton_valid%pair_valid).
  Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof. intros p q. by apply heap_mapsto_split. Qed.
  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.


  Global Instance heap_mapsto_vec_timeless l st q vl : Timeless (l ↦∗[st]{q} vl).
  Proof. rewrite /heap_mapsto_vec. apply _. Qed.

  Global Instance heap_mapsto_vec_fractional l vl: Fractional (λ q, l ↦∗{q} vl)%I.
  Proof.
    intros p q. rewrite /heap_mapsto_vec -big_sepL_sep.
    by setoid_rewrite (fractional (Φ := λ q, _ ↦{q} _)%I).
  Qed.
  Global Instance heap_mapsto_vec_as_fractional l q vl:
    AsFractional (l ↦∗{q} vl) (λ q, l ↦∗{q} vl)%I q.
  Proof. split. done. apply _. Qed.

  Global Instance heap_freeable_timeless q b n : Timeless (heap_freeable γ b q n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 st1 st2 : l ↦[st1]{q1} v1 ∗ l ↦[st2]{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]. move => /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid => -[? /to_agree_op_inv_L->]; eauto.
  Qed.

  Lemma heap_mapsto_valid l q v st : l ↦[st]{q} v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    rewrite heap_mapsto_eq. etrans; [apply: own_valid|]. iPureIntro.
    by rewrite auth_frag_valid singleton_valid !pair_valid => -[[??]?].
  Qed.

  Lemma heap_mapsto_ne l1 l2 q v1 v2 : l1 ↦ v1 -∗ l2 ↦{q} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof.
    destruct (decide (l1 = l2)); [subst |by eauto].
    iIntros "Hl1 Hl2".
    iDestruct (heap_mapsto_agree with "[$Hl1 $Hl2]") as %->.
    iCombine "Hl1" "Hl2" as "Hl".
    by iDestruct (heap_mapsto_valid with "Hl") as %?%Qp_not_add_le_l.
  Qed.

  Lemma heap_mapsto_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /heap_mapsto_vec. Qed.

  Lemma heap_mapsto_vec_app l q vl1 vl2 :
    l ↦∗{q} (vl1 ++ vl2) ⊣⊢ l ↦∗{q} vl1 ∗ (l +ₗ length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /heap_mapsto_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite loc_add_assoc Nat2Z.inj_add.
  Qed.

  Lemma heap_mapsto_vec_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
  Proof. by rewrite /heap_mapsto_vec /= loc_add_0 right_id. Qed.

  Lemma heap_mapsto_vec_cons l q v vl:
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vl.
  Proof.
    by rewrite (heap_mapsto_vec_app l q [v] vl) heap_mapsto_vec_singleton.
  Qed.

  Lemma heap_mapsto_vec_op l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{q1} vl1 ∗ l ↦∗{q2} vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗{q1+q2} vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !heap_mapsto_vec_nil. iIntros "_"; auto. }
      rewrite !heap_mapsto_vec_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (l +ₗ 1) with "[$Hvl1 $Hvl2]") as "[% $]"; subst.
      rewrite (inj_iff (.:: vl2)).
      iDestruct (heap_mapsto_agree with "[$Hv1 $Hv2]") as %<-.
      iSplit; first done. iFrame.
    - by iIntros "[% [$ Hl2]]"; subst.
  Qed.

  Lemma heap_mapsto_vec_st_length l q vl sts:
    l ↦∗[sts]{q} vl -∗ ⌜length sts = length vl⌝.
  Proof. apply big_sepL2_length. Qed.

  Lemma heap_mapsto_vec_to_st l q vl :
    l ↦∗{q} vl ⊣⊢ l ↦∗[replicate (length vl) (RSt 0)]{q} vl.
  Proof.
    rewrite /heap_mapsto_vec /heap_mapsto_vec_st.
    by rewrite big_sepL2_replicate_l.
  Qed.

  Lemma heap_mapsto_vec_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ vl,
      {[l +ₗ i := (q, Cinr 0%nat, to_agree v)]}).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def=>?.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
  Qed.

  Lemma heap_mapsto_vec_st_combine l q vl sts:
    vl ≠ [] →
    length sts = length vl →
    l ↦∗[sts]{q} vl ⊣⊢ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ zip sts vl,
      {[l +ₗ i := (q, to_lock_stateR v.1, to_agree v.2)]}).
  Proof.
    rewrite /heap_mapsto_vec_st heap_mapsto_eq /heap_mapsto_def=>??.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
    2: { by destruct vl, sts; simplify_eq/=. }
    rewrite big_sepL2_alt.
    assert (⌜length sts = length vl⌝ ⊣⊢@{iPropI Σ} True)%I as -> by (iPureIntro; naive_solver).
    by rewrite left_id.
  Qed.

  Lemma heap_freeable_idx l n :
    †l…?n -∗ ⌜loc_idx l = 0⌝.
  Proof. rewrite heap_freeable_eq. iIntros "[$ _]". Qed.

  Lemma heap_freeable_excl l l' n n' :
    loc_chunk l = loc_chunk l' →
    †l…?n -∗ †l'…?n' -∗ False.
  Proof.
    rewrite heap_freeable_eq.
    iIntros (?) "[% Hl1] [% Hl2]". destruct l, l'; simplify_eq/=.
    by iDestruct (ghost_map_elem_valid_2 with "Hl1 Hl2") as %[? ?].
  Qed.

  Lemma heap_freeable_rel_stable σ bs h l p :
    heap_freeable_rel σ bs h → is_Some (σ !! l) →
    heap_freeable_rel (<[l := p]>σ) bs h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? [? [? REL']]]; first done.
    split_and!; [done..|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = blk +ₗ i)); naive_solver.
  Qed.

  Lemma heap_freeable_rel_init_mem l h n σ bs v:
    n ≠ O →
    loc_idx l = 0 →
    loc_chunk l ∉ bs →
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_freeable_rel σ bs h →
    heap_freeable_rel (heap_array l (replicate n v) ∪ σ) ({[loc_chunk l]} ∪ bs)
                      (<[l := Some n]> h).
  Proof.
    move => ?? Hnotin Hnone Hrel l' o /lookup_insert_Some[[??]|[? Hl]]; simplify_eq/=.
    - split_and!; [set_solver|done|lia|] => i.
      split.
      + move => [?].
        rewrite lookup_union_Some ?Hnone.
        2: { apply heap_array_map_disjoint. naive_solver lia. }
        rewrite heap_array_lookup => -[[?[?[?[?[?]]]]]|//]. simplify_eq.
        rewrite lookup_replicate. lia.
      + move => ?.
        eexists _.
        rewrite lookup_union_Some ?Hnone.
        2: { apply heap_array_map_disjoint. naive_solver lia. }
        left. apply heap_array_lookup. eexists i, _.
        split_and!; [lia|done |done |].
        rewrite lookup_replicate. naive_solver lia.
    - have [?[?[? Hi]]]:= Hrel _ _ Hl.
      split_and!; [set_solver|done|lia|] => i.
      have <-:= Hi i. f_equiv.
      apply option_eq => ?.
      rewrite lookup_union_Some.
      2: { apply heap_array_map_disjoint. naive_solver lia. }
      rewrite heap_array_lookup.
      split; [|naive_solver].
      move => [[?[?[?[??]]]]|//].
      contradict Hnotin.
      have ->: loc_chunk l = loc_chunk l' by destruct l, l'; naive_solver.
      done.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l bs:
    loc_idx l = 0 →
    hF !! l = Some (Some n) →
    heap_freeable_rel σ bs hF →
    heap_freeable_rel (free_mem l n σ) bs (<[l:=None]> hF).
  Proof.
    intros ? Hl REL b qs Hlookup.
    destruct (REL l (Some n)) as [? [? [? REL']]]; auto.
    move: Hlookup => /lookup_insert_Some [[??]|[NEQ ?]]; simplify_eq.
    - split_and!; [done| done| simpl; lia |] => i /=. split; [|lia] => -[?].
      have : free_mem b n σ !! (b +ₗ i) = None; last naive_solver.
      destruct (decide (0 ≤ i < n))%Z.
      + apply lookup_free_mem_2; [done|]. simpl. lia.
      + destruct (decide (i < 0))%Z.
        * rewrite lookup_free_mem_3 => /=; [|done|lia].
          apply eq_None_not_Some. naive_solver lia.
        * rewrite lookup_free_mem_4 => /=; [|done|lia].
          apply eq_None_not_Some. naive_solver lia.
    - destruct (REL b qs) as [? [? [? REL'']]]; auto.
      split_and!; [done..|]=> i. rewrite -REL'' lookup_free_mem_1 //=.
      destruct b, l; simplify_eq/=. congruence.
  Qed.

  Lemma heap_freeable_inj n1 l1 l2 n2 σ bs:
    (0 < n1)%Z →
    (∀ m, is_Some (σ !! (l1 +ₗ m)) ↔ (0 ≤ m < n1)%Z) →
    loc_chunk l1 = loc_chunk l2 →
    heap_ctx γ σ bs -∗ †l2…?n2 -∗ ⌜n2 = Some (Z.to_nat n1) ∧ l1 = l2⌝.
  Proof.
    iIntros (? Hrel1 ?) "(%hF & ? & HhF & %Hrel & %) Hf".
    rewrite heap_freeable_eq. iDestruct "Hf" as (?) "Hf".
    iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.
    iPureIntro.
    have [? [? [? {}Hrel2]]]:= Hrel _ _ Hf.
    destruct n2; last first. {
      have [_ [|? Hl]]:= Hrel1 0; [lia|].
      have [/=[|] ]:= Hrel2 (loc_idx l1 - loc_idx l2)%Z; last lia.
      eexists _. erewrite <-Hl. f_equal. rewrite /loc_add. destruct l1, l2 => /=.
      f_equal; [done |lia].
    }
    simplify_eq/=.
    destruct (decide (l1 = l2)).
    { subst. split; [|done].
      have Heq: (∀ i : Z, (0 ≤ i < n) ↔ (0 ≤ i < n1))%Z. naive_solver.
      f_equal.
      destruct (decide (n1 < n)%Z). { have := Heq n1. lia. }
      destruct (decide (n < n1)%Z). { have := Heq n. lia. }
      lia.
    }
    have ?: loc_idx l1 ≠ loc_idx l2 by destruct l1, l2;  naive_solver.
    destruct (decide (loc_idx l1 < loc_idx l2)%Z).
    - have [_ [|? Hl]]:= Hrel1 0; first lia.
      have [/=[|] ]:= Hrel2 (loc_idx l1 - loc_idx l2)%Z; last lia.
      eexists _. erewrite <-Hl. f_equal. rewrite /loc_add. destruct l1, l2 => /=.
      f_equal; [done |lia].
    - have [_ [|? Hl]]:= Hrel2 0; first lia.
      have [/=[|] ]:= Hrel1 (loc_idx l2 - loc_idx l1)%Z; last lia.
      eexists _. erewrite <-Hl. f_equal. rewrite /loc_add. destruct l1, l2 => /=.
      f_equal; [done |lia].
  Qed.

  Lemma heap_freeable_lookup σ l l' x n bs:
    σ !! l' = Some x → loc_chunk l' = loc_chunk l →
    heap_ctx γ σ bs -∗ †l…?n -∗ ⌜∃ n' : nat, n' < default 0 n ∧ l' = l +ₗ n'⌝.
  Proof.
    iIntros (Hlo ?) "(%hF&?&HhF&%Hrel&%) Hf".
    rewrite heap_freeable_eq. iDestruct "Hf" as (?) "Hf".
    iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.
    iPureIntro.
    have [? {}Hrel]:= Hrel _ _ Hf.
    have Hl': l' = (l +ₗ (loc_idx l' - loc_idx l)).
    { destruct l', l => /=. rewrite /loc_add/=. f_equal; [done|lia]. }
    rewrite Hl' in Hlo.
    eapply mk_is_Some, Hrel in Hlo.
    eexists (Z.to_nat (loc_idx l' - loc_idx l)). split; [lia|].
    rewrite Hl'. f_equal => /=. lia.
  Qed.

  Lemma heap_ctx_wf σ bs:
    heap_ctx γ σ bs -∗ ⌜heap_wf σ bs⌝.
  Proof. by iDestruct 1 as (?) "(?&?&?&%)". Qed.

  (** Weakest precondition *)
  Lemma heap_alloc_vs σ l n v:
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    own γ.(heap_name) (● to_heap σ)
    ==∗ own γ.(heap_name) (● to_heap (heap_array l (replicate n v) ∪ σ))
       ∗ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ (replicate n v),
           {[l +ₗ i := (1%Qp, Cinr 0%nat, to_agree v)]}).
  Proof.
    intros FREE. rewrite -own_op. apply own_update, auth_update_alloc.
    revert l FREE. induction n as [|n IH]=> l FRESH.
    { by rewrite left_id. }
    rewrite replicate_S (big_opL_consZ_l (λ k _, _ (_ k) _ )) /=.
    etrans; first apply (IH (l +ₗ 1)).
    { intros. by rewrite loc_add_assoc. }
    rewrite loc_add_0 -insert_singleton_op; last first.
    { rewrite -equiv_None big_opL_commute equiv_None big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None -{2}(loc_add_0 l). apply not_inj; lia. }
    rewrite -insert_union_singleton_l -insert_union_l.
    rewrite to_heap_insert. setoid_rewrite loc_add_assoc.
    apply alloc_local_update; last done. apply lookup_to_heap_None.
    apply lookup_union_None. split.
    - apply eq_None_not_Some => -[?] /heap_array_lookup[?[?[?[?[?]]]]].
      rewrite lookup_replicate.
      destruct l; simplify_eq/=. unfold loc_add in *. naive_solver lia.
    - by rewrite -(loc_add_0 l) FRESH.
  Qed.

  Lemma heap_alloc σ l n v bs:
    (0 < n)%Z →
    loc_idx l = 0 →
    loc_chunk l ∉ bs →
    (∀ m, σ !! (l +ₗ m) = None) →
    heap_ctx γ σ bs ==∗
      heap_ctx γ (heap_array l (replicate (Z.to_nat n) v) ∪ σ) ({[loc_chunk l]} ∪ bs) ∗ heap_freeable γ l 1 (Some (Z.to_nat n)) ∗
      l ↦∗ replicate (Z.to_nat n) v.
  Proof.
    intros ???; iDestruct 1 as (hF) "(Hvalσ & HhF & %Hrel & %Hwf)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
    iMod (ghost_map_insert l (Some _) with "HhF") as "[? ?]".
    { apply eq_None_not_Some => -[? /Hrel]. naive_solver. }
    rewrite heap_freeable_eq heap_mapsto_vec_combine //.
    2: { by destruct (Z.to_nat n). }
    iFrame. iModIntro. iSplit; [|done]. iExists _. iFrame.
    iPureIntro. split.
    - by apply heap_freeable_rel_init_mem.
    - by apply heap_wf_init_mem.
  Qed.

  Lemma heap_free_vs σ l vl sts :
    length vl = length sts →
    own γ.(heap_name) (● to_heap σ) ∗ own γ.(heap_name) (◯ [^op list] i ↦ v ∈ zip sts vl,
      {[l +ₗ i := (1%Qp, to_lock_stateR v.1, to_agree v.2)]})
    ==∗ own γ.(heap_name) (● to_heap (free_mem l (length vl) σ)).
  Proof.
    rewrite -own_op => Hlen. apply own_update, auth_update_dealloc.
    revert σ l sts Hlen. induction vl as [|v vl IH]=> σ l; [by case |] => -[//|st sts][?].
    cbn [zip_with]. rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= loc_add_0.
    apply local_update_total_valid=> _ Hvalid _.
    assert (([^op list] k↦y ∈ zip sts vl,
      {[l +ₗ (1 + k) := (1%Qp, to_lock_stateR y.1, to_agree y.2)]} : heapUR) !! l = None).
    { move: (Hvalid l). rewrite lookup_op lookup_singleton.
      by move=> /(cmra_discrete_valid_iff 0) /exclusiveN_Some_l. }
    rewrite -insert_singleton_op //. etrans.
    { apply (delete_local_update _ _ l (1%Qp, to_lock_stateR st, to_agree v)).
      by rewrite lookup_insert. }
    rewrite delete_insert // -to_heap_delete delete_free_mem; [|done].
    setoid_rewrite <-loc_add_assoc. by apply IH.
  Qed.

  Lemma heap_free σ l vl (n : Z) sts bs:
    n = length vl →
    heap_ctx γ σ bs -∗ l ↦∗[sts] vl -∗ †l…?(Some (length vl))
    ==∗ ⌜0 < n⌝%Z ∗ ⌜∀ m, is_Some (σ !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝%Z ∗
        †l…?None ∗ heap_ctx γ (free_mem l (Z.to_nat n) σ) bs.
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & %REL & %Hwf)". subst.
    rewrite heap_freeable_eq. iIntros "Hmt [% Hf]".
    iDestruct (ghost_map_lookup with "HhF Hf") as %Hf.
    move: (Hf) => /REL[?[?[??]]]. simplify_eq/=.
    iSplitR. { iPureIntro. lia. } iSplitR; first done.
    iDestruct (heap_mapsto_vec_st_length with "Hmt") as %?.
    iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ"; [done| |].
    { rewrite heap_mapsto_vec_st_combine //. iFrame. destruct vl; simpl in * => //; lia. }
    rewrite Nat2Z.id.
    iMod (ghost_map_update None with "HhF Hf") as "[? $]".
    iModIntro. iSplit;[done|]. iExists _. iFrame. iPureIntro.
    eauto using heap_freeable_rel_free_mem, heap_wf_free_mem.
  Qed.

  Lemma heap_mapsto_lookup σ l ls q v :
    own γ.(heap_name) (● to_heap σ) -∗
    own γ.(heap_name) (◯ {[ l := (q, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜∃ n' : nat,
        σ !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    by exists O. eauto. exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_lookup_1 σ l ls v :
    own γ.(heap_name) (● to_heap σ) -∗
    own γ.(heap_name) (◯ {[ l := (1%Qp, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜σ !! l = Some (ls, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma heap_read_vs σ n1 n2 nf l q v:
    σ !! l = Some (RSt (n1 + nf), v) →
    own γ.(heap_name) (● to_heap σ) -∗ heap_mapsto γ l (RSt n1) q v
    ==∗ own γ.(heap_name) (● to_heap (<[l:=(RSt (n2 + nf), v)]> σ))
        ∗ heap_mapsto γ l (RSt n2) q v.
  Proof.
    rewrite heap_mapsto_eq.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma heap_read_st σ l st q v bs:
    heap_ctx γ σ bs -∗ l ↦[st]{q} v -∗
    ⌜∃ n' : nat,
        σ !! l = Some (match st with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.

  Lemma heap_read_st_1 σ l st v bs:
    heap_ctx γ σ bs -∗ l ↦[st] v -∗ ⌜σ !! l = Some (st, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; eauto.
  Qed.

  Lemma heap_read σ l q v bs:
    heap_ctx γ σ bs -∗ l ↦{q} v -∗ ∃ n, ⌜σ !! l = Some (RSt n, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.

  Lemma heap_read_1 σ l v bs:
    heap_ctx γ σ bs -∗ l ↦ v -∗ ⌜σ !! l = Some (RSt 0, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; auto.
  Qed.

  Lemma heap_read_na_1 σ l q v n bs:
    heap_ctx γ σ bs -∗ l ↦[RSt n]{q} v ==∗ ∃ n',
      ⌜σ !! l = Some (RSt (n + n'), v)⌝ ∗
      heap_ctx γ (<[l:=(RSt (S (n + n')), v)]> σ) bs ∗
      l ↦[RSt (S n)]{q} v.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st with "Hσ Hmt") as %[n' Hσl]; eauto.
    iDestruct "Hσ" as (hF) "(Hσ & HhF & % & %)".
    iMod (heap_read_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n'; iSplit; [done|]. iFrame.
    iExists hF. iFrame. eauto 8 using heap_freeable_rel_stable, heap_wf_stable.
  Qed.

  Lemma heap_read_na_2 σ l q v n bs:
    heap_ctx γ σ bs -∗ l ↦[RSt (S n)]{q} v ==∗ ∃ n',
      ⌜σ !! l = Some (RSt (S (n + n')), v)⌝ ∗
      heap_ctx γ (<[l:=(RSt (n + n'), v)]> σ) bs ∗
      l ↦[RSt n]{q} v.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st with "Hσ Hmt") as %[n' Hσl]; eauto.
    iDestruct "Hσ" as (hF) "(Hσ & HhF & % & %)".
    iMod (heap_read_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n'; iSplit; [done|]. iFrame.
    iExists hF. iFrame. eauto 8 using heap_freeable_rel_stable, heap_wf_stable.
  Qed.

  Lemma heap_read_na σ l q v bs:
    heap_ctx γ σ bs -∗ l ↦{q} v ==∗ ∃ n,
      ⌜σ !! l = Some (RSt n, v)⌝ ∗
      heap_ctx γ (<[l:=(RSt (S n), v)]> σ) bs ∗
      ∀ σ2 bs2, heap_ctx γ σ2 bs2 ==∗ ∃ n2, ⌜σ2 !! l = Some (RSt (S n2), v)⌝ ∗
        heap_ctx γ (<[l:=(RSt n2, v)]> σ2) bs2 ∗ l ↦{q} v.
  Proof.
    iIntros "Hσ Hmt".
    iMod (heap_read_na_1 with "Hσ Hmt") as (? ?) "[Hσ Hmt]".
    iModIntro. iExists _. iFrame. iSplit; [done|].
    iIntros (σ2 bs2) "Hσ".
    iMod (heap_read_na_2 with "Hσ Hmt") as (? ?) "[Hσ Hmt]".
    iModIntro. iExists _. iFrame. done.
  Qed.

  Lemma heap_write_vs σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own γ.(heap_name) (● to_heap σ) -∗ heap_mapsto γ l st1 1%Qp v
    ==∗ own γ.(heap_name) (● to_heap (<[l:=(st2, v')]> σ))
        ∗ heap_mapsto γ l st2 1%Qp v'.
  Proof.
    rewrite heap_mapsto_eq.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write σ l v v' st st' bs:
    heap_ctx γ σ bs -∗ l ↦[st] v ==∗ heap_ctx γ (<[l:=(st', v')]> σ) bs ∗ l ↦[st'] v'.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; auto.
    iDestruct "Hσ" as (hF) "(Hσ & HhF & % & %)".
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. iExists _. iFrame. eauto 8 using heap_freeable_rel_stable, heap_wf_stable.
  Qed.

  Lemma heap_write_na_1 σ l v st bs:
    heap_ctx γ σ bs -∗ l ↦[st] v ==∗
      ⌜σ !! l = Some (st, v)⌝ ∗
      heap_ctx γ (<[l:=(WSt, v)]> σ) bs ∗
      l ↦[WSt] v.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; eauto.
    iSplitR; [done|]. iApply (heap_write with "Hσ Hmt").
  Qed.

  Lemma heap_write_na_2 σ l v v' bs:
    heap_ctx γ σ bs -∗ l ↦[WSt] v ==∗
      ⌜σ !! l = Some (WSt, v)⌝ ∗
      heap_ctx γ (<[l:=(RSt 0, v')]> σ) bs ∗
      l ↦ v'.
  Proof.
    iIntros "Hσ Hmt".
    iDestruct (heap_read_st_1 with "Hσ Hmt") as %?; eauto.
    iSplitR; [done|]. iApply (heap_write with "Hσ Hmt").
  Qed.

  Lemma heap_write_na σ l v v' bs:
    heap_ctx γ σ bs -∗ l ↦ v ==∗
      ⌜σ !! l = Some (RSt 0, v)⌝ ∗
      heap_ctx γ (<[l:=(WSt, v)]> σ) bs ∗
      ∀ σ2 bs2, heap_ctx γ σ2 bs2 ==∗ ⌜σ2 !! l = Some (WSt, v)⌝ ∗
        heap_ctx γ (<[l:=(RSt 0, v')]> σ2) bs2 ∗ l ↦ v'.
  Proof.
    iIntros "Hσ Hmt".
    iMod (heap_write_na_1 with "Hσ Hmt") as (?) "[Hσ Hmt]".
    iModIntro. iFrame. iSplit; [done|].
    iIntros (σ2 bs2) "Hσ".
    iMod (heap_write_na_2 with "Hσ Hmt") as (?) "[Hσ Hmt]".
    iModIntro. iFrame. done.
  Qed.

End heap.
