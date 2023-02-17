From iris.algebra Require Import excl auth frac agree gmap list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.program_logic Require Import lifting.
From WBLogrel.F_mu_ref Require Export wp_rules.
From iris.prelude Require Import options.
Import uPred.

Definition specN := nroot .@ "spec".


(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmra := gmapUR nat (exclR exprO).
Definition heapUR (L V : Type) `{Countable L} : ucmra :=
  gmapUR L (prodR fracR (agreeR (leibnizO V))).
Definition cfgUR := prodUR tpoolUR (heapUR loc val).

Fixpoint to_tpool_go (i : nat) (tp : list expr) : tpoolUR :=
  match tp with
  | [] => ∅
  | e :: tp => <[i:=Excl e]>(to_tpool_go (S i) tp)
  end.
Definition to_tpool : list expr → tpoolUR := to_tpool_go 0.
Definition to_heap {L V} `{Countable L} : gmap L V → heapUR L V :=
  fmap (λ v, (1%Qp, to_agree (v : leibnizO V))).

(** The CMRA for the thread pool. *)
Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Section definitionsS.
  Context `{cfgSG Σ, invGS Σ}.

  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (ε, {[ l := (q, to_agree v) ]})).

  Definition tpool_mapsto (j : nat) (e: expr) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl e ]}, ∅)).

  Definition spec_inv (ρ : cfg F_mu_ref_lang) : iProp Σ :=
    (∃ tp σ, own cfg_name (● (to_tpool tp, to_heap σ))
                 ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I.
  Definition spec_ctx : iProp Σ :=
    (∃ ρ, inv specN (spec_inv ρ))%I.

  Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v).
  Proof. apply _. Qed.
  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.
End definitionsS.
Global Typeclasses Opaque heapS_mapsto tpool_mapsto.

Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Ltac iAsimpl :=
  repeat match goal with
  | |- context [ (_ ⤇ ?e)%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [asimpl; unfold e'; reflexivity|];
    unfold e'; clear e')
  | |- context [ WP ?e @ _ {{ _ }}%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [asimpl; unfold e'; reflexivity|];
    unfold e'; clear e')
 | |- context [ WBWP ?e @ _; _ {{ _ }}%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [asimpl; unfold e'; reflexivity|];
    unfold e'; clear e')
  end.

Section conversions.
  Context `{cfgSG Σ}.

  (** Conversion to tpools and back *)
  Lemma to_tpool_valid es : ✓ to_tpool es.
  Proof.
    rewrite /to_tpool. move: 0.
    induction es as [|e es]=> n //. by apply insert_valid.
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof.
    cut (∀ i, to_tpool_go i tp !! (i + j) = Excl <$> tp !! j).
    { intros help. apply (help 0). }
    revert j. induction tp as [|e tp IH]=> //= -[|j] i /=.
    - by rewrite Nat.add_0_r lookup_insert.
    - by rewrite -Nat.add_succ_comm lookup_insert_ne; last lia.
  Qed.
  Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Local Hint Resolve tpool_lookup_Some : core.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
    - by rewrite tpool_lookup lookup_insert list_lookup_insert.
    - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
      by rewrite tpool_lookup.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.

  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp:=Excl e]>(to_tpool tp).
  Proof.
    intros. apply: map_eq=> i.
    destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
    - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
    - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
    - rewrite lookup_insert_ne; last lia.
      rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
         change (ofe_car exprO) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included_l [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

End conversions.

Section to_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, to_agree (v:leibnizO V))]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

End to_heap.

Section cfg.
  Context `{heapIG Σ, cfgSG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.

  Local Hint Resolve tpool_lookup : core.
  Local Hint Resolve tpool_lookup_Some : core.
  Local Hint Resolve to_tpool_insert : core.
  Local Hint Resolve to_tpool_insert' : core.
  Local Hint Resolve tpool_singleton_included : core.

  Lemma mapstoS_agree l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /heapS_mapsto -own_op own_valid uPred.discrete_valid. f_equiv.
    rewrite auth_frag_op_valid -pair_op singleton_op -pair_op.
    rewrite pair_valid singleton_valid pair_valid to_agree_op_valid_L.
    by intros [_ [_ [=]]].
  Qed.
  Lemma mapstoS_combine l q1 q2 v1 v2 :
    l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ l ↦ₛ{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapstoS_agree with "Hl1 Hl2") as %->.
    rewrite /heapS_mapsto. iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.
  Lemma mapstoS_valid l q v : l ↦ₛ{q} v -∗ ✓ q.
  Proof.
    rewrite /heapS_mapsto own_valid !discrete_valid auth_frag_valid.
    by apply pure_mono=> -[_] /singleton_valid [??].
  Qed.
  Lemma mapstoS_valid_2 l q1 q2 v1 v2 :
    l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (mapstoS_combine with "H1 H2") as "[? ->]".
    by iApply (mapstoS_valid l _ v2).
  Qed.

  Lemma step_insert K tp j e σ κ e' σ' efs :
    tp !! j = Some (fill K e) → head_step e σ κ e' σ' efs →
    erased_step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle tp j (fill K e)) //.
    rewrite insert_app_r_alt take_length_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=. eexists.
    eapply step_atomic; eauto. by apply: Ectx_step'.
  Qed.

  Lemma step_insert_no_fork K tp j e σ κ e' σ' :
    tp !! j = Some (fill K e) → head_step e σ κ e' σ' [] →
    erased_step (tp, σ) (<[j:=fill K e']> tp, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma nsteps_inv_r {A} n (R : A → A → Prop) x y :
    relations.nsteps R (S n) x y → ∃ z, relations.nsteps R n x z ∧ R z y.
  Proof.
    revert x y; induction n as [|n IH]; intros x y.
    - inversion 1; subst.
      match goal with H : relations.nsteps _ 0 _ _ |- _ => inversion H end; subst.
      eexists; repeat econstructor; eauto.
    - inversion 1; subst.
      edestruct IH as [z [? ?]]; eauto.
      exists z; split; eauto using relations.nsteps_l.
  Qed.

  Lemma step_pure' E j K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hinv Hj]". iDestruct "Hinv" as (ρ) "Hspec".
    rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown Hrtc]" "Hclose".
    iDestruct "Hrtc" as %Hrtc.
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[Htpj%tpool_singleton_included' _]%prod_included ?]
          %auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iApply "Hclose". iNext. iExists (<[j:=fill K e']> tp), σ.
    rewrite to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    apply rtc_nsteps in Hrtc; destruct Hrtc as [m Hrtc].
    specialize (Hex HP). apply (rtc_nsteps_2 (m + n)).
    eapply nsteps_trans; eauto.
    revert e e' Htpj Hex.
    induction n as [|n IH] => e e' Htpj Hex.
    - inversion Hex; subst.
      rewrite list_insert_id; eauto. econstructor.
    - apply nsteps_inv_r in Hex.
      destruct Hex as [z [Hex1 Hex2]].
      specialize (IH _ _ Htpj Hex1).
      eapply nsteps_r; eauto.
      replace (<[j:=fill K e']> tp) with
          (<[j:=fill K e']> (<[j:=fill K z]> tp)); last first.
      { clear. revert tp; induction j as [|j IHj]; intros tp.
        - destruct tp; trivial.
        - destruct tp; simpl; auto. by rewrite IHj. }
      destruct Hex2 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]];
        subst.
      inversion Hexs; simpl in *; subst.
      rewrite -!fill_app.
      eapply step_insert_no_fork; eauto.
      { apply list_lookup_insert. apply lookup_lt_is_Some; eauto. }
  Qed.


  Lemma do_step_pure E j K e e' `{!PureExec True 1 e e'}:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof. by eapply step_pure'; last eauto. Qed.

  Lemma step_alloc E j K e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Alloc e) ={E}=∗ ∃ l, j ⤇ fill K (Loc l) ∗ l ↦ₛ v.
  Proof.
    iIntros (??) "[#Hinv Hj]". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    destruct (exist_fresh (dom σ)) as [l Hl%not_elem_of_dom].
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]
          %auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K (Loc l)))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,to_agree v)); last done.
      by apply lookup_to_heap_None. }
    iExists l. rewrite /heapS_mapsto. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (Loc l)]> tp), (<[l:=v]>σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_load E j K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Load (Loc l)) ∗ l ↦ₛ{q} v
    ={E}=∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hown Hl") 
      as %[[? ?%heap_singleton_included]%prod_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E j K l v' e v:
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Store (Loc l) e) ∗ l ↦ₛ v'
    ={E}=∗ j ⤇ fill K Unit ∗ l ↦ₛ v.
  Proof.
    iIntros (??) "(#Hinv & Hj & Hl)". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]
             %prod_included _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%heap_singleton_included]%prod_included _]
          %auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K Unit))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree v)); last done.
      by rewrite /to_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K Unit]> tp), (<[l:=v]>σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_rec E j K e1 e2 v :
    to_val e2 = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (App (Rec e1) e2)
    ={E}=∗ j ⤇ fill K (e1.[Rec e1,e2/]).
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_lam E j K e1 e2 v :
    to_val e2 = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (App (Lam e1) e2)
    ={E}=∗ j ⤇ fill K (e1.[e2/]).
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_letin E j K e1 e2 v :
    to_val e1 = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (LetIn e1 e2)
    ={E}=∗ j ⤇ fill K (e2.[e1/]).
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_seq E j K e1 e2 v :
    to_val e1 = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Seq e1 e2)
    ={E}=∗ j ⤇ fill K e2.
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_tlam E j K e :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (TApp (TLam e)) ={E}=∗ j ⤇ fill K e.
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_fold E j K e v :
    to_val e = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Unfold (Fold e)) ={E}=∗ j ⤇ fill K e.
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_pack E j K e1 v e2 :
    to_val e1 = Some v → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (UnpackIn (Pack e1) e2) ={E}=∗ j ⤇ fill K e2.[e1/].
  Proof. by intros ?; apply: do_step_pure. Qed.

  Lemma step_fst E j K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Fst (Pair e1 e2)) ={E}=∗ j ⤇ fill K e1.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_snd E j K e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Snd (Pair e1 e2)) ={E}=∗ j ⤇ fill K e2.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_case_inl E j K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Case (InjL e0) e1 e2)
      ={E}=∗ j ⤇ fill K (e1.[e0/]).
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_case_inr E j K e0 v0 e1 e2 :
    to_val e0 = Some v0 → nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Case (InjR e0) e1 e2)
      ={E}=∗ j ⤇ fill K (e2.[e0/]).
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_if_false E j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (If (#♭ false) e1 e2) ={E}=∗ j ⤇ fill K e2.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_if_true E j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (If (#♭ true) e1 e2) ={E}=∗ j ⤇ fill K e1.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_nat_binop E j K op a b :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (BinOp op (#n a) (#n b))
      ={E}=∗ j ⤇ fill K (of_val (binop_eval op a b)).
  Proof. by intros; apply: do_step_pure. Qed.

End cfg.
