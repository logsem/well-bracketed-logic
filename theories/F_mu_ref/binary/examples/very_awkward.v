From iris.algebra Require Import auth gmap.
From iris.staging.algebra Require Import monotone.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogrel.F_mu_ref Require Import rules.
From WBLogrel.F_mu_ref.binary Require Import soundness rules.
From iris.prelude Require Import options.

Definition very_awkward : expr :=
  LetIn
    (Alloc (#n 0))
    (Lam
       (Seq
          (Store (Var 1) (#n 0))
          (Seq
             (App (Var 0) Unit)
             (Seq
                (Store (Var 1) (#n 1))
                (Seq
                   (App (Var 0) Unit)
                   (Load (Var 1))))))).

Lemma very_awkward_typed : [] ⊢ₜ very_awkward : TArrow (TArrow TUnit TUnit) TNat.
Proof. repeat econstructor. Qed.

Definition call_twice_return_one : expr :=
  (Lam
     (Seq
        (App (Var 0) Unit)
        (Seq
           (App (Var 0) Unit)
           (#n 1)))).

Lemma call_twice_return_one_typed : [] ⊢ₜ call_twice_return_one : TArrow (TArrow TUnit TUnit) TNat.
Proof. repeat econstructor. Qed.

Definition rel : relation bool :=
  λ b1 b2,
  match b2 with
  | true => True
  | false =>
    match b1 with
    | true => False
    | false => True
    end
  end.

Global Instance rel_PreOrder : PreOrder rel.
Proof. split; repeat intros []; done. Qed.

Section rel.
  Context `{!inG Σ (authUR (mraUR rel))}.

  Definition exactly (γ : gname) (b : bool) := own γ (● principal rel b).

  Definition atleast (γ : gname) (b : bool) := own γ (◯ principal rel b).

  Lemma exactly_update γ b1 b2 : rel b1 b2 → exactly γ b1 ==∗ exactly γ b2 ∗ atleast γ b2.
  Proof.
    intros.
    rewrite -own_op; apply own_update.
    apply auth_update_alloc.
    apply mra_local_update_grow; done.
  Qed.

  Lemma exactly_alloc b : ⊢ |==> ∃ γ, exactly γ b.
  Proof. apply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma exatly_atleast_rel γ b1 b2 : exactly γ b1 -∗ atleast γ b2 -∗ ⌜rel b2 b1⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl _]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

End rel.

Definition relΣ := #[GFunctor (authUR (mraUR rel))].

Global Instance sub_relΣ_inG Σ : subG relΣ Σ → inG Σ (authUR (mraUR rel)).
Proof. solve_inG. Qed.

Section very_awkward.
  Context `{heapIG Σ, cfgSG Σ, ghost_regG Σ}.

  Lemma very_awkward_call_twice_return_one_refinement `{!inG Σ (authUR (mraUR rel))} :
    ⊢ [] ⊨ very_awkward ≤log≤ call_twice_return_one : TArrow (TArrow TUnit TUnit) TNat.
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (M j K) "Hreg Hj"; simpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_alloc; first done.
    iNext. iIntros (l) "Hl /=".
    iApply wp_pure_step_later; auto.
    iNext. iAsimpl.
    iMod (exactly_alloc false) as (γ) "Hex".
    iMod (res_name_alloc _ γ with "Hreg") as (id HidM) "[Hreg Hid]".
    rewrite insert_union_singleton_r; last first.
    { rewrite -(not_elem_of_dom (D := gset ghost_id)); done. }
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ b, named_ghost id 1 γ ∗ exactly γ b ∗ if b then l ↦ᵢ (#nv 1) else l ↦ᵢ (#nv 0))%I
            with "[Hex Hid Hl]") as "#Hinv".
    { iNext; iExists γ, false; iFrame. }
    iApply wp_value.
    iExists (LamV _), _; iFrame; iSplit.
    { iPureIntro. apply map_union_subseteq_l. }
    iIntros "!#" ([f f']) "#Hff".
    clear j K M HidM.
    iIntros (M j K) "Hreg Hj"; simpl.
    iApply wp_pure_step_later; auto. iNext.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAsimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ1 b) "(>Hid & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (named_ghost_agree with "Hreg Hid") as %Hids1.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (named_ghost_update _ _ _ γ2 with "Hreg Hid") as "[Hreg Hid]".
    iApply (wp_store with "[$]").
    iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hex2 Hid Hl]") as "_".
    { iNext; iExists γ2, false; iFrame. }
    iModIntro.
    iApply wp_pure_step_later; auto. iNext.
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_wand with "[Hj Hreg]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply ("Hff" $! _ _ (SeqCtx _ :: K) with "[$] [$]"). }
    iIntros (?); iDestruct 1 as (? N1) "(%HN1 & Hreg & Hj & [% %])"; simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply (wp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ3 b2) "(>Hid & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iMod (named_ghost_update _ _ _ γ1 with "Hreg Hid") as "[Hreg Hid]".
    iApply (wp_store with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists γ1, true; iFrame. }
    iModIntro. simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_wand with "[Hj Hreg]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply ("Hff" $! _ _ (SeqCtx _ :: K) with "[$] [$]"). }
    iIntros (?); iDestruct 1 as (? N2) "(%HN2 & Hreg & Hj & [% %])"; simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iInv (nroot .@ "awk") as (γ4 b3) "(>Hid & >Hex1 & Hl)" "Hcl".
    iDestruct (named_ghost_agree with "Hreg Hid") as %Hids2.
    assert (N2 !! id = Some γ1) as Heq.
    { eapply lookup_weaken; last by apply HN2.
      rewrite lookup_insert; done. }
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    iApply (wp_load with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists _, true; iFrame. }
    iModIntro.
    iExists (#nv 1), _; iFrame.
    iSplit; last by iExists _.
    iPureIntro.
    etrans; last apply HN2.
    etrans; last apply insert_mono, HN1.
    rewrite insert_insert insert_id; auto.
  Qed.

  Lemma call_twice_return_one_very_awkward_refinement `{inG Σ (authUR (mraUR rel))} :
    ⊢ [] ⊨ call_twice_return_one ≤log≤ very_awkward : TArrow (TArrow TUnit TUnit) TNat.
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (M j K) "Hreg Hj"; simpl.
    iMod (step_alloc _ _ (LetInCtx _ :: K) with "[$]") as (l) "[Hj Hl]"; eauto.
    simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAsimpl.
    iMod (exactly_alloc false) as (γ) "Hex".
    iMod (res_name_alloc _ γ with "Hreg") as (id HidM) "[Hreg Hid]".
    rewrite insert_union_singleton_r; last first.
    { rewrite -(not_elem_of_dom (D := gset ghost_id)); done. }
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ b, named_ghost id 1 γ ∗ exactly γ b ∗ if b then l ↦ₛ (#nv 1) else l ↦ₛ (#nv 0))%I
            with "[Hex Hid Hl]") as "#Hinv".
    { iNext; iExists γ, false; iFrame. }
    iApply wp_value.
    iExists (LamV _), _; iFrame; iSplit.
    { iPureIntro. apply map_union_subseteq_l. }
    iIntros "!#" ([f f']) "#Hff".
    clear j K M HidM.
    iIntros (M j K) "Hreg Hj"; simpl.
    iApply wp_pure_step_later; auto. iNext.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAsimpl.
    iApply fupd_wp.
    iInv (nroot .@ "awk") as (γ1 b) "(>Hid & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ₛ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (named_ghost_agree with "Hreg Hid") as %Hids1.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (named_ghost_update _ _ _ γ2 with "Hreg Hid") as "[Hreg Hid]".
    iMod (step_store _ _ (SeqCtx _ :: K) with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hex2 Hid Hl]") as "_".
    { iNext; iExists γ2, false; iFrame. }
    iModIntro.
    simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_wand with "[Hj Hreg]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply ("Hff" $! _ _ (SeqCtx _ :: K) with "[$] [$]"). }
    iIntros (?); iDestruct 1 as (? N1) "(%HN1 & Hreg & Hj & [% %])"; simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply fupd_wp.
    iInv (nroot .@ "awk") as (γ3 b2) "(>Hid & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ₛ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iMod (named_ghost_update _ _ _ γ1 with "Hreg Hid") as "[Hreg Hid]".
    iMod (step_store _ _ (SeqCtx _ :: K) with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists γ1, true; iFrame. }
    iModIntro. simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_wand with "[Hj Hreg]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply ("Hff" $! _ _ (SeqCtx _ :: K) with "[$] [$]"). }
    iIntros (?); iDestruct 1 as (? N2) "(%HN2 & Hreg & Hj & [% %])"; simplify_eq/=.
    iApply wp_pure_step_later; auto. iNext.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply fupd_wp.
    iInv (nroot .@ "awk") as (γ4 b3) "(>Hid & >Hex1 & Hl)" "Hcl".
    iDestruct (named_ghost_agree with "Hreg Hid") as %Hids2.
    assert (N2 !! id = Some γ1) as Heq.
    { eapply lookup_weaken; last by apply HN2.
      rewrite lookup_insert; done. }
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    iMod "Hl".
    iMod (step_load with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists _, true; iFrame. }
    iModIntro.
    iApply wp_value.
    iExists (#nv 1), _; iFrame.
    iSplit; last by iExists _.
    iPureIntro.
    etrans; last apply HN2.
    etrans; last apply insert_mono, HN1.
    rewrite insert_insert insert_id; auto.
  Qed.

End very_awkward.

Theorem very_awkward_call_twice_return_one_ctx_equiv :
  [] ⊨ very_awkward ≤ctx≤ call_twice_return_one : TArrow (TArrow TUnit TUnit) TNat ∧
  [] ⊨ call_twice_return_one ≤ctx≤ very_awkward : TArrow (TArrow TUnit TUnit) TNat.
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; soundness_binaryΣ; ghost_regΣ; relΣ]).
  set (HG := soundness.soundness_unary_preIG Σ _ _ _).
  split.
  - eapply (binary_soundness Σ); auto using very_awkward_typed, call_twice_return_one_typed.
    intros; apply very_awkward_call_twice_return_one_refinement.
  -  eapply (binary_soundness Σ); auto using very_awkward_typed, call_twice_return_one_typed.
    intros; apply call_twice_return_one_very_awkward_refinement.
Qed.
