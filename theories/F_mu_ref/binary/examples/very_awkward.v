From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogrel.F_mu_ref Require Import rules.
From WBLogrel.F_mu_ref.binary Require Import soundness rules.
From WBLogrel Require Import oneshot.

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

Section very_awkward.
  Context `{heapIG Σ, cfgSG Σ, ghost_regG Σ, oneshotG Σ}.

  Lemma very_awkward_call_twice_return_one_refinement :
    ⊢ [] ⊨ very_awkward ≤log≤ call_twice_return_one : TArrow (TArrow TUnit TUnit) TNat.
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (j K) "Hj"; simpl.
    iApply (wbwp_bind (fill [LetInCtx _])).
    iApply wbwp_alloc; first done.
    iNext. iIntros (l) "Hl /=".
    iApply wbwp_pure_step_later; auto.
    iNext; iIntros "_". iAsimpl.
    iApply (wbwp_make_gstack
              (λ n, inv (nroot .@ "awk") (∃ γ s, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗
               ((pending γ ∗ l ↦ᵢ #nv 0) ∨ (shot γ ∗ l ↦ᵢ #nv 1))) ∗ gstack_exists n)%I with "[Hl]").
    { iIntros (n Hn) "Hfl Hfr".
      iMod new_pending as (γ) "Hpen".
      iPoseProof (gstack_frag_exists with "Hfr") as "#?".
      iMod (gstack_push _ _ _ γ with "Hfl Hfr") as "[Hfl Hfr]".
      iMod (inv_alloc with "[- Hfl]"); last by iModIntro; iExists _; iFrame.
      iNext; iExists γ, _. iFrame "Hfr". iSplit; first by rewrite gtop_gsingleton. iLeft; iFrame. }
    iIntros (n Hn) "#[Hinv Hex]".
    iApply wbwp_value.
    iExists (LamV _); iFrame.
    iIntros "!#" ([f f']) "#Hff".
    clear j K.
    iIntros (j K) "Hj"; simpl.
    iApply (wbwp_get_gstack_full n with "[$]"); first done.
    iIntros (s) "Hfl".
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAsimpl.
    iApply (wbwp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ1 s') ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ᵢ v ∗ (pending γ1 ∨ shot γ1))%I with "[Hl]" as (?) "[Hl Hps]".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %Hids1.
    iMod (new_pending) as (γ2) "Hpen2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hpen2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _; iFrame "Hfr"; iSplit; first by rewrite gtop_gpush. iLeft; iFrame. }
    iModIntro.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iAssert (|==> shot γ1)%I with "[Hps]" as ">#Hsh".
    { iDestruct "Hps" as "[Hp|Hs]"; last done. iApply shoot; done. }
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hj Hfl]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hff" $! _ (SeqCtx _ :: K) with "[$]"). }
    iIntros (?) "[Hfl Hj]". iDestruct "Hj" as (?) "(Hj & [% %])"; simplify_eq/=.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply (wbwp_bind (fill [SeqCtx _])).
    iInv (nroot .@ "awk") as (γ3 ?) ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ᵢ v)%I with "[Hl]" as (?) "Hl".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists γ1, _; iFrame "Hfr". iSplit; first done. iRight; iFrame; done. }
    iModIntro. simpl.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hj Hfl]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hff" $! _ (SeqCtx _ :: K) with "[$]"). }
    iIntros (?) "[Hfl Hj]"; iDestruct "Hj" as (?) "(Hj & [% %])"; simplify_eq/=.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iInv (nroot .@ "awk") as (γ4 ?) ">(Hfr & % & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct "Hl" as "[[Hp _]|[_ Hl]]".
    { iExFalso; iApply shot_not_pending; done. }
    iApply (wbwp_load with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists _, _; iFrame. iSplit; first done. iRight; iFrame; done. }
    iModIntro.
    iFrame "Hfl".
    iExists (#nv 1); iFrame; eauto.
  Qed.

  Lemma call_twice_return_one_very_awkward_refinement :
    ⊢ [] ⊨ call_twice_return_one ≤log≤ very_awkward : TArrow (TArrow TUnit TUnit) TNat.
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (j K) "Hj"; simpl.
    iMod (step_alloc _ _ (LetInCtx _ :: K) with "[$]") as (l) "[Hj Hl]"; eauto.
    simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto. iAsimpl.
    iApply (wbwp_make_gstack
              (λ n, inv (nroot .@ "awk") (∃ γ s, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗
               ((pending γ ∗ l ↦ₛ #nv 0) ∨ (shot γ ∗ l ↦ₛ  #nv 1))) ∗ gstack_exists n)%I with "[Hl]").
    { iIntros (n Hn) "Hfl Hfr".
      iMod new_pending as (γ) "Hpen".
      iPoseProof (gstack_frag_exists with "Hfr") as "#?".
      iMod (gstack_push _ _ _ γ with "Hfl Hfr") as "[Hfl Hfr]".
      iMod (inv_alloc with "[- Hfl]"); last by iModIntro; iExists _; iFrame.
      iNext; iExists γ, _. iFrame "Hfr". iSplit; first by rewrite gtop_gsingleton. iLeft; iFrame. }
    iIntros (n Hn) "#[Hinv Hex]".
    iApply wbwp_value.
    iExists (LamV _); iFrame.
    iIntros "!#" ([f f']) "#Hff".
    clear j K.
    iIntros (j K) "Hj"; simpl.
    iApply (wbwp_get_gstack_full n with "[$]"); first done.
    iIntros (s) "Hfl".
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAsimpl.
    iApply fupd_wbwp.
    iInv (nroot .@ "awk") as (γ1 s') ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ₛ v ∗ (pending γ1 ∨ shot γ1))%I with "[Hl]" as (?) "[Hl Hps]".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %Hids1.
    iMod (new_pending) as (γ2) "Hpen2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (step_store _ _ (SeqCtx _ :: K) with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hpen2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _; iFrame "Hfr"; iSplit; first by rewrite gtop_gpush. iLeft; iFrame. }
    iModIntro.
    simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAssert (|==> shot γ1)%I with "[Hps]" as ">#Hsh".
    { iDestruct "Hps" as "[Hp|Hs]"; last done. iApply shoot; done. }
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hj Hfl]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hff" $! _ (SeqCtx _ :: K) with "[$]"). }
    iIntros (?) "[Hfl Hj]"; iDestruct "Hj" as (?) "(Hj & [% %])"; simplify_eq/=.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply fupd_wbwp.
    iInv (nroot .@ "awk") as (γ3 ?) ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ₛ v)%I with "[Hl]" as (?) "Hl".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq /=.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (step_store _ _ (SeqCtx _ :: K) with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists γ1, _; iFrame "Hfr". iSplit; first done. iRight; iFrame; done. }
    iModIntro. simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply (wbwp_bind (fill [SeqCtx _])).
    iApply (wbwp_wand with "[Hj Hfl]").
    { iSpecialize ("Hff" $! (UnitV, UnitV) with "[//]").
      iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hff" $! _ (SeqCtx _ :: K) with "[$]"). }
    iIntros (?) "[Hfl Hj]"; iDestruct "Hj" as (?) "(Hj & [% %])"; simplify_eq/=.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iApply fupd_wbwp.
    iInv (nroot .@ "awk") as (γ4 ?) ">(Hfr & % & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct "Hl" as "[[Hp _]|[_ Hl]]".
    { iExFalso; iApply shot_not_pending; done. }
    iMod (step_load with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists _, _; iFrame. iSplit; first done. iRight; iFrame; done. }
    iModIntro.
    iApply wbwp_value.
    iFrame "Hfl".
    iExists (#nv 1); iFrame; eauto.
  Qed.

End very_awkward.

Theorem very_awkward_call_twice_return_one_ctx_equiv :
  [] ⊨ very_awkward ≤ctx≤ call_twice_return_one : TArrow (TArrow TUnit TUnit) TNat ∧
  [] ⊨ call_twice_return_one ≤ctx≤ very_awkward : TArrow (TArrow TUnit TUnit) TNat.
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; soundness_binaryΣ; gstacksΣ; oneshotΣ]).
  set (HG := soundness.soundness_unary_preIG Σ _ _ _).
  split.
  - eapply (binary_soundness Σ); auto using very_awkward_typed, call_twice_return_one_typed.
    intros; apply very_awkward_call_twice_return_one_refinement.
  -  eapply (binary_soundness Σ); auto using very_awkward_typed, call_twice_return_one_typed.
    intros; apply call_twice_return_one_very_awkward_refinement.
Qed.
