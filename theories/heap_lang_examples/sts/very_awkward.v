From iris.algebra Require Import auth gmap.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import adequacy.
From WBLogrel.program_logic.lib Require Import sts.
From WBLogrel.heap_lang Require Import adequacy.
From iris.heap_lang Require Import lang notation.
From WBLogrel.heap_lang Require Import proofmode.

Program Canonical Structure vae_sts : STS := {| STS_state := bool; pub_rel := λ a b, implb a b = true; pri_rel := λ _ _, True |}.
Next Obligation.
Proof. split; (do 3 try intros []); done. Qed.
Next Obligation.
Proof. done. Qed.
Next Obligation.
Proof. done. Qed.

Definition very_awkward : expr :=
  let: "l" := ref #0 in
  λ: "f", "l" <- #0;; "f" #();; "l" <- #1;; "f" #();; ! "l".

Definition very_awkward_self_apply : expr :=
  let: "f" := very_awkward in
  "f" (λ: <>, "f" (λ: <>, #());; #()).

Section very_awkward.
  Context `{!wbheapGS Σ, !inG Σ (STSUR vae_sts)}.

  Lemma wbwp_very_awkward :
    ⊢ {WB{{ True }}}
      very_awkward
      {{{(f : val), RET f;
          ∀ (g : val),
            {WB{{ {WB{{ True }}} g #() {{{ RET #(); True }}} }}} f g {{{ RET #1; True }}}
      }}}.
  Proof.
    rewrite /very_awkward.
    iIntros (Φ) "_ !# HΦ".
    wbwp_alloc l as "Hl".
    wbwp_pures.
    iApply (wbwp_make_gstack (λ N, STS_inv N (λ b : vae_sts, if b then l ↦ #1 else l ↦ #0)%I) with "[Hl]").
    { iIntros (? ?) "? ?".
      iMod (make_STS false (λ b, if b then l ↦ #1 else l ↦ #0)%I with "[$] [$] [$]") as "[Hinv Hstk]".
      iDestruct "Hstk" as (?) "Hstk".
      iModIntro; iExists _; iFrame. }
    iIntros (N ?) "#Hinv".
    iApply wbwp_value.
    iApply "HΦ".
    clear Φ.
    iIntros (g) "!#".
    iIntros (Φ) "#Hg HΦ".
    wbwp_pures.
    iApply wbwp_sts_get_state; [done|done|by iFrame "#"|].
    iIntros (sc) "Hfr".
    wbwp_bind (_ <- _)%E.
    iInv (STS_inv_name N) as (sc') "(>Hfl & Hl)" "Hclose".
    iDestruct (sts_configs_pub_related with "Hfl Hfr") as "#Hrl".
    iAssert (▷ ∃ v, l ↦ v)%I with "[Hl]" as (?) ">Hl"; first (destruct (state_of sc'); iExists _; iFrame).
    wbwp_store.
    iApply wbwp_value.
    iMod (sts_configs_update_frag with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (sts_make_private_trans _ _ false with "[$] [$]") as (sc'') "(Hprrel & %Hsc'' & Hfr & Hfl)"; first done.
    iMod ("Hclose" with "[Hl Hfl]") as "_".
    { iNext. iExists sc''; rewrite Hsc''; iFrame. }
    iModIntro.
    wbwp_pures.
    wbwp_bind (g _)%E.
    iApply (wbwp_wand with "[Hfr]").
    { iApply (wbwp_sts_mend with "Hfr").
      replace ((∅ ∪ {[N]}) ∖ {[N]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hg" $! (λ w, ⌜w = #()⌝)%I); done. }
    iIntros (?) "[Hfr->] /=".
    wbwp_pures.
    wbwp_bind (_ <- _)%E.
    iInv (STS_inv_name N) as (sc3) "(>Hfl & Hl)" "Hclose".
    iAssert (▷ ∃ v, l ↦ v)%I with "[Hl]" as (?) ">Hl"; first by destruct (state_of sc3); iExists _; iFrame.
    wbwp_store.
    iApply wbwp_value.
    iDestruct (sts_configs_pub_related with "Hfl Hfr") as "#Hrl'".
    iMod (sts_configs_update_frag with "Hfl Hfr") as "[Hfl Hfr]".
    iDestruct (related_private_public with "Hprrel Hrl'") as "Hprrel".
    iMod (sts_make_undo_private_trans with "Hprrel Hfr Hfl") as "[Hfr Hfl]".
    iMod (sts_make_public_trans _ _ true with "Hfr Hfl") as (sc4) "(Hrl'' & %Hsc4 & Hfr & Hfl)".
    { rewrite /= implb_true_r //. }
    iMod ("Hclose" with "[Hl Hfl]") as "_".
    { iNext. iExists sc4; rewrite Hsc4; iFrame. }
    iModIntro.
    wbwp_pures.
    wbwp_bind (g _)%E.
    iApply (wbwp_wand with "[Hfr]").
    { iApply (wbwp_sts_mend with "Hfr").
      replace ((∅ ∪ {[N]}) ∖ {[N]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hg" $! (λ w, ⌜w = #()⌝)%I); done. }
    iIntros (?) "[Hfr->] /=".
    wbwp_pures.
    iInv (STS_inv_name N) as (sc5) "(>Hfl & Hl)" "Hclose".
    iDestruct (sts_configs_pub_related with "Hfl Hfr") as "#Hrl'''".
    iMod (sts_configs_update_frag with "Hfl Hfr") as "[Hfl Hfr]".
    iDestruct (related_public_states with "Hrl'''") as "%Hpubrel".
    rewrite Hsc4 in Hpubrel.
    destruct (state_of sc5) eqn:Hsc5; last done.
    wbwp_load.
    iApply wbwp_value.
    iMod ("Hclose" with "[Hl Hfl]") as "_".
    { iNext. iExists sc5; rewrite Hsc5; iFrame. }
    iModIntro.
    iSplitL "HΦ"; first by iApply "HΦ".
    iExists _; iFrame.
    iApply (related_public_trans with "[Hrl Hrl''] [$]").
    iApply (related_public_trans with "[$Hrl] [$]").
  Qed.

  Lemma wbwp_very_awkward_self_apply :
    ⊢ WBWP very_awkward_self_apply {{v, ⌜v = #1⌝}}.
  Proof.
    rewrite /very_awkward_self_apply.
    wbwp_apply wbwp_very_awkward; first done.
    iIntros (f) "#Hf".
    wbwp_pures.
    wbwp_apply "Hf"; last done.
    iIntros "!#" (Φ) "_ HΦ".
    wbwp_pures.
    wbwp_apply "Hf"; last first.
    { iIntros; wbwp_pures; iApply wbwp_value; iApply "HΦ"; done. }
    iIntros "!#" (Ψ) "_ HΨ".
    wbwp_pures.
    iApply wbwp_value.
    iApply "HΨ"; done.
  Qed.

End very_awkward.

Theorem very_awkward_self_apply_returns_one σ :
  adequate NotStuck very_awkward_self_apply σ (λ v _, v = #1).
Proof.
  set (Σ := #[heapΣ; STSΣ vae_sts]).
  apply (wbheap_adequacy Σ).
  iIntros (?) "?". iApply wbwp_very_awkward_self_apply.
Qed.
