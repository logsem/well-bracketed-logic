From iris.algebra Require Import auth gmap.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import adequacy.
From WBLogrel.heap_lang Require Import adequacy.
From iris.heap_lang Require Import lang notation.
From WBLogrel.heap_lang Require Import proofmode.
From WBLogrel Require Import oneshot.

Definition very_awkward : expr :=
  let: "l" := ref #0 in
  λ: "f", "l" <- #0;; "f" #();; "l" <- #1;; "f" #();; ! "l".

Definition very_awkward_self_apply : expr :=
  let: "f" := very_awkward in
  "f" (λ: <>, "f" (λ: <>, #());; #()).

Section very_awkward.
  Context `{!wbheapGS Σ} `{!oneshotG Σ}.

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
    iMod new_pending as (γ) "Hpen".
    iApply (wbwp_make_gstack _ _ γ); iIntros (n) "Hfr".
    iDestruct (gstack_frag_exists with "Hfr") as "#Hx".
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ s, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗
               ((pending γ ∗ l ↦ #0) ∨ (shot γ ∗ l ↦ #1)))%I with "[Hpen Hfr Hl]") as "#Hinv".
    { iNext; iExists γ, _. iFrame "Hfr". iSplit; first by rewrite gtop_gsingleton. iLeft; iFrame. }
    iApply wbwp_value.
    iApply "HΦ".
    clear Φ.
    iIntros (g) "!#".
    iIntros (Φ) "#Hg HΦ".
    wbwp_pures.
    iApply (wbwp_get_gstack_full n with "[$]"); first done.
    iIntros (s) "Hfl".
    wbwp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as (γ1 s') ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ v ∗ (pending γ1 ∨ shot γ1))%I with "[Hl]" as (?) "[Hl Hps]".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (new_pending) as (γ2) "Hpen2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    wbwp_store.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hpen2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _; iFrame "Hfr"; iSplit; first by rewrite gtop_gpush. iLeft; iFrame. }
    iModIntro.
    wbwp_pures.
    iAssert (|==> shot γ1)%I with "[Hps]" as ">#Hsh".
    { iDestruct "Hps" as "[Hp|Hs]"; last done. iApply shoot; done. }
    wbwp_bind (g _)%E.
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hg" $! (λ w, ⌜w = #()⌝)%I); done. }
    iIntros (?) "[Hfl ->] /=".
    wbwp_pures.
    wbwp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as (γ3 s') ">(Hfr & % & Hl)" "Hcl".
    iAssert (∃ v, l ↦ v)%I with "[Hl]" as (?) "Hl".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    wbwp_store.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists γ1, _; iFrame "Hfr". iSplit; first done. iRight; iFrame; done. }
    iModIntro. simpl.
    wbwp_pures.
    wbwp_bind (g _)%E.
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hg" $! (λ w, ⌜w = #()⌝)%I); done. }
    iIntros (?) "[Hfl ->]"; simplify_eq/=.
    wbwp_pures.
    iInv (nroot .@ "awk") as (γ4 s') ">(Hfr & % & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct "Hl" as "[[Hp _]|[_ Hl]]".
    { iExFalso; iApply shot_not_pending; done. }
    wbwp_load.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hfr Hl]") as "_".
    { iNext; iExists _, _; iFrame. iSplit; first done. iRight; iFrame; done. }
    iModIntro.
    iFrame. iApply "HΦ"; done.
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
  set (Σ := #[heapΣ; oneshotΣ]).
  apply (wbheap_adequacy Σ).
  iIntros (?) "?". iApply wbwp_very_awkward_self_apply.
Qed.
