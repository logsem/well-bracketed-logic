From iris.algebra Require Import auth gmap.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import adequacy.
From WBLogic.heap_lang Require Import adequacy.
From iris.heap_lang Require Import lang notation.
From WBLogic.heap_lang Require Import proofmode.
From WBLogic Require Import oneshot.

Definition awkward : expr :=
  let: "l" := ref #0 in
  λ: "f", "l" <- #1;; "f" #();; ! "l".

Definition awkward_self_apply : expr :=
  let: "f" := awkward in
  "f" (λ: <>, "f" (λ: <>, #());; #()).

Section awkward.
  Context `{!wbheapGS Σ} `{!oneshotG Σ}.

  Lemma wbwp_awkward :
    ⊢ {WB{{ True }}}
      awkward
      {{{(f : val), RET f;
          ∀ (g : val),
            {WB{{ {WB{{ True }}} g #() {{{ RET #(); True }}} }}} f g {{{ RET #1; True }}}
      }}}.
  Proof.
    rewrite /awkward.
    iIntros (Φ) "_ !# HΦ".
    wbwp_alloc l as "Hl".
    wbwp_pures.
    iMod new_pending as (γ) "Hpen".
    iMod (inv_alloc
            (nroot .@ "awk") _
            ((pending γ ∗ l ↦ #0) ∨ (shot γ ∗ l ↦ #1))%I with "[Hpen Hl]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    iApply wbwp_value.
    iApply "HΦ".
    clear Φ.
    iIntros (g) "!#".
    iIntros (Φ) "#Hg HΦ".
    wbwp_pures.
    wbwp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as ">Hl" "Hcl".
    iAssert (∃ v, l ↦ v ∗ (pending γ ∨ shot γ))%I with "[Hl]" as (?) "[Hl Hps]".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iAssert (|==> shot γ)%I with "[Hps]" as ">#Hsh".
    { iDestruct "Hps" as "[Hp|Hs]"; last done. iApply shoot; done. }
    wbwp_store.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hl]") as "_".
    { iNext; iRight; iFrame; done. }
    iModIntro.
    wbwp_pures.
    wbwp_apply "Hg"; first done.
    iIntros "_".
    wbwp_pures.
    iInv (nroot .@ "awk") as ">Hl" "Hcl".
    iDestruct "Hl" as "[[Hp _]|[_ Hl]]".
    { iExFalso; iApply shot_not_pending; done. }
    wbwp_load.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hl]") as "_".
    { iNext; iRight; iFrame; done. }
    iModIntro.
    iFrame. iApply "HΦ"; done.
  Qed.

  Lemma wbwp_awkward_self_apply :
    ⊢ WBWP awkward_self_apply {{v, ⌜v = #1⌝}}.
  Proof.
    rewrite /awkward_self_apply.
    wbwp_apply wbwp_awkward; first done.
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

End awkward.

Theorem awkward_self_apply_returns_one σ :
  adequate NotStuck awkward_self_apply σ (λ v _, v = #1).
Proof.
  set (Σ := #[heapΣ; oneshotΣ]).
  apply (wbheap_adequacy Σ).
  iIntros (?) "?". iApply wbwp_awkward_self_apply.
Qed.
