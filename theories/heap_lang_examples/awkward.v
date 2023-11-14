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
  Context `{!heapGS Σ} `{!oneshotG Σ}.

  Lemma wp_awkward :
    ⊢ {{{ True }}}
      awkward
      {{{(f : val), RET f;
          ∀ (g : val),
            {{{ {{{ True }}} g #() {{{ RET #(); True }}} }}} f g {{{ RET #1; True }}}
      }}}.
  Proof.
    rewrite /awkward.
    iIntros (Φ) "_ !# HΦ".
    wp_alloc l as "Hl".
    wp_pures.
    iMod new_pending as (γ) "Hpen".
    iMod (inv_alloc
            (nroot .@ "awk") _
            ((pending γ ∗ l ↦ #0) ∨ (shot γ ∗ l ↦ #1))%I with "[Hpen Hl]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    iModIntro; iApply "HΦ".
    clear Φ.
    iIntros (g) "!#".
    iIntros (Φ) "#Hg HΦ".
    wp_pures.
    wp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as ">Hl" "Hcl".
    iAssert (∃ v, l ↦ v ∗ (pending γ ∨ shot γ))%I with "[Hl]" as (?) "[Hl Hps]".
    { iDestruct "Hl" as "[[? ?]|[? ?]]"; iExists _; iFrame. }
    iAssert (|==> shot γ)%I with "[Hps]" as ">#Hsh".
    { iDestruct "Hps" as "[Hp|Hs]"; last done. iApply shoot; done. }
    wp_store.
    iMod ("Hcl" with "[Hl]") as "_".
    { iNext; iRight; iFrame; done. }
    iModIntro.
    wp_pures.
    wp_apply "Hg"; first done.
    iIntros "_".
    wp_pures.
    iInv (nroot .@ "awk") as ">Hl" "Hcl".
    iDestruct "Hl" as "[[Hp _]|[_ Hl]]".
    { iExFalso; iApply shot_not_pending; done. }
    wp_load.
    iMod ("Hcl" with "[Hl]") as "_".
    { iNext; iRight; iFrame; done. }
    iModIntro.
    iFrame. iApply "HΦ"; done.
  Qed.

  Lemma wp_awkward_self_apply :
    ⊢ WP awkward_self_apply {{v, ⌜v = #1⌝}}.
  Proof.
    rewrite /awkward_self_apply.
    wp_apply wp_awkward; first done.
    iIntros (f) "#Hf".
    wp_pures.
    wp_apply "Hf"; last done.
    iIntros "!#" (Φ) "_ HΦ".
    wp_pures.
    wp_apply "Hf"; last first.
    { iIntros; wp_pures; iApply "HΦ"; done. }
    iIntros "!#" (Ψ) "_ HΨ".
    wp_pures.
    iApply "HΨ"; done.
  Qed.

End awkward.

Theorem awkward_self_apply_returns_one σ :
  adequate NotStuck awkward_self_apply σ (λ v _, v = #1).
Proof.
  set (Σ := #[heapΣ; oneshotΣ]).
  apply (heap_adequacy Σ).
  iIntros (?) "?". iApply wp_awkward_self_apply.
Qed.
