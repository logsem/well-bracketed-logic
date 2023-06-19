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

Definition factorial : val :=
  rec: "fact" "n" := if: "n" = #0 then #1 else "n" * ("fact" ("n" - #1)).

Definition call_fact_across : expr :=
  let: "b" := ref #true in
  let: "c" := ref NONE in
  let: "wait" := rec: "w" <> := if: ! "c" = NONE then "w" #() else #() in
  λ: <>, if: ! "b" then "b"  <- #false;; Fork (factorial #1000000) else "wait" #().

Definition very_akward_call_fact_across : expr :=
  let: "g" := call_fact_across in
  let: "h" := very_awkward in
  "h" "g".

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
    iApply (wbwp_make_gstack
              (λ n, inv (nroot .@ "awk") (∃ γ s, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗
               ((pending γ ∗ l ↦ #0) ∨ (shot γ ∗ l ↦ #1))) ∗ gstack_exists n)%I with "[Hl]").
    { iIntros (n Hn) "Hfl Hfr".
      iMod new_pending as (γ) "Hpen".
      iPoseProof (gstack_frag_exists with "Hfr") as "#?".
      iMod (gstack_push _ _ _ γ with "Hfl Hfr") as "[Hfl Hfr]".
      iMod (inv_alloc with "[- Hfl]"); last by iModIntro; iExists _; iFrame.
      iNext; iExists γ, _. iFrame "Hfr". iSplit; first by rewrite gtop_gsingleton. iLeft; iFrame. }
    iIntros (n Hn) "#[Hinv Hex]".
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

  (* a very weak spec just showing safety of factorial *)
  Lemma wp_factorial (n : Z) :
    ⊢ {{{ True }}} factorial #n {{{ (k : Z), RET #k; True }}}.
  Proof.
    rewrite /factorial.
    iLöb as "IH" forall (n).
    iIntros "!#" (Φ) "_ HΦ".
    wp_pures.
    destruct (decide (n = 0)) as [->|].
    - wp_pures. iApply "HΦ"; done.
    - rewrite bool_decide_eq_false_2; last by intros ?; simplify_eq.
      do 2 wp_pure.
      wp_apply "IH"; first done.
      iIntros (k) "_"; wp_pures.
      iModIntro.
      iApply "HΦ"; done.
  Qed.

  Lemma wp_call_fact_across :
    ⊢ {{{ True }}} call_fact_across {{{(f : val), RET f; {{{ True }}} f #() {{{ RET #(); True }}} }}}.
  Proof.
    iIntros "!#" (Φ) "_ HΦ".
    rewrite /call_fact_across.
    wp_alloc b as "Hb".
    wp_pures.
    wp_alloc c as "Hc".
    wp_pures.
    iMod (inv_alloc (nroot .@ "cfa") _
            (∃ (a : bool), b ↦ #a ∗ (c ↦ NONEV ∨ ∃ (n : nat), c ↦ SOMEV #n)) with "[Hb Hc]")
      as "#Hinv".
    { iExists _; iFrame. }
    iModIntro.
    iApply "HΦ".
    clear Φ.
    iIntros "!#" (Φ) "_ HΦ".
    wp_pures.
    wp_bind (! _)%E.
    iInv (nroot .@ "cfa") as (a) "[Hb Hc]".
    wp_load.
    iModIntro.
    iSplitL "Hb Hc"; first by iFrame "Hc"; eauto.
    destruct a.
    - wp_pures.
      wp_bind (_ <- _)%E.
      iInv (nroot .@ "cfa") as (a) "[Hb Hc]".
      wp_store.
      iModIntro.
      iSplitL "Hb Hc"; first by iFrame "Hc"; eauto.
      wp_pures.
      iApply wp_fork.
      + iNext; iApply wp_factorial; done.
      + iNext; iApply "HΦ"; done.
    - wp_pure.
      iLöb as "IH".
      wp_pures.
      wp_bind (! _)%E.
      iInv (nroot .@ "cfa") as (a) "[Hb [Hc|Hc]]".
      + wp_load.
        iModIntro.
        iSplitL "Hb Hc"; first by iExists _; iFrame.
        do 2 wp_pure.
        iApply "IH"; done.
      + iDestruct "Hc" as (?) "Hc".
        wp_load.
        iModIntro.
        iSplitL "Hb Hc"; first by iExists _; iFrame; eauto.
        wp_pures. iApply "HΦ"; done.
  Qed.

  Lemma wbwp_very_akward_call_fact_across :
    ⊢ WBWP very_akward_call_fact_across {{v, ⌜v = #1⌝ }}.
  Proof.
    rewrite /very_akward_call_fact_across.
    wbwp_bind call_fact_across.
    iApply wp_wbwp.
    iApply wp_call_fact_across; first done.
    iNext.
    iIntros (g) "#Hg".
    wbwp_pures.
    wbwp_apply wbwp_very_awkward; first done.
    iIntros (h) "#Hh".
    wbwp_pures.
    iApply "Hh"; last done.
    iIntros "!#" (Φ) "_ HΦ".
    iApply wp_wbwp.
    iApply "Hg"; done.
  Qed.

End very_awkward.

Theorem very_awkward_self_apply_returns_one σ :
  adequate NotStuck very_awkward_self_apply σ (λ v _, v = #1).
Proof.
  set (Σ := #[heapΣ; oneshotΣ]).
  apply (wbheap_adequacy Σ).
  iIntros (?) "?". iApply wbwp_very_awkward_self_apply.
Qed.

Theorem wbwp_very_akward_call_fact_across_returns_one σ :
  adequate NotStuck very_akward_call_fact_across σ (λ v _, v = #1).
Proof.
  set (Σ := #[heapΣ; oneshotΣ]).
  apply (wbheap_adequacy Σ).
  iIntros (?) "?". iApply wbwp_very_akward_call_fact_across.
Qed.
