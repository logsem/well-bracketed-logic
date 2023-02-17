From iris.algebra Require Import auth gmap.
From iris.base_logic Require Import invariants.
From iris.unstable.algebra Require Import monotone.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import adequacy.
From WBLogrel.heap_lang Require Import adequacy.
From iris.heap_lang Require Import lang notation.
From WBLogrel.heap_lang Require Import proofmode.

Definition very_awkward : expr :=
  let: "l" := ref #0 in
  λ: "f", "l" <- #0;; "f" #();; "l" <- #1;; "f" #();; ! "l".

Definition very_awkward_self_apply : expr :=
  let: "f" := very_awkward in
  "f" (λ: <>, "f" (λ: <>, #());; #()).

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
  Context `{!wbheapGS Σ}.

  Lemma wbwp_very_awkward `{!inG Σ (authUR (mraUR rel))} :
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
    iMod (exactly_alloc false) as (γ) "Hex".
    iApply (wbwp_make_gstack _ _ γ); iIntros (n) "Hfrg".
    iDestruct (gstack_frag_exists with "Hfrg") as "#Hx".
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ s b, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗ exactly γ b ∗
               if b then l ↦ #1 else l ↦ #0)%I with "[Hex Hfrg Hl]") as "#Hinv".
    { iNext; iExists γ, _, false; iFrame; rewrite gtop_gsingleton; done. }
    iApply wbwp_value.
    iApply "HΦ".
    clear Φ.
    iIntros (g) "!#".
    iIntros (Φ) "#Hg HΦ".
    wbwp_pures.
    iApply (wbwp_get_gstack_full n with "[$]"); first done.
    iIntros (s) "Hfl".
    wbwp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as (γ1 s' b) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    wbwp_store.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hex2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _, false; iFrame; rewrite gtop_gpush; done. }
    iModIntro.
    wbwp_pures.
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
    wbwp_bind (g _)%E.
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hg" $! (λ w, ⌜w = #()⌝)%I); done. }
    iIntros (?) "[Hfl ->] /=".
    wbwp_pures.
    wbwp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as (γ3 s' b2) "(>Hfr & >%Hγ3 & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    wbwp_store.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists γ1, _, true; iFrame; done. }
    iModIntro. simpl.
    wbwp_pures.
    wbwp_bind (g _)%E.
    iApply (wbwp_wand with "[Hfl]").
    { iApply (wbwp_mend with "Hfl").
      replace ((∅ ∪ {[n]}) ∖ {[n]}) with (∅ : gset ghost_id) by set_solver.
      iApply ("Hg" $! (λ w, ⌜w = #()⌝)%I); done. }
    iIntros (?) "[Hfl ->]"; simplify_eq/=.
    wbwp_pures.
    iInv (nroot .@ "awk") as (γ4 ? b3) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    wbwp_load.
    iApply wbwp_value.
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists _, _, true; iFrame; done. }
    iModIntro.
    iFrame. iApply "HΦ"; done.
  Qed.

  Lemma wbwp_very_awkward_self_apply `{!inG Σ (authUR (mraUR rel))} :
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
  set (Σ := #[heapΣ; relΣ]).
  apply (wbheap_adequacy Σ).
  iIntros (?) "?". iApply wbwp_very_awkward_self_apply.
Qed.
