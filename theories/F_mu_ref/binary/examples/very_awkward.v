From iris.algebra Require Import auth gmap.
From iris.unstable.algebra Require Import monotone.
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
    iIntros (j K) "Hj"; simpl.
    iApply (wbwp_bind (fill [LetInCtx _])).
    iApply wbwp_alloc; first done.
    iNext. iIntros (l) "Hl /=".
    iApply wbwp_pure_step_later; auto.
    iNext; iIntros "_". iAsimpl.
    iMod (exactly_alloc false) as (γ) "Hex".
    iApply (wbwp_make_gstack _ _ γ); iIntros (n) "Hfr".
    iDestruct (gstack_frag_exists with "Hfr") as "#Hx".
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ s b,  gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗ exactly γ b ∗
              if b then l ↦ᵢ (#nv 1) else l ↦ᵢ (#nv 0))%I with "[Hex Hfr Hl]") as "#Hinv".
    { iNext; iExists γ, _, false; iFrame; rewrite gtop_gsingleton //. }
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
    iInv (nroot .@ "awk") as (γ1 ? b) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %Hids1.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hex2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _, false; iFrame; rewrite gtop_gpush //. }
    iModIntro.
    iApply wbwp_pure_step_later; auto. iNext; iIntros "_".
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
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
    iInv (nroot .@ "awk") as (γ3 ? b2) "(>Hfr & >% & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ᵢ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iApply (wbwp_store with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists γ1, _, true; iFrame; done. }
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
    iInv (nroot .@ "awk") as (γ4 ? b3) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    iApply (wbwp_load with "[$]").
    iNext; iIntros "Hl".
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists _, _, true; iFrame; done. }
    iModIntro.
    iFrame "Hfl".
    iExists (#nv 1); iFrame; eauto.
  Qed.

  Lemma call_twice_return_one_very_awkward_refinement `{inG Σ (authUR (mraUR rel))} :
    ⊢ [] ⊨ call_twice_return_one ≤log≤ very_awkward : TArrow (TArrow TUnit TUnit) TNat.
  Proof.
    iIntros (? vs) "!# [#HE HΔ]".
    iDestruct (interp_env_length with "HΔ") as %Hlen; destruct vs; simplify_eq.
    iClear (Hlen) "HΔ". asimpl.
    iIntros (j K) "Hj"; simpl.
    iMod (step_alloc _ _ (LetInCtx _ :: K) with "[$]") as (l) "[Hj Hl]"; eauto.
    simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iAsimpl.
    iMod (exactly_alloc false) as (γ) "Hex".
    iApply (wbwp_make_gstack _ _ γ); iIntros (n) "Hfr".
    iDestruct (gstack_frag_exists with "Hfr") as "#Hx".
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ s b, gstack_frag n s ∗ ⌜gtop s = Some γ⌝ ∗ exactly γ b ∗
              if b then l ↦ₛ (#nv 1) else l ↦ₛ (#nv 0))%I with "[Hex Hfr Hl]") as "#Hinv".
    { iNext; iExists γ, _, false; iFrame; rewrite gtop_gsingleton; done. }
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
    iInv (nroot .@ "awk") as (γ1 ? b) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ₛ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %Hids1.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (gstack_push _ _ _ γ2 with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (step_store _ _ (SeqCtx _ :: K) with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hex2 Hfr Hl]") as "_".
    { iNext; iExists γ2, _, false; iFrame; rewrite gtop_gpush //. }
    iModIntro.
    simpl.
    iMod (do_step_pure with "[$]") as "Hj"; auto.
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
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
    iInv (nroot .@ "awk") as (γ3 ? b2) "(>Hfr & >% & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ₛ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq /=.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (step_store _ _ (SeqCtx _ :: K) with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists γ1, _, true; iFrame; done. }
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
    iInv (nroot .@ "awk") as (γ4 ? b3) "(>Hfr & >% & >Hex1 & Hl)" "Hcl".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    iMod "Hl".
    iMod (step_load with "[$]") as "[Hj Hl]"; eauto; first by solve_ndisj.
    iMod ("Hcl" with "[Hex1 Hfr Hl]") as "_".
    { iNext; iExists _, _, true; iFrame; done. }
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
  set (Σ := #[invΣ ; gen_heapΣ loc val ; soundness_binaryΣ; gstacksΣ; relΣ]).
  set (HG := soundness.soundness_unary_preIG Σ _ _ _).
  split.
  - eapply (binary_soundness Σ); auto using very_awkward_typed, call_twice_return_one_typed.
    intros; apply very_awkward_call_twice_return_one_refinement.
  -  eapply (binary_soundness Σ); auto using very_awkward_typed, call_twice_return_one_typed.
    intros; apply call_twice_return_one_very_awkward_refinement.
Qed.
