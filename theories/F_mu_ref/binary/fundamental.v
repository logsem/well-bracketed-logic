From iris.algebra Require Import list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export lifting.
From WBLogrel.F_mu_ref.binary Require Export logrel rules.
From iris.prelude Require Import options.

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ, ghost_regG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).

  Definition bin_log_related (Γ : list type) (e e' : expr) (τ : type) : iProp Σ :=
    tc_opaque (□ ∀ Δ vvs,
      spec_ctx ∧ ⟦ Γ ⟧* Δ vvs -∗
      ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]))%I.

  Global Instance: ∀ Γ e e' τ, Persistent (bin_log_related Γ e e' τ).
  Proof. rewrite/bin_log_related /=. apply _. Qed.

End bin_log_def.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{heapIG Σ, cfgSG Σ, ghost_regG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
  Implicit Types e : expr.
  Implicit Types Δ : listO D.
  Implicit Type τi : listO D -n> D.
  Local Hint Resolve to_of_val : core.

  Lemma bin_expr_rel_bind K K' τi1 τi2 Δ e e' :
    interp_expr τi1 Δ (e, e') -∗
    (∀ v v', τi1 Δ (v, v') -∗ interp_expr τi2 Δ (fill K (of_val v), fill K' (of_val v'))) -∗
    interp_expr τi2 Δ (fill K e, fill K' e').
  Proof.
    iIntros "Hee Hkk".
    iIntros (M j Krs) "Hreg Hj /=".
    iApply (wp_bind (fill K)).
    rewrite -fill_app.
    iApply (wp_wand with "[- Hkk]"); first by iApply ("Hee" with "Hreg Hj").
    iIntros (v); simpl.
    iDestruct 1 as (v' N1) "[Hreg [Hj #Hvv]]".
    rewrite fill_app.
    iApply ("Hkk" with "[$] [$] [$]").
  Qed.

  Lemma bin_val_rel_bin_expr_rel v v' τi Δ :
    τi Δ (v, v') -∗ interp_expr τi Δ (of_val v, of_val v').
  Proof.
    iIntros "#?".
    iIntros (M j Krs) "Hreg Hj /=".
    iApply wp_value.
    iExists _, _; iFrame; done.
  Qed.

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Γ e e' τ} Δ vvs M j K :
    Γ ⊨ e ≤log≤ e' : τ -∗
    spec_ctx ∗ ⟦ Γ ⟧* Δ vvs ∗ ghost_reg_full M ∗ j ⤇ fill K (e'.[env_subst (vvs.*2)])
    -∗ WP e.[env_subst (vvs.*1)] {{ v, ∃ v' M',
        ghost_reg_full M' ∗ j ⤇ fill K (of_val v') ∗ interp τ Δ (v, v') }}.
  Proof.
    iIntros "#Hee (#Hspec & #HΓ & Hreg & Hj)".
    iSpecialize ("Hee" $! Δ vvs with "[$]").
    iApply (wp_wand with "[-]"); first by iApply ("Hee" with "Hreg Hj").
    iIntros (v) "?"; done.
  Qed.

  Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → ⊢ Γ ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (? Δ vvs) "!# #(Hs & HΓ)". iIntros (M j K) "Hreg Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[Heq ?]"; first done.
    iDestruct "Heq" as %Heq.
    erewrite !env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    iApply wp_value; iExists _, _; iFrame; done.
  Qed.

  Lemma bin_log_related_unit Γ : ⊢ Γ ⊨ Unit ≤log≤ Unit : TUnit.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (M j K) "Hreg Hj /=".
    iApply wp_value. iExists UnitV, _; iFrame; eauto.
  Qed.

  Lemma bin_log_related_nat Γ n : ⊢ Γ ⊨ #n n ≤log≤ #n n : TNat.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (M j K) "Hreg Hj /=".
    iApply wp_value. iExists (#nv _), _; iFrame; eauto.
  Qed.

  Lemma bin_log_related_bool Γ b : ⊢ Γ ⊨ #♭ b ≤log≤ #♭ b : TBool.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (M j K) "Hreg Hj /=".
    iApply wp_value. iExists (#♭v _), _; iFrame; eauto.
  Qed.

  Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [PairLCtx _] [PairLCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iApply (bin_expr_rel_bind [PairRCtx _] [PairRCtx _]); first by iApply "IH2"; iFrame "#".
    iIntros (w w') "Hww /=".
    iApply (bin_val_rel_bin_expr_rel (PairV _ _) (PairV _ _)); simpl.
    iExists _, _; repeat iSplit; eauto; simpl; done.
  Qed.

  Lemma bin_log_related_fst Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [FstCtx] [FstCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct "Hvv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq/=.
    iIntros (M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_fst with "[$]") as "Hw"; eauto.
    iApply wp_value. iExists _, _; iFrame; done.
  Qed.

  Lemma bin_log_related_snd Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [SndCtx] [SndCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct "Hvv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq/=.
    iIntros (M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_snd with "[$]") as "Hw"; eauto.
    iApply wp_value. iExists _, _; iFrame; done.
  Qed.

  Lemma bin_log_related_injl Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : τ1 -∗ Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [InjLCtx] [InjLCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iApply (bin_val_rel_bin_expr_rel (InjLV _) (InjLV _)).
    iLeft; iExists (_, _); simpl; eauto.
  Qed.

  Lemma bin_log_related_injr Γ e e' τ1 τ2 :
      Γ ⊨ e ≤log≤ e' : τ2 -∗ Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [InjRCtx] [InjRCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iApply (bin_val_rel_bin_expr_rel (InjRV _) (InjRV _)).
    iRight; iExists (_, _); simpl; eauto.
  Qed.

  Lemma bin_log_related_case Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2 -∗
    τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3 -∗
    τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3 -∗
    Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [CaseCtx _ _] [CaseCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct "Hvv" as "[Hvv|Hvv]".
    - iDestruct "Hvv" as ([w w']) "[% Hw]"; simplify_eq/=.
      iIntros (M j K) "Hreg Hj /=".
      iApply wp_pure_step_later; eauto. iNext.
      iMod (step_case_inl with "[$]") as "Hj"; eauto.
      iAsimpl.
      iApply (bin_log_related_alt _ ((w,w') :: vvs) with "IH2"); iFrame; iFrame "#".
      iApply interp_env_cons; auto.
    - iDestruct "Hvv" as ([w w']) "[% Hw]"; simplify_eq/=.
      iIntros (M j K) "Hreg Hj /=".
      iApply wp_pure_step_later; eauto. iNext.
      iMod (step_case_inr with "[$]") as "Hj"; eauto.
      iAsimpl.
      iApply (bin_log_related_alt _ ((w,w') :: vvs) with "IH3"); iFrame; iFrame "#".
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_if Γ e0 e1 e2 e0' e1' e2' τ :
    Γ ⊨ e0 ≤log≤ e0' : TBool -∗
    Γ ⊨ e1 ≤log≤ e1' : τ -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [IfCtx _ _] [IfCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct "Hvv" as ([]) "[-> ->]".
    - iIntros (M j K) "Hreg Hj /=".
      iApply wp_pure_step_later; eauto. iNext.
      iMod (step_if_true with "[$]") as "Hj"; eauto.
      iAsimpl.
      iApply (bin_log_related_alt with "IH2"); iFrame; iFrame "#".
    - iIntros (M j K) "Hreg Hj /=".
      iApply wp_pure_step_later; eauto. iNext.
      iMod (step_if_false with "[$]") as "Hj"; eauto.
      iAsimpl.
      iApply (bin_log_related_alt with "IH3"); iFrame; iFrame "#".
  Qed.

  Lemma bin_log_related_nat_binop Γ op e1 e2 e1' e2' :
    Γ ⊨ e1 ≤log≤ e1' : TNat -∗
    Γ ⊨ e2 ≤log≤ e2' : TNat -∗
    Γ ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : binop_res_type op.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [BinOpLCtx _ _] [BinOpLCtx _ _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct "Hvv" as (n1) "[% %]"; simplify_eq/=.
    iApply (bin_expr_rel_bind [BinOpRCtx _ (NatV _)] [BinOpRCtx _ (NatV _)]);
        first by iApply "IH2"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct "Hvv" as (n2) "[% %]"; simplify_eq/=.
    iIntros (M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_nat_binop _ j K with "[$]") as "Hj"; eauto.
    iApply wp_value. iExists _, _; iFrame.
    destruct op; simpl; try destruct eq_nat_dec; try destruct le_dec;
      try destruct lt_dec; eauto.
  Qed.

  Lemma bin_log_related_rec Γ e e' τ1 τ2 :
    TArrow τ1 τ2 :: τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Rec e ≤log≤ Rec e' : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_val_rel_bin_expr_rel (RecV _) (RecV _)); simpl.
    iIntros "!#".
    iLöb as "IHL". iIntros ([v v']) "#Hiv /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    iIntros (M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iMod (step_rec _ _ _ _ (of_val v') v' with "[$]") as "Hz"; eauto.
    iAsimpl.
    change (Rec ?e) with (of_val (RecV e)).
    iApply (bin_log_related_alt _ ((_,_) :: (v,v') :: vvs) with "IH").
    iFrame; iFrame "#".
    rewrite !interp_env_cons; eauto.
  Qed.

  Lemma bin_log_related_lam Γ e e' τ1 τ2 :
    τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_val_rel_bin_expr_rel (LamV _) (LamV _)); simpl.
    iIntros "!#".
    iIntros ([v v']) "#Hiv /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    iIntros (M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iMod (step_lam _ _ _ _ (of_val v') v' with "[$]") as "Hz"; eauto.
    iAsimpl.
    iApply (bin_log_related_alt _ ((v,v') :: vvs) with "IH").
    iFrame; iFrame "#".
    rewrite !interp_env_cons; eauto.
  Qed.

  Lemma bin_log_related_letin Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    τ1 :: Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ LetIn e1 e2 ≤log≤ LetIn e1' e2': τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [LetInCtx _] [LetInCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    iIntros (M j K) "Hreg Hj /=".
    iMod (step_letin with "[$]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro.
    iAsimpl.
    iApply (bin_log_related_alt _ ((v, v') :: vvs) with "IH2").
    iFrame; iFrame "#".
    rewrite !interp_env_cons; eauto.
  Qed.

  Lemma bin_log_related_seq Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Seq e1 e2 ≤log≤ Seq e1' e2': τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [SeqCtx _] [SeqCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iIntros (M j K) "Hreg Hj /=".
    iMod (step_seq with "[$]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro.
    iApply (bin_log_related_alt with "IH2").
    iFrame; iFrame "#".
  Qed.

  Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ1 -∗
    Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [AppLCtx _] [AppLCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iApply (bin_expr_rel_bind [AppRCtx _] [AppRCtx _]); first by iApply "IH2"; iFrame "#".
    iIntros (w w') "Hww /=".
    iIntros (M j K) "Hreg Hj /=".
    iApply ("Hvv" $! (w, w') with "[$] Hreg"); iFrame.
  Qed.

  Lemma bin_log_related_tlam Γ e e' τ :
    (subst (ren (+1)) <$> Γ) ⊨ e ≤log≤ e' : τ -∗
    Γ ⊨ TLam e ≤log≤ TLam e' : TForall τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_val_rel_bin_expr_rel (TLamV _) (TLamV _)); simpl.
    iIntros "!#"; iIntros (τi M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; auto. iNext.
    iMod (step_tlam with "[$]") as "Hj"; eauto.
    iApply (bin_log_related_alt with "IH [$Hj $Hreg]"); iFrame "#"; [].
    rewrite interp_env_ren; auto.
  Qed.

  Lemma bin_log_related_tapp Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : TForall τ -∗ Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; simpl.
    iApply (bin_expr_rel_bind [TAppCtx] [TAppCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "Hvv /=".
    iApply interp_expr_change_type; first by intros; rewrite -interp_subst.
    iApply "Hvv".
  Qed.

  Lemma bin_log_related_pack Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : τ.[τ'/] -∗ Γ ⊨ Pack e ≤log≤ Pack e' : TExist τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [PackCtx] [PackCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "#Hvv /=".
    iApply (bin_val_rel_bin_expr_rel (PackV _) (PackV _)).
    rewrite -interp_subst.
    iIntros "!#".
    iExists _, (_, _); iSplit; done.
  Qed.

  Lemma bin_log_related_unpack Γ e1 e1' e2 e2' τ τ' :
    Γ ⊨ e1 ≤log≤ e1' : TExist τ -∗
    τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 ≤log≤ e2' : τ'.[ren (+1)] -∗
    Γ ⊨ UnpackIn e1 e2 ≤log≤ UnpackIn e1' e2' : τ'.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [UnpackInCtx _] [UnpackInCtx _]); first by iApply "IH1"; iFrame "#".
    simpl.
    iIntros (v v') "#Hvv /=".
    iDestruct "Hvv" as (τi (v1, v2) ?) "Hvv"; simplify_eq/=.
    iIntros (M j K) "Hreg Hj /=".
    iApply wp_pure_step_later; auto. iNext.
    iMod (step_pack with "[$]") as "Hj"; eauto.
    iAsimpl.
    iApply wp_wand_r; iSplitL.
    { iApply (bin_log_related_alt (τi :: Δ) ((v1, v2) :: vvs) with "IH2 [$Hj $Hreg]").
      iFrame "#".
      iApply interp_env_cons; iSplit; first done.
      by iApply interp_env_ren. }
    iIntros (w). iDestruct 1 as (v M') "[Hreg [Hj #Hv]]".
    iExists _, _; iFrame.
    by iApply (interp_weaken [] [_]); simpl.
  Qed.

  Lemma bin_log_related_fold Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/] -∗ Γ ⊨ Fold e ≤log≤ Fold e' : TRec τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [FoldCtx] [FoldCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "#Hvv /=".
    iApply (bin_val_rel_bin_expr_rel (FoldV _) (FoldV _)).
    rewrite fixpoint_interp_rec1_eq /= -interp_subst.
    iModIntro; iExists (_, _); eauto.
  Qed.

  Lemma bin_log_related_unfold Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : TRec τ -∗ Γ ⊨ Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [UnfoldCtx] [UnfoldCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "#Hvv /=".
    rewrite fixpoint_interp_rec1_eq /=.
    iDestruct "Hvv" as ([]) "[% #Hvv]"; simplify_eq/=.
    iIntros (M j K) "Hreg Hj /=".
    iMod (step_fold with "[$]") as "Hj"; eauto.
    iApply wp_pure_step_later; auto.
    iApply wp_value; iNext. iExists _, _; iFrame.
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_alloc Γ e e' τ :
      Γ ⊨ e ≤log≤ e' : τ -∗ Γ ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [AllocCtx] [AllocCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "#Hvv /=".
    iIntros (M j K) "Hreg Hj /=".
    iMod (step_alloc with "[$]") as (l') "[Hj Hl]"; eauto.
    iApply wp_fupd.
    iApply wp_alloc; eauto. iNext.
    iIntros (l) "Hl'".
    iMod (inv_alloc (logN .@ (l,l')) _ (∃ w : val * val,
      l ↦ᵢ w.1 ∗ l' ↦ₛ w.2 ∗ interp τ Δ w)%I with "[Hl Hl']") as "HN"; eauto.
    { by iNext; iExists (v, v'); iFrame. }
    iModIntro; iExists (LocV l'), _. iFrame. iExists (l, l'); eauto.
  Qed.

  Lemma bin_log_related_load Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : (Tref τ) -∗ Γ ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [LoadCtx] [LoadCtx]); first by iApply "IH"; iFrame "#".
    iIntros (v v') "#Hvv /=".
    iDestruct "Hvv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iIntros (M j K) "Hreg Hj /=".
    iInv (logN .@ (l,l')) as ([w w']) "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iApply (wp_load with "Hw1").
    iNext. iIntros "Hw1".
    iMod (step_load  with "[$]") as "[Hv Hw2]"; first by solve_ndisj.
    iMod ("Hclose" with "[Hw1 Hw2]") as "_".
    { iNext. iExists (w,w'); by iFrame. }
    iModIntro. iExists w', _; by iFrame.
  Qed.

  Lemma bin_log_related_store Γ e1 e2 e1' e2' τ :
    Γ ⊨ e1 ≤log≤ e1' : (Tref τ) -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)".
    iApply (bin_expr_rel_bind [StoreLCtx _] [StoreLCtx _]); first by iApply "IH1"; iFrame "#".
    iIntros (v v') "#Hvv /=".
    iDestruct "Hvv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply (bin_expr_rel_bind [StoreRCtx (LocV _)] [StoreRCtx (LocV _)]);
        first by iApply "IH2"; iFrame "#".
    iIntros (w w') "#Hww/=".
    iIntros (M j K) "Hreg Hj /=".
    iInv (logN .@ (l,l')) as ([v v']) "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iApply (wp_store with "Hv1"); auto using to_of_val.
    iNext. iIntros "Hw2".
    iMod (step_store with "[$]") as "[Hw Hv2]"; eauto; first by solve_ndisj.
    iMod ("Hclose" with "[Hw2 Hv2]") as "_".
    { by iNext; iExists (w, w'); simpl; iFrame. }
    iExists UnitV; iFrame; auto.
  Qed.

  Theorem binary_fundamental Γ e τ :
    Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e ≤log≤ e : τ.
  Proof.
    revert Γ e τ; fix IH 4; destruct 1.
    - iApply bin_log_related_var; done.
    - iApply bin_log_related_unit.
    - iApply bin_log_related_nat.
    - iApply bin_log_related_bool.
    - iApply bin_log_related_nat_binop; iApply IH; done.
    - iApply bin_log_related_pair; iApply IH; done.
    - iApply bin_log_related_fst; iApply IH; done.
    - iApply bin_log_related_snd; iApply IH; done.
    - iApply bin_log_related_injl; iApply IH; done.
    - iApply bin_log_related_injr; iApply IH; done.
    - iApply bin_log_related_case; iApply IH; done.
    - iApply bin_log_related_if; iApply IH; done.
    - iApply bin_log_related_rec; iApply IH; done.
    - iApply bin_log_related_lam; iApply IH; done.
    - iApply bin_log_related_letin; iApply IH; done.
    - iApply bin_log_related_seq; iApply IH; done.
    - iApply bin_log_related_app; iApply IH; done.
    - iApply bin_log_related_tlam; iApply IH; done.
    - iApply bin_log_related_tapp; iApply IH; done.
    - iApply bin_log_related_pack; iApply IH; done.
    - iApply bin_log_related_unpack; iApply IH; done.
    - iApply bin_log_related_fold; iApply IH; done.
    - iApply bin_log_related_unfold; iApply IH; done.
    - iApply bin_log_related_alloc; iApply IH; done.
    - iApply bin_log_related_load; iApply IH; done.
    - iApply bin_log_related_store; iApply IH; done.
  Qed.
End fundamental.
