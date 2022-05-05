From iris.algebra Require Import list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export lifting.
From WBLogrel.F_mu_ref.binary Require Export logrel rules.
From iris.prelude Require Import options.

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ}.
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
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
  Implicit Types e : expr.
  Implicit Types Δ : listO D.
  Local Hint Resolve to_of_val : core.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]");
      [iApply Hp; iFrame "#"; trivial|];
    iIntros (v); iDestruct 1 as (w) Hv; simpl.

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Γ e e' τ} Δ vvs j K :
    Γ ⊨ e ≤log≤ e' : τ -∗
    spec_ctx ∗ ⟦ Γ ⟧* Δ vvs ∗ j ⤇ fill K (e'.[env_subst (vvs.*2)])
    -∗ WP e.[env_subst (vvs.*1)] {{ v, ∃ v',
        j ⤇ fill K (of_val v') ∗ interp τ Δ (v, v') }}.
  Proof.
    iIntros "#Hlog (#Hs & HΓ & Hj)".
    iApply ("Hlog" with "[HΓ]"); iFrame; eauto.
  Qed.

  Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → ⊢ Γ ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (? Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[Heq ?]"; first done.
    iDestruct "Heq" as %Heq.
    erewrite !env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_unit Γ : ⊢ Γ ⊨ Unit ≤log≤ Unit : TUnit.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists UnitV; eauto.
  Qed.

  Lemma bin_log_related_nat Γ n : ⊢ Γ ⊨ #n n ≤log≤ #n n : TNat.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (#nv _); eauto.
  Qed.

  Lemma bin_log_related_bool Γ b : ⊢ Γ ⊨ #♭ b ≤log≤ #♭ b : TBool.
  Proof.
    iIntros (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (#♭v _); eauto.
  Qed.

  Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)". iIntros (j K) "Hj /=".
    smart_wp_bind (PairLCtx e2.[env_subst _]) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j ((PairLCtx e2'.[env_subst _]) :: K) with "IH1").
    smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
      (bin_log_related_alt _ _ j ((PairRCtx v') :: K) with "IH2").
    iApply wp_value. iExists (PairV v' w'); iFrame "Hw".
    iExists (v, v'), (w, w'); simpl; repeat iSplit; trivial.
  Qed.

  Lemma bin_log_related_fst Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (FstCtx) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j (FstCtx :: K) with "[IH]"); cbn.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_fst with "[Hs Hv]") as "Hw"; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_snd Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : TProd τ1 τ2 -∗ Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (SndCtx) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j (SndCtx :: K) with "IH"); cbn.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iApply wp_pure_step_later; eauto. iNext.
    iMod (step_snd with "[Hs Hv]") as "Hw"; eauto.
    iApply wp_value; eauto.
  Qed.

  Lemma bin_log_related_injl Γ e e' τ1 τ2 :
    Γ ⊨ e ≤log≤ e' : τ1 -∗ Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j (InjLCtx :: K) with "IH"); cbn.
    iApply wp_value. iExists (InjLV v'); iFrame "Hv".
    iLeft; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_injr Γ e e' τ1 τ2 :
      Γ ⊨ e ≤log≤ e' : τ2 -∗ Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j (InjRCtx :: K) with "IH"); cbn.
    iApply wp_value. iExists (InjRV v'); iFrame "Hv".
    iRight; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_case Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2 -∗
    τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3 -∗
    τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3 -∗
    Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (CaseCtx _ _) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j ((CaseCtx _ _) :: K) with "IH1"); cbn.
    iDestruct "Hiv" as "[Hiv|Hiv]";
    iDestruct "Hiv" as ([w w']) "[% Hw]"; simplify_eq.
    - iApply fupd_wp.
      iMod (step_case_inl with "[Hs Hv]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. fold of_val. iModIntro. iNext.
      asimpl.
      iApply (bin_log_related_alt _ ((w,w') :: vvs) with "IH2").
      repeat iSplit; eauto.
      iApply interp_env_cons; auto.
    - iApply fupd_wp.
      iMod (step_case_inr with "[Hs Hv]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. fold of_val. iModIntro. iNext.
      asimpl.
      iApply (bin_log_related_alt _ ((w,w') :: vvs) with "IH3").
      repeat iSplit; eauto.
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_if Γ e0 e1 e2 e0' e1' e2' τ :
    Γ ⊨ e0 ≤log≤ e0' : TBool -∗
    Γ ⊨ e1 ≤log≤ e1' : τ -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (IfCtx _ _) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j ((IfCtx _ _) :: K) with "IH1"); cbn.
    iDestruct "Hiv" as ([]) "[% %]"; simplify_eq/=; iApply fupd_wp.
    - iMod (step_if_true _ j K with "[-]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto. iModIntro. iNext.
      iApply (bin_log_related_alt with "IH2"); eauto.
    - iMod (step_if_false _ j K with "[-]") as "Hz"; eauto.
      iApply wp_pure_step_later; auto.
      iModIntro. iNext.
      iApply (bin_log_related_alt with "IH3"); eauto.
  Qed.

  Lemma bin_log_related_nat_binop Γ op e1 e2 e1' e2' :
    Γ ⊨ e1 ≤log≤ e1' : TNat -∗
    Γ ⊨ e2 ≤log≤ e2' : TNat -∗
    Γ ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : binop_res_type op.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (BinOpLCtx _ _) v v' "[Hv #Hiv]"
                  (bin_log_related_alt _ _ j ((BinOpLCtx _ _) :: K) with "IH1"); cbn.
    smart_wp_bind (BinOpRCtx _ _) w w' "[Hw #Hiw]"
                  (bin_log_related_alt _ _ j ((BinOpRCtx _ _) :: K) with "IH2"); cbn.
    iDestruct "Hiv" as (n) "[% %]"; simplify_eq/=.
    iDestruct "Hiw" as (n') "[% %]"; simplify_eq/=.
    iApply fupd_wp.
    iMod (step_nat_binop _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro. iNext.
    iApply wp_value. iExists _; iSplitL; eauto.
    destruct op; simpl; try destruct eq_nat_dec; try destruct le_dec;
      try destruct lt_dec; eauto.
  Qed.

  Lemma bin_log_related_rec Γ e e' τ1 τ2 :
    TArrow τ1 τ2 :: τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Rec e ≤log≤ Rec e' : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (RecV _). iIntros "{$Hj} !#".
    iLöb as "IHL". iIntros ([v v']) "#Hiv". iIntros (j' K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iApply fupd_wp.
    iMod (step_rec _ j' K' _ (of_val v') v' with "[-]") as "Hz"; eauto.
    asimpl. change (Rec ?e) with (of_val (RecV e)).
    iApply (bin_log_related_alt _ ((_,_) :: (v,v') :: vvs) with "IH").
    repeat iSplit; eauto.
    iModIntro.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_lam Γ e e' τ1 τ2 :
    τ1 :: Γ ⊨ e ≤log≤ e' : τ2 -∗
    Γ ⊨ Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (LamV _). iIntros "{$Hj} !#".
    iIntros ([v v']) "#Hiv". iIntros (j' K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iApply fupd_wp.
    iMod (step_lam _ j' K' _ (of_val v') v' with "[-]") as "Hz"; eauto.
    asimpl. iFrame "#". change (Lam ?e) with (of_val (LamV e)).
    iApply (bin_log_related_alt _  ((v,v') :: vvs) with "IH").
    repeat iSplit; eauto.
    iModIntro.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_letin Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    τ1 :: Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ LetIn e1 e2 ≤log≤ LetIn e1' e2': τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (LetInCtx _) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j ((LetInCtx _) :: K) with "IH1"); cbn.
    iMod (step_letin _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro.
    asimpl.
    iApply (bin_log_related_alt _ ((v, v') :: vvs) with "IH2").
    repeat iSplit; eauto.
    rewrite !interp_env_cons; iSplit; try iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_seq Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : τ1 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ2 -∗
    Γ ⊨ Seq e1 e2 ≤log≤ Seq e1' e2': τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (SeqCtx _) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j ((SeqCtx _) :: K) with "IH1"); cbn.
    iMod (step_seq _ j K with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto. iModIntro.
    asimpl.
    iApply (bin_log_related_alt with "IH2"); repeat iSplit; eauto.
  Qed.

  Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2 :
    Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2 -∗
    Γ ⊨ e2 ≤log≤ e2' : τ1 -∗
    Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (AppLCtx (e2.[env_subst (vvs.*1)])) v v' "[Hv #Hiv]"
      (bin_log_related_alt
        _ _ j (((AppLCtx (e2'.[env_subst (vvs.*2)]))) :: K) with "IH1"); cbn.
    smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
      (bin_log_related_alt _ _ j ((AppRCtx v') :: K) with "IH2"); cbn.
    iApply ("Hiv" $! (w, w') with "Hiw"); simpl; eauto.
  Qed.

  Lemma bin_log_related_tlam Γ e e' τ :
    (subst (ren (+1)) <$> Γ) ⊨ e ≤log≤ e' : τ -∗
    Γ ⊨ TLam e ≤log≤ TLam e' : TForall τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply wp_value. iExists (TLamV _).
    iIntros "{$Hj} /= !#"; iIntros (τi j' K') "Hv /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply fupd_wp.
    iMod (step_tlam _ j' K' (e'.[env_subst (vvs.*2)]) with "[-]") as "Hz"; eauto.
    iApply (bin_log_related_alt with "IH"); repeat iSplit; eauto.
    iModIntro.
    rewrite interp_env_ren; auto.
  Qed.

  Lemma bin_log_related_tapp Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : TForall τ -∗ Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (TAppCtx) v v' "[Hj #Hv]"
      (bin_log_related_alt _ _ j (TAppCtx :: K) with "IH"); cbn.
    rewrite -/interp.
    iApply wp_wand_r; iSplitL.
    { iSpecialize ("Hv" $! (interp τ' Δ)). iApply "Hv"; eauto. }
    iIntros (w). iDestruct 1 as (w') "[Hw Hiw]".
    iExists _; rewrite -interp_subst; eauto.
  Qed.

  Lemma bin_log_related_pack Γ e e' τ τ' :
    Γ ⊨ e ≤log≤ e' : τ.[τ'/] -∗ Γ ⊨ Pack e ≤log≤ Pack e' : TExist τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (PackCtx) v v' "[Hj #Hv]"
      (bin_log_related_alt _ _ j (PackCtx :: K) with "IH"); cbn.
    iApply wp_value.
    iExists (PackV _); iFrame.
    iModIntro.
    rewrite -interp_subst.
    iExists (interp _ Δ), (_, _); iSplit; done.
  Qed.

  Lemma bin_log_related_unpack Γ e1 e1' e2 e2' τ τ' :
    Γ ⊨ e1 ≤log≤ e1' : TExist τ -∗
    τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 ≤log≤ e2' : τ'.[ren (+1)] -∗
    Γ ⊨ UnpackIn e1 e2 ≤log≤ UnpackIn e1' e2' : τ'.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (UnpackInCtx _) v v' "[Hj #Hv]"
      (bin_log_related_alt _ _ j (UnpackInCtx _ :: K) with "IH1"); cbn.
    rewrite -/interp.
    iDestruct "Hv" as (τi (v1, v2) Hvv) "#Hvv"; simplify_eq /=.
    iApply wp_pure_step_later; auto. iNext.
    iApply fupd_wp.
    iMod (step_pack with "[Hj]") as "Hj"; eauto.
    asimpl.
    iModIntro.
    iApply wp_wand_r; iSplitL.
    { iApply (bin_log_related_alt (τi :: Δ) ((v1, v2) :: vvs) with "IH2 [$Hj]").
      iFrame; iFrame "#".
      iApply interp_env_cons; iSplit; first done.
      by iApply interp_env_ren. }
    iIntros (w). iDestruct 1 as (v) "[Hj #Hv]".
    iExists _; iFrame.
    by iApply (interp_weaken [] [_]); simpl.
  Qed.

  Lemma bin_log_related_fold Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/] -∗ Γ ⊨ Fold e ≤log≤ Fold e' : TRec τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply (wp_bind (fill [FoldCtx])); iApply wp_wand_l; iSplitR;
        [|iApply (bin_log_related_alt _ _ j (FoldCtx :: K) with "IH");
          simpl; repeat iSplitR; trivial].
    iIntros (v); iDestruct 1 as (w) "[Hv #Hiv]".
    iApply wp_value. iExists (FoldV w); iFrame "Hv".
    rewrite fixpoint_interp_rec1_eq /= -interp_subst.
    iModIntro; iExists (_, _); eauto.
  Qed.

  Lemma bin_log_related_unfold Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : TRec τ -∗ Γ ⊨ Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    iApply (wp_bind (fill [UnfoldCtx])); iApply wp_wand_l; iSplitR;
        [|iApply (bin_log_related_alt _ _ j (UnfoldCtx :: K) with "IH");
          simpl; repeat iSplitR; trivial].
    iIntros (v). iDestruct 1 as (v') "[Hw #Hiw]".
    rewrite /= fixpoint_interp_rec1_eq /=.
    change (fixpoint _) with (interp (TRec τ) Δ).
    iDestruct "Hiw" as ([w w']) "#[% Hiz]"; simplify_eq/=.
    iApply fupd_wp.
    iMod (step_fold _ j K (of_val w') w' with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; auto.
    iModIntro. iApply wp_value. iNext; iExists _; iFrame "Hz".
      by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_alloc Γ e e' τ :
      Γ ⊨ e ≤log≤ e' : τ -∗ Γ ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (AllocCtx) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j (AllocCtx :: K) with "IH").
    iApply fupd_wp.
    iMod (step_alloc _ j K (of_val v') v' with "[-]") as (l') "[Hj Hl]"; eauto.
    iApply wp_atomic; eauto.
    iApply wp_alloc; eauto. do 2 iModIntro. iNext.
    iIntros (l) "Hl'".
    iMod (inv_alloc (logN .@ (l,l')) _ (∃ w : val * val,
      l ↦ᵢ w.1 ∗ l' ↦ₛ w.2 ∗ interp τ Δ w)%I with "[Hl Hl']") as "HN"; eauto.
    { iNext. iExists (v, v'); iFrame. iFrame "Hiv". }
    iModIntro; iExists (LocV l'). iFrame "Hj". iExists (l, l'); eauto.
  Qed.

  Lemma bin_log_related_load Γ e e' τ :
    Γ ⊨ e ≤log≤ e' : (Tref τ) -∗ Γ ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros "#IH" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j (LoadCtx :: K) with "IH").
    iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([w w']) "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    (* TODO: why can we eliminate the next modality here? ↑ *)
    iModIntro.
    iApply (wp_load with "Hw1").
    iNext. iIntros "Hw1".
    iMod (step_load  with "[Hv Hw2]") as "[Hv Hw2]";
      [solve_ndisj|by iFrame|].
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists (w,w'); by iFrame. }
    iModIntro. iExists w'; by iFrame.
  Qed.

  Lemma bin_log_related_store Γ e1 e2 e1' e2' τ :
    Γ ⊨ e1 ≤log≤ e1' : (Tref τ) -∗
    Γ ⊨ e2 ≤log≤ e2' : τ -∗
    Γ ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros "#IH1 #IH2" (Δ vvs) "!# #(Hs & HΓ)"; iIntros (j K) "Hj /=".
    smart_wp_bind (StoreLCtx _) v v' "[Hv #Hiv]"
      (bin_log_related_alt _ _ j ((StoreLCtx _) :: K) with "IH1").
    smart_wp_bind (StoreRCtx _) w w' "[Hw #Hiw]"
      (bin_log_related_alt _ _ j ((StoreRCtx _) :: K) with "IH2").
    iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iApply wp_atomic; eauto.
    iInv (logN .@ (l,l')) as ([v v']) "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro.
    iApply (wp_store with "Hv1"); auto using to_of_val.
    iNext. iIntros "Hw2".
    iMod (step_store with "[$Hs Hw Hv2]") as "[Hw Hv2]"; eauto;
    [solve_ndisj | by iFrame|].
    iMod ("Hclose" with "[Hw2 Hv2]").
    { iNext; iExists (w, w'); simpl; iFrame. iFrame "Hiw". }
    iExists UnitV; iFrame; auto.
  Qed.

  Theorem binary_fundamental Γ e τ :
    Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e ≤log≤ e : τ.
  Proof.
    induction 1.
    - iApply bin_log_related_var; done.
    - iApply bin_log_related_unit.
    - iApply bin_log_related_nat.
    - iApply bin_log_related_bool.
    - iApply bin_log_related_nat_binop; done.
    - iApply bin_log_related_pair; done.
    - iApply bin_log_related_fst; done.
    - iApply bin_log_related_snd; done.
    - iApply bin_log_related_injl; done.
    - iApply bin_log_related_injr; done.
    - iApply bin_log_related_case; done.
    - iApply bin_log_related_if; done.
    - iApply bin_log_related_rec; done.
    - iApply bin_log_related_lam; done.
    - iApply bin_log_related_letin; done.
    - iApply bin_log_related_seq; done.
    - iApply bin_log_related_app; done.
    - iApply bin_log_related_tlam; done.
    - iApply bin_log_related_tapp; done.
    - iApply bin_log_related_pack; done.
    - iApply bin_log_related_unpack; done.
    - iApply bin_log_related_fold; done.
    - iApply bin_log_related_unfold; done.
    - iApply bin_log_related_alloc; done.
    - iApply bin_log_related_load; done.
    - iApply bin_log_related_store; done.
  Qed.
End fundamental.
