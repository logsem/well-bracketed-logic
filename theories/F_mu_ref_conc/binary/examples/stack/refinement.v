From iris.algebra Require Import auth list.
From iris.program_logic Require Import adequacy ectxi_language.
From iris_examples.logrel.F_mu_ref_conc.binary Require Import soundness.
From iris_examples.logrel.F_mu_ref_conc.binary.examples Require Import lock.
From iris_examples.logrel.F_mu_ref_conc.binary.examples.stack Require Import
  CG_stack FG_stack stack_rules.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

Definition stackN : namespace := nroot .@ "stack".

Section Stack_refinement.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
  Implicit Types Δ : listO D.

  Lemma FG_CG_counter_refinement :
    ⊢ [] ⊨ FG_stack ≤log≤ CG_stack : TForall (TProd (TProd
           (TArrow (TVar 0) TUnit)
           (TArrow TUnit (TSum TUnit (TVar 0))))
           (TArrow (TArrow (TVar 0) TUnit) TUnit)).
  Proof.
    (* executing the preambles *)
    iIntros (Δ [|??]) "!# #[Hspec HΓ]"; iIntros (j K) "Hj"; last first.
    { iDestruct (interp_env_length with "HΓ") as %[=]. }
    iClear "HΓ". cbn -[FG_stack CG_stack].
    rewrite ?empty_env_subst /CG_stack /FG_stack.
    iApply wp_value; eauto.
    iExists (TLamV _); iFrame "Hj".
    clear j K. iModIntro. iIntros (τi j K) "Hj /=".
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iApply wp_pure_step_later; auto. iNext.
    iMod (steps_newlock _ j (LetInCtx _ :: K) with "[$Hj]")
      as (l) "[Hj Hl]"; eauto.
    iMod (do_step_pure _ j K with "[$Hj]") as "Hj"; eauto.
    simpl. iAsimpl.
    iMod (step_alloc  _ j (LetInCtx _ :: K) with "[$Hj]")
      as (stk') "[Hj Hstk']"; eauto.
    simpl.
    iMod (do_step_pure with "[$Hj]") as "Hj"; eauto.
    iAsimpl.
    iApply (wp_bind (fill [AllocCtx; AppRCtx (RecV _)]));
      iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
    iApply wp_alloc; first done. iNext; iIntros (istk) "Histk".
    iApply (wp_bind (fill [AppRCtx (RecV _)]));
      iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
    iApply wp_alloc; first done. iNext; iIntros (stk) "Hstk".
    simpl. iApply wp_pure_step_later; trivial. iNext. simpl.
    iAsimpl.
    iMod (mapsto_persist with "Histk") as "#Histk".
    (* establishing the invariant *)
    iAssert (StackLink τi (LocV istk, FoldV (InjLV UnitV))) with "[]" as "HLK".
    { rewrite StackLink_unfold.
      iExists _, _. iSplitR; simpl; trivial.
      iFrame "Histk". iLeft. iSplit; trivial. }
    iAssert ((∃ istk v, stk' ↦ₛ v
                      ∗ stk ↦ᵢ (LocV istk)
                      ∗ StackLink τi (LocV istk, v)
                      ∗ l ↦ₛ (#♭v false)
             )%I) with "[Hstk Hstk' HLK Hl]" as "Hinv".
    { iExists _, _. by iFrame "Hstk' Hstk Hl HLK". }
    iMod (inv_alloc stackN with "[Hinv]") as "#Hinv"; [iNext; iExact "Hinv"|].
    iClear (istk) "Histk HLK".
    (* splitting *)
    iApply wp_value; simpl; trivial.
    iExists (PairV (PairV (CG_locked_pushV _ _) (CG_locked_popV _ _)) (LamV _)).
    simpl. iAsimpl.
    rewrite CG_locked_push_of_val CG_locked_pop_of_val.
    Local Transparent CG_snap_iter. (* HACK *)
    iFrame "Hj".
    iExists (_, _), (_, _); iSplit; eauto.
    iSplit.
    (* refinement of push and pop *)
    - iExists (_, _), (_, _); iSplit; eauto. iSplit.
      + (* refinement of push *)
        iModIntro. clear j K. iIntros ( [v1 v2] ) "#Hrel". iIntros (j K) "Hj /=".
        rewrite -(FG_push_folding (Loc stk)).
        iLöb as "Hlat".
        rewrite {2}(FG_push_folding (Loc stk)).
        iApply wp_pure_step_later; auto using to_of_val.
        iNext.
        rewrite -(FG_push_folding (Loc stk)).
        iAsimpl.
        iApply (wp_bind (fill [LetInCtx _]));
          iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
        iInv stackN as (istk v) "[Hstk' [Hstk [HLK Hl]]]" "Hclose".
        iApply (wp_load with "Hstk"). iNext. iIntros "Hstk".
        iMod ("Hclose" with "[Hstk' HLK Hl Hstk]") as "_".
        { iNext. iExists _, _; by iFrame "Hstk' HLK Hl Hstk". }
        clear v.
        iApply wp_pure_step_later; auto using to_of_val.
        iModIntro. iNext. iAsimpl.
        iApply (wp_bind (fill [CasRCtx (LocV _) (LocV _); IfCtx _ _]));
          iApply wp_wand_l; iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
        iApply wp_alloc; simpl; trivial.
        iNext. iIntros (ltmp) "Hltmp".
        iApply (wp_bind (fill [IfCtx _ _]));
          iApply wp_wand_l; iSplitR; [iIntros (w) "H"; iExact "H"|].
        iInv stackN as (istk2 v) "[Hstk' [Hstk [HLK Hl]]]" "Hclose".
        (* deciding whether CAS will succeed or fail *)
        destruct (decide (istk = istk2)) as [|Hneq]; subst.
        * (* CAS succeeds *)
          (* In this case, the specification pushes *)
          iMod "Hstk'". iMod "Hl".
          iMod (steps_CG_locked_push _ j K with "[Hj Hl Hstk']")
            as "[Hj [Hstk' Hl]]"; first solve_ndisj.
          { rewrite CG_locked_push_of_val. by iFrame "Hspec Hstk' Hj". }
          iApply (wp_cas_suc with "Hstk"); auto.
          iNext. iIntros "Hstk".
          iMod (mapsto_persist with "Hltmp") as "#Hltmp".
          iMod ("Hclose" with "[-Hj]") as "_".
          { iNext. iExists ltmp, _.
            iFrame "Hstk' Hstk Hl".
            do 2 rewrite StackLink_unfold.
            rewrite -StackLink_unfold.
            iExists _, _. iSplit; trivial.
            iFrame "Hltmp". eauto 10. }
          iModIntro.
          iApply wp_pure_step_later; auto. iNext; iApply wp_value; trivial.
          iExists UnitV; eauto.
        * iApply (wp_cas_fail with "Hstk"); auto; first congruence.
          iNext. iIntros "Hstk". iMod ("Hclose" with "[-Hj]").
          { iNext. iExists _, _. by iFrame "Hstk' Hstk Hl". }
          iApply wp_pure_step_later; auto. iModIntro. iNext. by iApply "Hlat".
      + (* refinement of pop *)
        iModIntro. clear j K. iIntros ( [v1 v2] ) "[% %]".
        iIntros (j K) "Hj /="; simplify_eq/=.
        rewrite -(FG_pop_folding (Loc stk)).
        iLöb as "Hlat".
        rewrite {2}(FG_pop_folding (Loc stk)).
        iApply wp_pure_step_later; auto. iNext.
        rewrite -(FG_pop_folding (Loc stk)).
        iAsimpl.
        iApply (wp_bind (fill [LetInCtx _]));
          iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
        iInv stackN as (istk v) "[Hstk' [Hstk [#HLK Hl]]]" "Hclose".
        iApply (wp_load with "Hstk"). iNext. iIntros "Hstk".
        iPoseProof "HLK" as "HLK'".
        (* Checking whether the stack is empty *)
        rewrite {2}StackLink_unfold.
        iDestruct "HLK'" as (istk2 w) "[% [Hmpt [[% %]|HLK']]]"; simplify_eq/=.
        * (* The stack is empty *)
          rewrite CG_locked_pop_of_val.
          iMod (steps_CG_locked_pop_fail with "[$Hspec $Hstk' $Hl $Hj]")
             as "[Hj [Hstk' Hl]]"; first solve_ndisj.
          iMod ("Hclose" with "[-Hj Hmpt]") as "_".
          { iNext. iExists _, _. by iFrame "Hstk' Hstk Hl". }
          iModIntro.
          iApply wp_pure_step_later; auto. iNext. iAsimpl.
          iApply (wp_bind (fill [LetInCtx _]));
            iApply wp_wand_l; iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
          iClear "HLK".
          iInv stackN as (istk3 w) "[Hstk' [Hstk [HLK Hl]]]" "Hclose".
          iApply (wp_load with "Hmpt").
          iNext. iIntros "_". iMod ("Hclose" with "[-Hj]") as "_".
          { iNext. iExists _, _. iFrame "Hstk' Hstk HLK Hl". }
          iApply wp_pure_step_later; simpl; trivial.
          iModIntro. iNext. iAsimpl.
          iApply wp_pure_step_later; trivial.
          iNext. iApply wp_value; simpl; trivial. iExists (InjLV UnitV).
          iSplit; trivial. iLeft. iExists (_, _); repeat iSplit; simpl; trivial.
        * (* The stack is not empty *)
          iMod ("Hclose" with "[-Hj Hmpt HLK']") as "_".
          { iNext. iExists _, _. by iFrame "Hstk' Hstk HLK Hl". }
          iModIntro. iApply wp_pure_step_later; auto.
          iNext. iAsimpl.
          iApply (wp_bind (fill [LetInCtx _]));
            iApply wp_wand_l; iSplitR; [iIntros (w') "Hw"; iExact "Hw"|].
          iClear "HLK".
          iInv stackN as (istk3 w') "[Hstk' [Hstk [HLK Hl]]]" "Hclose".
          iApply (wp_load with "Hmpt"). iNext; iIntros "_".
          iMod ("Hclose" with "[-Hj Hmpt HLK']") as "_".
          { iNext. iExists _, _. by iFrame "Hstk' Hstk HLK Hl". }
          iApply wp_pure_step_later; auto.
          iModIntro. iNext. iAsimpl.
          iDestruct "HLK'" as (y1 z1 y2 z2) "[% HLK']". subst. simpl.
          iApply wp_pure_step_later; first done.
          iNext. iAsimpl.
          iApply (wp_bind (fill [UnfoldCtx; CasRCtx (LocV _) (LocV _); IfCtx _ _]));
            iApply wp_wand_l; iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
          iAsimpl. iApply wp_pure_step_later; auto.
          simpl. iNext. iApply wp_value.
          iApply (wp_bind (fill [CasRCtx (LocV _) (LocV _); IfCtx _ _]));
            iApply wp_wand_l; iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
          iAsimpl. iApply wp_pure_step_later; auto.
          simpl. iNext. iApply wp_value.
          iApply (wp_bind (fill [IfCtx _ _]));
            iApply wp_wand_l; iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
          clear istk3. iAsimpl.
          iInv stackN as (istk3 w) "[Hstk' [Hstk [#HLK Hl]]]" "Hclose".
          (* deciding whether CAS will succeed or fail *)
          destruct (decide (istk2 = istk3)) as [|Hneq]; subst.
          -- (* CAS succeeds *)
            (* In this case, the specification pushes *)
            iApply (wp_cas_suc with "Hstk"); simpl; auto.
            iNext. iIntros "Hstk {HLK'}". iPoseProof "HLK" as "HLK'".
            rewrite {2}StackLink_unfold.
            iDestruct "HLK'" as (istk4 w2) "[% [Hmpt' HLK']]"; simplify_eq/=.
            iDestruct (mapsto_agree with "Hmpt Hmpt'") as %<-.
            iDestruct "HLK'" as "[[% %]|HLK']"; simplify_eq/=.
            iDestruct "HLK'" as (yn1 yn2 zn1 zn2)
                                   "[% [% [#Hrel HLK'']]]"; simplify_eq/=.
             (* Now we have proven that specification can also pop. *)
             rewrite CG_locked_pop_of_val.
             iMod (steps_CG_locked_pop_suc with "[$Hspec $Hstk' $Hl $Hj]")
                as "[Hj [Hstk' Hl]]"; first solve_ndisj.
             iMod ("Hclose" with "[-Hj]") as "_".
             { iNext. iIntros "{Hmpt Hmpt' HLK}". rewrite StackLink_unfold.
               iDestruct "HLK''" as (istk5 w2) "[% [Hmpt HLK]]"; simplify_eq/=.
               iExists istk5, _. iFrame "Hstk' Hstk Hl".
               rewrite StackLink_unfold.
               iExists _, _; iSplitR; trivial.
               by iFrame "HLK". }
             iApply wp_pure_step_later; auto. iModIntro. iNext.
             iApply (wp_bind (fill [InjRCtx])); iApply wp_wand_l;
               iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
             iApply wp_pure_step_later; auto. iApply wp_value.
             iNext. iApply wp_value; simpl.
             iExists (InjRV _); iFrame "Hj".
             iRight. iExists (_, _). iSplit; trivial.
          -- (* CAS will fail *)
            iApply (wp_cas_fail with "Hstk"); [rewrite /= ?to_of_val //; congruence..|].
            iNext. iIntros "Hstk". iMod ("Hclose" with "[-Hj]") as "_".
            { iNext. iExists _, _. by iFrame "Hstk' Hstk HLK Hl". }
            iApply wp_pure_step_later; auto. iModIntro. iNext. by iApply "Hlat".
    - (* refinement of iter *)
      iModIntro. clear j K. iIntros ( [f1 f2] ) "/= #Hfs". iIntros (j K) "Hj".
      iApply wp_pure_step_later; auto using to_of_val. iNext.
      iMod (do_step_pure with "[$Hspec $Hj]") as "Hj"; eauto.
      iAsimpl.
      replace (FG_iter (of_val f1)) with (of_val (FG_iterV (of_val f1)))
        by (by rewrite FG_iter_of_val).
      replace (CG_iter (of_val f2)) with (of_val (CG_iterV (of_val f2)))
        by (by rewrite CG_iter_of_val).
      iApply (wp_bind (fill [FoldCtx; AppRCtx _])); iApply wp_wand_l;
        iSplitR; [iIntros (w) "Hw"; iExact "Hw"|].
      iInv stackN as (istk3 w) "[>Hstk' [>Hstk [#HLK >Hl]]]" "Hclose".
      iMod (steps_CG_snap _ _ (AppRCtx _ :: K)
            with "[Hstk' Hj Hl]") as "[Hj [Hstk' Hl]]"; first solve_ndisj.
      { rewrite ?fill_app. simpl. by iFrame "Hspec Hstk' Hl Hj". }
      iApply (wp_load with "[$Hstk]"). iNext. iIntros "Hstk".
      iMod ("Hclose" with "[-Hj]") as "_".
      { iNext. iExists _, _; by iFrame "Hstk' Hstk HLK Hl". }
      iModIntro.
      rewrite ?fill_app /= -FG_iter_folding.
      iLöb as "Hlat" forall (istk3 w) "HLK".
      rewrite {2}FG_iter_folding.
      iApply wp_pure_step_later; simpl; trivial.
      rewrite -FG_iter_folding. iAsimpl.
      iNext.
      iApply (wp_bind (fill [LoadCtx; CaseCtx _ _])); iApply wp_wand_l;
        iSplitR; [iIntros (v) "Hw"; iExact "Hw"|].
      iApply wp_pure_step_later; trivial. iApply wp_value. iNext.
      iApply (wp_bind (fill [CaseCtx _ _])); iApply wp_wand_l;
        iSplitR; [iIntros (v) "Hw"; iExact "Hw"|].
      rewrite StackLink_unfold.
      iDestruct "HLK" as (istk4 v) "[% [Hmpt HLK]]"; simplify_eq/=.
      iInv stackN as (istk5 v') "[Hstk' [Hstk [HLK' Hl]]]" "Hclose".
      iApply (wp_load with "Hmpt"). iNext. iIntros "_".
      iDestruct "HLK" as "[[% %]|HLK'']"; simplify_eq/=.
      * rewrite CG_iter_of_val.
        iMod (steps_CG_iter_end with "[$Hspec $Hj]") as "Hj"; first solve_ndisj.
        iMod ("Hclose" with "[-Hj]").
        { iNext. iExists _, _. by iFrame "Hstk' Hstk Hl". }
        iApply wp_pure_step_later; trivial.
        iModIntro. iNext. iApply wp_value; trivial. iExists UnitV; eauto.
      * iDestruct "HLK''" as (yn1 yn2 zn1 zn2)
                              "[% [% [#Hrel HLK'']]]"; simplify_eq/=.
        rewrite CG_iter_of_val.
        iMod (steps_CG_iter with "[$Hspec $Hj]") as "Hj"; first solve_ndisj.
        iMod ("Hclose" with "[-Hj HLK'']") as "_".
        { iNext. iExists _, _. by iFrame "Hstk' Hstk Hl". }
        simpl.
        iApply wp_pure_step_later; simpl; rewrite ?to_of_val; trivial.
        iAsimpl.
        iModIntro. iNext.
        iApply (wp_bind (fill [AppRCtx _; SeqCtx _]));
          iApply wp_wand_l; iSplitR; [iIntros (w') "Hw"; iExact "Hw"|].
        iApply wp_pure_step_later; simpl; rewrite ?to_of_val; trivial. iNext.
        iApply wp_value.
        iApply (wp_bind (fill [SeqCtx _]));
          iApply wp_wand_l; iSplitR; [iIntros (w') "Hw"; iExact "Hw"|].
        rewrite StackLink_unfold.
        iDestruct "HLK''" as (istk6 w') "[% HLK]"; simplify_eq/=.
        iSpecialize ("Hfs" $! (yn1, zn1) with "Hrel").
        iSpecialize ("Hfs" $! _ (SeqCtx _ :: K)).
        iApply wp_wand_l; iSplitR "Hj"; [|iApply "Hfs"; by iFrame "#"].
        iIntros (u) "/="; iDestruct 1 as (z) "[Hj [% %]]".
        simpl. subst. iAsimpl.
        iMod (do_step_pure with "[$Hspec $Hj]") as "Hj"; [done..|].
        iAsimpl.
        replace (CG_iter (of_val f2)) with (of_val (CG_iterV (of_val f2)))
          by (by rewrite CG_iter_of_val).
        iMod (step_snd _ _ (AppRCtx _ :: K) with "[$Hspec Hj]") as "Hj";
          [| | |simpl; by iFrame "Hj"|]; rewrite ?to_of_val; auto.
        iApply wp_pure_step_later; trivial.
        iNext. simpl.
        replace (FG_iter (of_val f1)) with (of_val (FG_iterV (of_val f1)))
          by (by rewrite FG_iter_of_val).
        iApply (wp_bind (fill [AppRCtx _]));
          iApply wp_wand_l; iSplitR; [iIntros (w'') "Hw"; iExact "Hw"|].
        iApply wp_pure_step_later; auto using to_of_val.
        simpl. iNext. rewrite -FG_iter_folding. iApply wp_value.
        iApply ("Hlat" $! istk6 zn2 with "[Hj] [HLK]"); trivial.
        rewrite StackLink_unfold; iModIntro; simpl.
        iDestruct "HLK" as "[Histk6 [HLK|HLK]]";
          iExists istk6, w'; iSplit; auto; iFrame "#".
        iRight. iDestruct "HLK" as (? ? ? ?) "(?&?&?&?)".
        iExists _, _, _, _; iFrame "#".
  Qed.
End Stack_refinement.

Theorem stack_ctx_refinement :
  [] ⊨ FG_stack ≤ctx≤ CG_stack : TForall (TProd (TProd
        (TArrow (TVar 0) TUnit)
        (TArrow TUnit (TSum TUnit (TVar 0))))
        (TArrow (TArrow (TVar 0) TUnit) TUnit)).
Proof.
  set (Σ := #[invΣ; gen_heapΣ loc val; soundness_binaryΣ]).
  set (HG := soundness.HeapPreIG Σ _ _).
  eapply (binary_soundness Σ); eauto using FG_stack_type, CG_stack_type.
  intros; apply FG_CG_counter_refinement.
Qed.
