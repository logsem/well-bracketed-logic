From WBLogrel.F_mu_ref.binary Require Export context_refinement.
From iris.algebra Require Import auth frac agree.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogrel.program_logic Require Import adequacy.
From WBLogrel.F_mu_ref.unary Require Import soundness.
From iris.prelude Require Import options.

Definition soundness_binaryΣ : gFunctors := #[ GFunctor (authR cfgUR) ].

(* FIXME: Really we should define a [soundnessG] as well. *)
Global Instance inG_soundness_binaryΣ Σ : subG soundness_binaryΣ Σ → inG Σ (authR cfgUR).
Proof. solve_inG. Qed.

Lemma basic_soundness Σ `{soundness_unary_preG Σ, inG Σ (authR cfgUR)}
    e e' τ v thp hp :
  (∀ `{heapIG Σ, cfgSG Σ}, ⊢ [] ⊨ e ≤log≤ e' : τ) →
  rtc erased_step ([e], ∅) (of_val v :: thp, hp) →
  (∃ thp' hp' v', rtc erased_step ([e'], ∅) (of_val v' :: thp', hp')).
Proof.
  intros Hlog Hsteps.
  cut (adequate NotStuck e ∅ (λ _ _, ∃ thp' h v, rtc erased_step ([e'], ∅) (of_val v :: thp', h))).
  { destruct 1; naive_solver. }
  eapply (wbwp_adequacy Σ _); iIntros (Hinv ? ?).
  iMod (gen_heap_init (∅: state)) as (Hheap) "[Hh _]".
  iMod (own_alloc (● (to_tpool [e'], ∅)
    ⋅ ◯ ((to_tpool [e'] : tpoolUR, ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_both_valid_discrete. split=>//. split=>//. apply to_tpool_valid. }
  set (Hcfg := CFGSG _ _ γc).
  iMod (inv_alloc specN _ (spec_inv ([e'], ∅)) with "[Hcfg1]") as "#Hcfg".
  { iNext. iExists [e'], ∅. rewrite /to_heap fmap_empty. auto. }
  set (HeapΣ := (HeapIG Σ Hinv Hheap _)).
  iExists (λ σ _, gen_heap_interp σ), (λ _, True%I); iFrame.
  iApply wbwp_fupd. iApply wbwp_wand_r.
  iSplitL.
  - iPoseProof ((Hlog _ _)) as "Hrel".
    iSpecialize ("Hrel" $! [] [] with "[]").
    { iSplit.
      - by iExists ([e'], ∅).
      - iApply (interp_env_nil []). }
    simpl.
    replace e with e.[env_subst[]] at 2 by by asimpl.
    iModIntro.
    iApply ("Hrel" $! 0 []).
    { rewrite /tpool_mapsto. asimpl. by iFrame. }
  - iModIntro. iIntros (v1); iDestruct 1 as (v2) "(Hj & #Hinterp)".
    iInv specN as (tp σ) ">[Hown Hsteps]" "Hclose"; iDestruct "Hsteps" as %Hsteps'.
    rewrite /tpool_mapsto /=.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    move: Hvalid=> /auth_both_valid_discrete
      [/prod_included [/tpool_singleton_included Hv2 _] _].
    destruct tp as [|? tp']; simplify_eq/=.
    iMod ("Hclose" with "[-]") as "_"; [iExists (_ :: tp'), σ; auto|].
    iIntros "!> !%"; eauto.
Qed.

Lemma binary_soundness Σ `{soundness_unary_preG Σ, inG Σ (authR cfgUR)}
    Γ e e' τ :
  (Γ ⊢ₜ e : τ) → (Γ ⊢ₜ e' : τ) →
  (∀ `{heapIG Σ, cfgSG Σ}, ⊢ Γ ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros He He' Hlog; repeat split; auto.
  intros K thp σ v ?. eapply (basic_soundness Σ _)=> ??.
  iApply (bin_log_related_under_typed_ctx _ _ _ _ []);
    [by eapply typed_n_closed|by eapply typed_n_closed|done|].
  iApply Hlog.
Qed.
