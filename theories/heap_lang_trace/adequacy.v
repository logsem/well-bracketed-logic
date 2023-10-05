From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From WBLogic.program_logic Require Export weakestpre adequacy.
From WBLogic.heap_lang_trace Require Import notation.
From WBLogic.heap_lang_trace Require Import proofmode.
From WBLogic.heap_lang_trace Require Import trace_resources.
From iris.prelude Require Import options.

Class wbheapGpreS Σ := WBHeapGpreS {
  wbheapGpreS_iris :: invGpreS Σ;
  wbheapGpreS_heap :: gen_heapGpreS loc (option val) Σ;
  wbheapGpreS_inv_heap :: inv_heapGpreS loc (option val) Σ;
  wbheapGpreS_proph :: proph_mapGpreS proph_id (val * val) Σ;
  wbheapGS_step_cnt :: mono_natG Σ;
  wbheapGpreS_gstacks :: gstacksGpre Σ;
  wbheapGpreS_trace :: trace_preG Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val); inv_heapΣ loc (option val);
    proph_mapΣ proph_id (val * val); mono_natΣ; gstacksΣ; traceΣ].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → wbheapGpreS Σ.
Proof. solve_inG. Qed.

(* TODO: The [wp_adequacy] lemma is insufficient for a state interpretation
with a non-constant step index function. We thus use the more general
[wp_strong_adequacy] lemma. The proof below replicates part of the proof of
[wp_adequacy], and it hence would make sense to see if we can prove a version
of [wp_adequacy] for a non-constant step version. *)
Definition wbheap_adequacy Σ `{!wbheapGpreS Σ} e σ φ :
  (∀ `{!wbheapGS Σ}, ⊢ inv_heap_inv -∗ WBWP e @ ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wbwp_strong_adequacy Σ _); [|done].
  iIntros (Hinv ?).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (trace_auth_init σ.(trace)) as (?) "(Hta & Ht & Hth)".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc) as (γ) "[Hsteps _]".
  iDestruct (Hwp (WBHeapGS _ _ _ _ _ _ _ _ _) with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          trace_auth σ.(trace) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists (λ v, ⌜φ v⌝%I), (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ?) " _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|by eauto].
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Definition wbheap_invariance Σ `{!wbheapGpreS Σ} (N: namespace) (I: list val → Prop) e σ :
  I (trace σ) →
  (∀ `{!wbheapGS Σ}, ⊢ trace_inv N I -∗ trace_is (trace σ) -∗ WBWP e @ ⊤ {{ _, True }}) →
  ∀ σ' t,
    rtc erased_step ([e], σ) (t, σ') →
    I (trace σ').
Proof.
  intros HI Hwp t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wbwp_strong_adequacy Σ _); [|done].
  iIntros (Hinv ?).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (trace_auth_init σ.(trace)) as (?) "(Hta & Ht & Hth)".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc) as (γ) "[Hsteps _]".
  iDestruct (inv_alloc N _ (∃ t, trace_half_frag t ∗ ⌜I t⌝) with "[Hth]") as ">#HI".
  { iNext. eauto. }
  iDestruct (Hwp (WBHeapGS _ _ _ _ _ _ _ _ _) with "HI Ht") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          trace_auth σ.(trace) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists (λ _, True)%I, (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ?) " (? & Hta & ? & ?) _ _".
  iInv "HI" as ">Ht'" "_". iDestruct "Ht'" as (t') "(Ht' & %)".
  iDestruct (trace_auth_half_frag_agree with "Hta Ht'") as %->.
  iApply fupd_mask_intro_discard; [solve_ndisj|]. eauto.
Qed.

(** Specialized adequacy theorem to establish trace properties as free theorems.
   This corresponds to Theorem 4.1 in the paper.

   Minor remark 1: in the paper, the state of the operational semantics is
   represented as a pair of a heap and a trace. Here, we instead have σ,σ' be
   inhabitants of the [state] record type, and we use the [trace] projection to
   get the trace of a given state.

   Minor remark 2: the following theorem is slightly more general than the one
   from the paper, as we only require the trace property to hold of the trace of
   the initial state σ, while the theorem in the paper is specialized to the
   case where the initial trace is the empty trace. *)
Lemma module_invariance {Σ} `{!wbheapGpreS Σ} (N: namespace)
  (Φ: ∀ `{wbheapGS Σ}, iProp Σ → expr → iProp Σ)  (* Module specification *)
  (P0: iProp Σ) (* Initial resources required by the module *)
  (e: expr → expr) (* Context program, parameterized by the module *)
  (e_init: expr) (* Initialization code, used to allocate resources for P0 *)
  (imimpl: expr) (* Implementation of the module (instrumented) *)
  (good_trace: list val → Prop) (* Trace property *)
  (σ: state) (* Initial state *)
:
  (* The initial trace must satisfy the property *)
  good_trace (trace σ) →
  (* The context must be safe, given a module satisfying the specification Φ *)
  (⊢ ∀ `(wbheapGS Σ) P m, Φ P m -∗ {WB{{ P }}} e m {{{ v, RET v; True }}}) →
  (* The initialization code must provide P0; it does not need to be WB *)
  (⊢ ∀ `(wbheapGS Σ), {{{ True }}} e_init {{{ v, RET v; P0 }}}) →
  (* The implementation provided for the module (iops) must satisfy the specification Φ.
     On top of P0 it is given SL resources for the trace. *)
  (⊢ ∀ `(wbheapGS Σ), Φ (P0 ∗ trace_is (trace σ) ∗ trace_inv N good_trace)%I imimpl) →
  (* Then the trace remains good at every step *)
  ∀ σ' e',
    rtc erased_step ([(e_init;; e imimpl)%E], σ) (e', σ') →
    good_trace (trace σ').
Proof.
  intros Htrσ Hctx Hinit Himpl σ' e' Hsteps.
  eapply wbheap_invariance; [done | by apply Htrσ | | by eapply Hsteps].
  iIntros (?) "HI Htr". wbwp_bind e_init.
  iApply wp_wbwp. iApply Hinit; first done.
  iIntros "!>" (v) "H0". wbwp_pures.
  iApply (Hctx with "[] [H0 Htr HI]").
  - iApply Himpl.
  - iFrame.
  - eauto.
Qed.
