From iris.algebra Require Import agree.
From iris.base_logic Require Import invariants.
From WBLogrel.heap_lang_trace Require Import adequacy notation proofmode.

(** ** Proof that the very awkward example specification guarantees
       that its implementation behaves sequentially, whatever the
       implementation. *)

(** *** Separation logic specification *)

Section Spec.
Context `{!wbheapGS Σ}.

Definition very_awk_spec P0 (very_awk: expr) : iProp Σ :=
  {WB{{ P0 }}}
    very_awk
  {{{(f : val), RET f;
       ∀ (g : val),
         {WB{{ {WB{{ True }}} g #() {{{ RET #(); True }}} }}} f g {{{ RET #1; True }}}
  }}}.

End Spec.

(** *** The trace property: calls (identified by '(') and returns (identified by
    ')') are well bracketed *)

Section Trace.

Inductive sequential_with_opened : list val → list val → Prop :=
  | sequential_with_opened_nil :
      sequential_with_opened [] []
  | sequential_with_opened_open tag o t :
      sequential_with_opened o t →
      sequential_with_opened (tag :: o) (t ++ (tag, #"(")%V :: nil)
  | sequential_with_opened_close tag o t :
      sequential_with_opened (tag :: o) t →
      sequential_with_opened o (t ++ (tag, #")")%V :: nil).

Definition sequential_trace (t: list val) :=
  ∃ o, sequential_with_opened o t.

End Trace.

(** *** Definition and correctness of the wrapper code *)

Module Wrap.
Section S.
Context `{!wbheapGS Σ, !inG Σ (agreeR (leibnizO (list val)))}.

Context (very_awk: expr).

Definition very_awk_instrumented : expr :=
  let: "f" := very_awk in
  λ: "g",
  (* fresh *)
    "f" (λ: <>,
      let: "t" := Fresh (#"(") in
      "g" #() ;;
      Emit ("t", #")")
    (* emit *)
).

Lemma correct (P0: iProp Σ) t :
  very_awk_spec P0 very_awk -∗
  very_awk_spec (P0 ∗ trace_is t ∗ trace_inv (nroot .@ "trace") sequential_trace) very_awk_instrumented.
Proof.
  iIntros "#Hspec". rewrite /very_awk_instrumented /very_awk_spec.
  iIntros (φ) "!> (HP0 & Ht & #HI) Hφ".

  iMod (trace_is_inv with "Ht HI") as "[Ht %Ht]".
  destruct Ht as [o Ht].

  iMod (own_alloc (to_agree (o:leibnizO _))) as (γ) "Hγ". done.
  iApply (wbwp_make_gstack _ _ γ). iIntros (N) "Hstk".
  iAssert (gstack_exists N) as "#Hstkex"; first by iApply gstack_frag_exists.

  iMod (inv_alloc
          (nroot .@ "wrap") _
          (∃ γ s (o: list val) t,
             gstack_frag N (gpush γ s) ∗ own γ (to_agree (o:leibnizO _)) ∗
             trace_is t ∗ ⌜sequential_with_opened o t⌝)%I
        with "[Hstk Hγ Ht]") as "#Hinv".
  { iNext. iExists γ, [], o, t. by iFrame. }

  wbwp_bind very_awk. iApply ("Hspec" with "HP0").
  iIntros "!>" (f) "#Hf".
  wbwp_pures. iApply wbwp_value.
  iApply "Hφ". iIntros (g Φ) "!# #Hg HΦ".
  wbwp_pures. iApply "Hf"; last done.

  iIntros (Ψ) "!# _ HΨ". wbwp_pures.
  (* access the stack for the whole duration of the call to g and its
     instrumentation *)
  iApply (wbwp_get_gstack_full N with "Hstkex"); first done.
  iIntros (s) "Hstkfull".

  (* Fresh *)
  wbwp_bind (Fresh _).
  iInv (nroot .@ "wrap") as (γ1 s1 o1 t1) "(>Hstk & >Hγ1 & >Ht1 & >%Ht1)" "Hclose".
  iDestruct (gstacks_agree with "Hstkfull Hstk") as %->.
  iApply (wbwp_fresh with "[$Ht1 $HI]"); first solve_ndisj.
  { intros tag Htag. exists (#tag :: o1). by constructor. }
  iIntros "!>" (tag) "[Ht1 %Htag]".
  iMod (own_alloc (to_agree ((#tag :: o1) : leibnizO _))) as (γ2) "#Hγ2"; first done.
  iMod (gstack_push _ _ _ γ2 with "Hstkfull Hstk") as "[Hstkfull Hstk]".
  iMod ("Hclose" with "[Ht1 Hγ2 Hstk]") as "_".
  { iNext. iExists γ2, (gpush γ1 s1), (#tag :: o1), _. iFrame "Hγ2 ∗".
    iPureIntro. by constructor. }
  iModIntro.

  (* call to g *)
  wbwp_pures. wbwp_bind (g _).
  iApply (wbwp_wand with "[Hstkfull]").
  { iApply (wbwp_mend _ _ _ _ _ (λ _, True)%I with "Hstkfull").
    rewrite (_: (∅ ∪ {[N]}) ∖ {[N]} = ∅); last set_solver. by iApply "Hg". }
  iIntros (v) "[Hstkfull _]".

  (* Emit *)
  wbwp_pures.
  iInv (nroot .@ "wrap") as (γ3 s3 o3 t3) "(>Hstk & >Hγ3 & >Ht3 & >%Ht3)" "Hclose".
  (* exploit the fact that the call to g preserved the stack because g is well
     bracketed *)
  iDestruct (gstacks_agree with "Hstkfull Hstk") as %Hagree.
  inversion Hagree; subst γ3 s3.
  iDestruct (own_op with "[$Hγ3 $Hγ2]") as "Hγ2'".
  iDestruct (own_valid with "Hγ2'") as %Ho3%to_agree_op_inv%leibniz_equiv. subst o3.
  iClear "Hγ2'".
  iApply (wbwp_emit with "[$Ht3 $HI]"); first solve_ndisj.
  { eexists. by econstructor. }
  iIntros "!> Ht".

  (* restore the stack and return *)
  iMod (gstack_pop with "Hstkfull Hstk") as "[Hstkfull Hstk]".
  iMod ("Hclose" with "[Ht Hγ1 Hstk]") as "_".
  { iNext. iExists _, _, _, _. iFrame. iPureIntro. by constructor. }
  iModIntro.
  iFrame "Hstkfull". by iApply "HΨ".
Qed.

End S.

End Wrap.

(** *** Adequacy *)

Definition awkN := nroot .@ "trace".
Definition empty_state : state := Build_state ∅ [] ∅.

(** The trace property [sequential_trace] is satisfied at every step of the
    execution at the level of the operational semantics. *)
Lemma wrap_very_awk_correct `{wbheapGpreS Σ, inG Σ (agreeR (leibnizO (list val)))}
  (e: expr → expr) (very_awk_init: expr) (very_awk: expr) (P0: iProp Σ):
  (∀ `(wbheapGS Σ), ⊢ {{{ True }}} very_awk_init {{{ v, RET v; P0 }}}) →
  (∀ `(wbheapGS Σ), ⊢ very_awk_spec P0 very_awk) →
  (∀ `(wbheapGS Σ), ⊢ ∀ P very_awk, very_awk_spec P very_awk -∗ {WB{{ P }}} e very_awk {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(very_awk_init;; e (Wrap.very_awk_instrumented very_awk))%E], empty_state) (e', σ') →
    sequential_trace (trace σ').
Proof.
  intros Hinit Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ (WBHeapGpreS Σ _ _ _ _ _ _ _)
                             awkN (@very_awk_spec Σ) P0 e very_awk_init (Wrap.very_awk_instrumented very_awk)
                             sequential_trace empty_state).
  { cbn. econstructor. constructor. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? ? ?) "!> Hφ". iApply Hinit; eauto. }
  { iIntros (?). iApply Wrap.correct. iApply Hlib. }
  eauto.
Qed.
