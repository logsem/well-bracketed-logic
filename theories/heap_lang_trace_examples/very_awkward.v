From iris.algebra Require Import agree.
From iris.base_logic Require Import invariants.
From WBLogic Require Import oneshot.
From WBLogic.heap_lang_trace Require Import adequacy notation proofmode.

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
    ')') are well bracketed.

    See [sequential_trace_alt.v] for an alternative, equivalent definition of
    [sequential_trace]. *)

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

  iApply (wbwp_make_gstack
              (λ n, inv (nroot .@ "wrap")
                      (∃ γ s (o: list val) t,
                          gstack_frag n (gpush γ s) ∗ own γ (to_agree (o:leibnizO _)) ∗
                            trace_is t ∗ ⌜sequential_with_opened o t⌝) ∗ gstack_exists n)%I with "[Ht]").
    { iIntros (n Hn) "Hfl Hfr".
      iMod (own_alloc (to_agree (o:leibnizO _))) as (γ) "Hγ". done.
      iPoseProof (gstack_frag_exists with "Hfr") as "#?".
      iMod (gstack_push _ _ _ γ with "Hfl Hfr") as "[Hfl Hfr]".
      iMod (inv_alloc with "[- Hfl]"); last by iModIntro; iExists _; iFrame.
      iNext; iExists γ, [], o, t; by iFrame. }
    iIntros (N HN) "#[Hinv Hex]".

  wbwp_bind very_awk. iApply ("Hspec" with "HP0").
  iIntros "!>" (f) "#Hf".
  wbwp_pures. iApply wbwp_value.
  iApply "Hφ". iIntros (g Φ) "!# #Hg HΦ".
  wbwp_pures. iApply "Hf"; last done.

  iIntros (Ψ) "!# _ HΨ". wbwp_pures.
  (* access the stack for the whole duration of the call to g and its
     instrumentation *)
  iApply (wbwp_get_gstack_full N with "[$]"); first done.
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

(* concretizing with concrete programs. *)

Definition very_awkward : expr :=
  let: "l" := ref #0 in
  λ: "f", "l" <- #0;; "f" #();; "l" <- #1;; "f" #();; ! "l".

Definition very_awkward_self_apply very_awk : expr :=
  let: "f" := very_awk in
  "f" (λ: <>, "f" (λ: <>, #());; #()).


Definition factorial : val :=
  rec: "fact" "n" := if: "n" = #0 then #1 else "n" * ("fact" ("n" - #1)).

Definition call_fact_across : expr :=
  let: "b" := ref #true in
  let: "c" := ref NONE in
  let: "wait" := rec: "w" <> := if: ! "c" = NONE then "w" #() else #() in
  λ: <>, if: ! "b" then "b"  <- #false;; Fork (factorial #1000000) else "wait" #().

Definition very_akward_call_fact_across very_awk : expr :=
  let: "h" := very_awk in
  let: "g" := call_fact_across in
  "h" "g".

Section very_awkward.
  Context `{!wbheapGS Σ} `{!oneshotG Σ}.

  Lemma wbwp_very_awkward : ⊢ very_awk_spec True very_awkward.
  Proof.
    rewrite /very_awkward /very_awk_spec.
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

  Lemma wbwp_very_awkward_self_apply P very_awk :
    very_awk_spec P very_awk -∗ {WB{{ P }}} very_awkward_self_apply very_awk {{{ RET #1; True }}}.
  Proof.
    rewrite /very_awkward_self_apply.
    iIntros "#Hawk !#" (Φ) "HP HΦ".
    wbwp_apply ("Hawk" with "[$]").
    iIntros (f) "#Hf".
    wbwp_pures.
    wbwp_apply "Hf"; last done.
    clear Φ.
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

  Lemma wbwp_very_akward_call_fact_across P very_awk :
    very_awk_spec P very_awk -∗
    {WB{{ P }}} very_akward_call_fact_across very_awk {{{ RET #1; True }}}.
  Proof.
    rewrite /very_akward_call_fact_across /very_awk_spec.
    iIntros "#Hawk !#" (Φ) "HP HΦ".
    wbwp_apply ("Hawk" with "[$]").
    iIntros (h) "#Hh".
    wbwp_pures.
    wbwp_bind call_fact_across.
    iApply wp_wbwp.
    iApply wp_call_fact_across; first done.
    iNext.
    iIntros (g) "#Hg".
    wbwp_pures.
    iApply "Hh"; last done.
    clear Φ.
    iIntros "!#" (Φ) "_ HΦ".
    iApply wp_wbwp.
    iApply "Hg"; done.
  Qed.

End very_awkward.

Theorem very_awkward_self_apply_returns_one :
    ∀ σ' e',
      rtc erased_step ([((#();; #());; very_awkward_self_apply (Wrap.very_awk_instrumented very_awkward))%E], empty_state)
        (e', σ') →
      sequential_trace (trace σ').
Proof.
  assert (∀ Σ, subG (GFunctor (agreeR (leibnizO (list val)))) Σ → inG Σ (agreeR (leibnizO (list val)))).
  { solve_inG. }
  set (Σ := #[heapΣ; oneshotΣ; GFunctor (agreeR (leibnizO (list val)))]).
  apply (@wrap_very_awk_correct Σ _ _ _ _ _ True%I).
  - iIntros (?) "!#"; iIntros (?) "_ H"; wp_pures; iApply "H"; done.
  - intros; apply wbwp_very_awkward.
  - iIntros (? ? ?) "#? !#"; iIntros (?) "HP H".
    iApply (wbwp_very_awkward_self_apply with "[$] [$]").
    iNext; iIntros "_"; iApply "H"; done.
Qed.

Theorem wbwp_very_akward_call_fact_across_returns_one :
    ∀ σ' e',
      rtc erased_step ([((#();; #());; very_akward_call_fact_across (Wrap.very_awk_instrumented very_awkward))%E], empty_state)
        (e', σ') →
      sequential_trace (trace σ').
Proof.
  assert (∀ Σ, subG (GFunctor (agreeR (leibnizO (list val)))) Σ → inG Σ (agreeR (leibnizO (list val)))).
  { solve_inG. }
  set (Σ := #[heapΣ; oneshotΣ; GFunctor (agreeR (leibnizO (list val)))]).
  apply (@wrap_very_awk_correct Σ _ _ _ _ _ True%I).
  - iIntros (?) "!#"; iIntros (?) "_ H"; wp_pures; iApply "H"; done.
  - intros; apply wbwp_very_awkward.
  - iIntros (? ? ?) "#? !#"; iIntros (?) "HP H".
    iApply (wbwp_very_akward_call_fact_across with "[$] [$]").
    iNext; iIntros "_"; iApply "H"; done.
Qed.
