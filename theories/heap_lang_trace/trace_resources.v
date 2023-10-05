From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl agree gmap list.
From iris.algebra.lib Require Import frac_auth.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map invariants.
From WBLogic.heap_lang_trace Require Import lang.
Set Default Proof Using "Type".

Fixpoint gmap_of_trace {A} (n: nat) (l: list A): gmap nat (agree (leibnizO A)) :=
  match l with
  | nil => ∅
  | x :: l' => <[ n := to_agree x ]> (gmap_of_trace (S n) l')
  end.

Lemma gmap_of_trace_snoc {A} n (l: list A) (a: A):
  gmap_of_trace n (l ++ [a]) =
  <[ (n + length l)%nat := to_agree a ]> (gmap_of_trace n l).
Proof.
  revert n. induction l as [| x l].
  { cbn. intros. by rewrite Nat.add_0_r. }
  { intros. cbn. rewrite IHl /= -Nat.add_succ_r insert_commute //. lia. }
Qed.

Lemma gmap_of_trace_dom {A} (n: nat) (l: list A) k :
  k ∈ dom (gmap_of_trace n l) ↔ (n ≤ k < n + length l)%nat.
Proof.
  revert n. induction l.
  { intros. cbn. rewrite dom_empty_L elem_of_empty. lia. }
  { intros. cbn. rewrite dom_insert_L elem_of_union elem_of_singleton IHl. lia. }
Qed.

Definition eventO := leibnizO val.
Definition traceO := leibnizO (list val).

Class traceGS Σ := TraceGS {
  trace_hist_inG :: inG Σ (authR (gmapUR nat (agreeR eventO)));
  trace_hist_name : gname;
  trace_inG :: inG Σ (frac_authR (agreeR traceO));
  trace_name : gname;
}.

Definition traceΣ : gFunctors :=
  #[GFunctor (authR (gmapUR nat (agreeR eventO)));
    GFunctor (frac_authR (agreeR traceO))].

Class trace_preG Σ := TracePreG {
  trace_hist_preG_inG :: inG Σ (authR (gmapUR nat (agreeR eventO)));
  trace_preG_inG :: inG Σ (frac_authR (agreeR traceO));
}.

Global Instance subG_tracePreG {Σ} : subG traceΣ Σ → trace_preG Σ.
Proof. solve_inG. Qed.

(** Trace-related resources.

   - [trace_is] asserts the ownership over the trace (it corresponds to [trace]
     in the paper);
   - [trace_inv] asserts that the trace preserves a given invariant (it is named
     [traceInv] in the paper);
   - [hist] describes a snapshot of the trace, as it was sometime in the past
*)
Definition trace_auth `{hT: traceGS Σ} (t: list val) :=
  (own trace_name (●F (to_agree (t: traceO))))%I.
Definition hist `{hT: traceGS Σ} (t: list val) :=
  own trace_hist_name (◯ (gmap_of_trace 0 t)).
Definition trace_half_frag `{hT:traceGS} (t: list val) :=
  own trace_name (◯F{1/2} (to_agree (t: traceO))).
Definition trace_is `{hT: traceGS Σ} (t: list val) :=
  (trace_half_frag t ∗ own trace_hist_name (● gmap_of_trace 0 t) ∗ hist t)%I.

Definition trace_inv `{hT:traceGS Σ, hI:invGS Σ} (N: namespace) (I: list val → Prop) :=
  inv N (∃ t, trace_half_frag t ∗ ⌜I t⌝).

(** Reasoning rules for the trace predicates *)

Global Instance hist_persistent `{traceGS Σ} (t: list val): Persistent (hist t) := _.

Lemma alloc_hist `{traceGS Σ} t :
  trace_is t -∗ trace_is t ∗ hist t.
Proof.
  rewrite /trace_is /hist. iIntros "(? & ? & #H)". iFrame "H ∗".
Qed.

Lemma trace_auth_half_frag_agree `{traceGS Σ} t t':
  trace_auth t -∗ trace_half_frag t' -∗ ⌜t = t'⌝.
Proof.
  rewrite /trace_auth /trace_is.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as "H".
  iDestruct "H" as %Hi%frac_auth_included.
  rewrite -> Some_included_total in Hi.
  apply to_agree_included, leibniz_equiv in Hi. eauto.
Qed.

Lemma trace_agree `{traceGS Σ} t t':
  trace_auth t -∗ trace_is t' -∗ ⌜t = t'⌝.
Proof.
  iIntros "H1 (H2 & _ & _)". iApply (trace_auth_half_frag_agree with "H1 H2").
Qed.

Lemma trace_half_frag_agree `{traceGS Σ} t t':
  trace_half_frag t -∗ trace_is t' -∗ ⌜t = t'⌝.
Proof.
  rewrite /trace_is /trace_half_frag.
  iIntros "H1 (H2 & _ & _)".
  iDestruct (own_valid_2 with "H1 H2") as "H".
  rewrite -frac_auth_frag_op Qp.half_half.
  iDestruct "H" as %Hv. rewrite frac_auth_frag_valid in Hv.
  destruct Hv as [_ Hv].
  apply to_agree_op_inv, leibniz_equiv in Hv. eauto.
Qed.

Lemma trace_add_event `{traceGS Σ} t (e: val) :
  trace_auth t -∗ trace_is t -∗ trace_half_frag t ==∗
  trace_auth (t ++ [e]) ∗ trace_is (t ++ [e]) ∗ trace_half_frag (t ++ [e]).
Proof.
  rewrite /trace_auth /trace_is /hist.
  iIntros "H1 (H2 & H2ha & H2h) H3".
  iDestruct (own_op with "[$H2 $H3]") as "H2".
  rewrite -frac_auth_frag_op Qp.half_half agree_idemp.
  iMod (own_update_2 _ _ _ (●F (to_agree (t++[e]:traceO)) ⋅ ◯F (to_agree (t++[e]:traceO))) with "H1 H2") as "[? ?]".
  by apply frac_auth_update_1.
  rewrite gmap_of_trace_snoc Nat.add_0_l.
  iMod (own_update_2 with "H2ha H2h") as "[? ?]".
  apply auth_update.
  eapply (alloc_local_update _ _ (length t : nat) (to_agree (e:eventO))); [|done].
  { eapply not_elem_of_dom. intros ?%gmap_of_trace_dom. lia. }
  iModIntro. iFrame.
  rewrite /trace_half_frag -own_op -frac_auth_frag_op Qp.half_half agree_idemp //.
  Unshelve. all: typeclasses eauto.
Qed.

Lemma gmap_of_trace_hist_valid_prefix `{traceGS Σ} {A} n (t: list A) h :
  ✓ gmap_of_trace n t →
  gmap_of_trace n h ≼ gmap_of_trace n t →
  h `prefix_of` t.
Proof.
  revert n t. induction h as [| a h].
  { cbn. intros. apply prefix_nil. }
  { intros n t Hv Hsub.
    pose proof (proj1 (lookup_included _ _) Hsub) as Hsub'.
    destruct t as [| e t].
    { exfalso. specialize (Hsub' n).
      rewrite /= lookup_insert lookup_empty in Hsub'.
      apply option_included in Hsub' as [HH|(? & ? & ? & HH & ?)]; inversion HH. }
    specialize (Hsub' n). rewrite /= !lookup_insert in Hsub'.
    eapply (proj1 (Some_included_total _ _)) in Hsub'.
    eapply (proj1 (to_agree_included (a:leibnizO A) e)) in Hsub'.
    apply leibniz_equiv in Hsub'. subst e.
    cbn in Hsub.
    apply (delete_valid _ n) in Hv. rewrite /= delete_insert in Hv.
    2: { eapply not_elem_of_dom. intros ?%gmap_of_trace_dom. lia. }
    assert (gmap_of_trace (S n) h ≼ gmap_of_trace (S n) t).
    { apply lookup_included. intros i.
      eapply (proj1 (lookup_included _ _)) with i in Hsub.
      destruct (decide (i = n)); subst.
      { rewrite (_ : gmap_of_trace (S n) h !! n = None).
        rewrite (_ : gmap_of_trace (S n) t !! n = None) //.
        all: eapply not_elem_of_dom.
        all: intros ?%gmap_of_trace_dom; lia. }
      rewrite !lookup_insert_ne // in Hsub. }
    eapply prefix_cons, IHh; eauto. }
  Unshelve. all: typeclasses eauto.
Qed.

Lemma hist_trace_is_prefix `{traceGS Σ} t h :
  trace_is t -∗ hist h -∗ ⌜ h `prefix_of` t ⌝.
Proof.
  rewrite /trace_is /hist. iIntros "(H1 & H2 & H3) H4".
  iDestruct (own_op with "[$H2 $H4]") as "H".
  iDestruct (own_valid with "H") as %[Hsub Hv]%auth_both_valid_discrete.
  iPureIntro. eapply gmap_of_trace_hist_valid_prefix; eauto.
Qed.

Lemma trace_is_inv `{traceGS Σ, invGS Σ} t N I :
  trace_is t -∗ trace_inv N I ={⊤}=∗ trace_is t ∗ ⌜ I t ⌝.
Proof.
  iIntros "Ht Hi". unfold trace_inv.
  iInv N as ">H" "Hclose". iDestruct "H" as (t') "(Ht' & %)".
  iDestruct (trace_half_frag_agree with "[$] [$]") as %->.
  iMod ("Hclose" with "[Ht']"). eauto. iIntros "!>". eauto.
Qed.

Lemma gmap_of_trace_valid {A} (l: list A) (n: nat):
  ✓ gmap_of_trace n l.
Proof.
  revert n. induction l.
  { cbn. done. }
  { intro. cbn. eapply (@insert_valid _ _ _ (agreeR (leibnizO A))); eauto; done. }
Qed.

Lemma trace_auth_init `{hT: trace_preG Σ} (t: list val) :
  ⊢ |==> ∃ H: traceGS Σ, trace_auth t ∗ trace_is t ∗ trace_half_frag t.
Proof.
  iMod (own_alloc (●F (to_agree (t: traceO)) ⋅ ◯F (to_agree (t: traceO)))) as (γ) "Hγ".
  by apply frac_auth_valid.
  rewrite own_op. iDestruct "Hγ" as "[? Hγf]".
  iMod (own_alloc (● gmap_of_trace 0 t ⋅ ◯ gmap_of_trace 0 t)) as (γh) "Hγh".
  apply auth_both_valid. split; [ done | by apply gmap_of_trace_valid].
  rewrite own_op. iDestruct "Hγh" as "[? ?]".
  iModIntro. iExists (TraceGS _ _ γh _ γ).
  rewrite /trace_auth /trace_is /trace_half_frag /hist. iFrame.
  rewrite -own_op -frac_auth_frag_op Qp.half_half agree_idemp //.
Qed.
