From stdpp Require Import list.
From WBLogic.heap_lang_trace Require Import notation.
From WBLogic.heap_lang_trace_examples Require Import very_awkward.

Inductive sequential_full_trace : list val → Prop :=
  | sequential_full_trace_nil : sequential_full_trace []
  | sequential_full_trace_wrap tag t :
      sequential_full_trace t →
      sequential_full_trace ((tag, #"(")%V :: t ++ (tag, #")")%V :: nil)
  | sequential_full_trace_app t t' :
      sequential_full_trace t →
      sequential_full_trace t' →
      sequential_full_trace (t ++ t').

Definition sequential_trace_alt (t: list val) :=
  ∃ t', sequential_full_trace t' ∧ t `prefix_of` t'.

Lemma sequential_call tag :
  sequential_full_trace [(tag, #"(")%V ; (tag, #")")%V].
Proof. apply (sequential_full_trace_wrap tag _ sequential_full_trace_nil). Qed.

Lemma sequential_full_trace_call_middle tag t t' :
  sequential_full_trace (t ++ t') →
  sequential_full_trace (t ++ (tag, #"(")%V :: (tag, #")")%V :: t').
Proof.
  set tt := t ++ t'. intros Htt. assert (tt = t ++ t') as HH by done. revert HH; clearbody tt.
  revert t t'. induction Htt as [| tag' |].
  { intros ? ? [-> ->]%eq_sym%app_eq_nil. cbn. apply sequential_call. }
  { intros t1 t2 HH. rewrite app_comm_cons in HH.
    apply app_eq_inv in HH as [HH|HH].
    { destruct HH as [? [Ht1 Ht2]]. subst.
      destruct t1.
      { cbn in *. subst. cbn.
        pose proof (sequential_full_trace_app _ _ (sequential_call tag)
                     (sequential_full_trace_wrap tag' t Htt)). done. }
      { cbn in *. inversion Ht1; subst. specialize (IHHtt _ _ eq_refl).
        pose proof (sequential_full_trace_wrap tag' _ IHHtt). rewrite -app_assoc // in H. } }
    { destruct HH as [? [Ht1 Ht2]]. subst. apply eq_sym, app_eq_unit in Ht2.
      destruct_or!; destruct_and!; subst; cbn.
      { rewrite app_nil_r /=.
        pose proof (sequential_full_trace_app _ _ Htt (sequential_call tag)) as HH.
        pose proof (sequential_full_trace_wrap tag' _ HH). rewrite -app_assoc // in H. }
      { apply (sequential_full_trace_app _ _
                 (sequential_full_trace_wrap tag' _ Htt) (sequential_call tag)). } } }
  { intros t1 t2 Ht1t2. apply app_eq_inv in Ht1t2 as [HH|HH].
    { destruct HH as [? [-> ->]]. specialize (IHHtt1 _ _ eq_refl).
      pose proof (sequential_full_trace_app _ _ IHHtt1 Htt2) as HH. rewrite -app_assoc // in HH. }
    { destruct HH as [? [-> ->]]. specialize (IHHtt2 _ _ eq_refl).
      pose proof (sequential_full_trace_app _ _ Htt1 IHHtt2) as HH. rewrite -app_assoc //. } }
Qed.

Lemma sequential_with_opened_sequential o t :
  sequential_with_opened o t →
  sequential_trace_alt t.
Proof.
  set closing : list val → list val := map (λ tag, (tag, #")")%V).
  enough (Hind: sequential_with_opened o t → sequential_full_trace (t ++ closing o)).
  { intros Ho. specialize (Hind Ho). eexists. split; eauto.
    by apply prefix_app_r. }

  induction 1 as [| ? ? ? Ho Ht|].
  { rewrite /=. constructor. }
  { rewrite /=. eapply (sequential_full_trace_call_middle tag) in Ht. rewrite -app_assoc//. }
  { cbn in *. rewrite -app_assoc //. }
Qed.

Lemma prefix_snoc_inv {A} (l1 l2: list A) x :
  l1 `prefix_of` (l2 ++ [x]) →
  l1 = l2 ++ [x] ∨ l1 `prefix_of` l2.
Proof.
  revert l1 x. induction l2 as [| y l2].
  { cbn. intros ? ? HH. destruct l1. right; done.
    pose proof (prefix_cons_inv_1 _ _ _ _ HH) as ->.
    apply (prefix_cons_inv_2), prefix_nil_inv in HH. subst. by left. }
  { cbn. intros ? ? HH. destruct l1. right; by apply prefix_nil.
    pose proof (prefix_cons_inv_1 _ _ _ _ HH) as ->.
    apply (prefix_cons_inv_2), IHl2 in HH as [->|HH]. by left.
    right. by apply prefix_cons. }
Qed.

Lemma sequential_with_opened_open_front o t tag :
  sequential_with_opened o t →
  sequential_with_opened (o ++ [tag]) ((tag, #"(")%V :: t).
Proof.
  induction 1; cbn.
  { rewrite (_: [(tag, #"(")%V] = [] ++ (tag, #"(")%V :: nil) //.
    econstructor. constructor. }
  { rewrite (_: ∀ x, (tag, #"(")%V :: t ++ x = ((tag, #"(")%V :: t) ++ x) //.
    by econstructor. }
  { rewrite (_: ∀ x, (tag, #"(")%V :: t ++ x = ((tag, #"(")%V :: t) ++ x) //.
    by econstructor. }
Qed.

Lemma sequential_with_opened_app o t o' t' :
  sequential_with_opened o t →
  sequential_with_opened o' t' →
  sequential_with_opened (o' ++ o) (t ++ t').
Proof.
  intros H1 H2. revert o t H1. induction H2.
  { intros. rewrite app_nil_r //=. }
  { intros o1 t1 Hot1. cbn. rewrite app_assoc. econstructor.
    eauto. }
  { intros o1 t1 Hot1. rewrite app_assoc. econstructor. eauto. }
Qed.

Lemma sequential_full_trace_with_opened_nil t :
  sequential_full_trace t →
  sequential_with_opened [] t.
Proof.
  induction 1.
  { constructor. }
  { rewrite (_: ∀ x, (tag, #"(")%V :: t ++ x = ((tag, #"(")%V :: t) ++ x) //.
    econstructor.
    rewrite (_: [tag] = [] ++ [tag]) //.
    by eapply sequential_with_opened_open_front. }
  { rewrite (_: [] = [] ++ []) //. by eapply sequential_with_opened_app. }
Qed.

Lemma sequential_with_opened_prefix o t t' :
  sequential_with_opened o t →
  t' `prefix_of` t →
  ∃ o', sequential_with_opened o' t'.
Proof.
  revert o t'. induction t using rev_ind.
  { intros ? ? ? ->%prefix_nil_inv. eexists. econstructor. }
  { intros ? ? Hseq. inversion Hseq; simplify_list_eq.
    { exfalso. destruct t; simplify_list_eq. }
    { intros [->|Hpre]%prefix_snoc_inv; eauto. }
    { intros [->|Hpre]%prefix_snoc_inv; eauto. } }
Qed.

Lemma sequential_with_opened_of_sequential t :
  sequential_trace_alt t →
  ∃ o, sequential_with_opened o t.
Proof.
  intros [t' [Ht' Htt']].
  apply sequential_full_trace_with_opened_nil in Ht'.
  eapply sequential_with_opened_prefix in Ht'; eauto.
Qed.

Lemma sequential_trace_alt_iff t :
  sequential_trace t ↔ sequential_trace_alt t.
Proof.
  split.
  { by intros [? ?%sequential_with_opened_sequential]. }
  { by intros ?%sequential_with_opened_of_sequential. }
Qed.
