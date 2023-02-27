 (** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.heap_lang Require Export primitive_laws.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre.
From WBLogrel.program_logic Require Export weakestpre lifting.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From WBLogrel.heap_lang_trace Require Import class_instances.
From WBLogrel.heap_lang_trace Require Import tactics notation.
From WBLogrel.heap_lang_trace Require Import trace_resources.
From WBLogrel.heap_lang_trace Require Import lang.
From iris.prelude Require Import options.

Class wbheapGS Σ := WBHeapGS {
  wbheapGS_invGS : invGS_gen HasLc Σ;
  wbheapGS_gen_heapGS :> gen_heapGS loc (option val) Σ;
  wbheapGS_inv_heapGS :> inv_heapGS loc (option val) Σ;
  wbheapGS_proph_mapGS :> proph_mapGS proph_id (val * val) Σ;
  wbheapGS_step_name : gname;
  wbheapGS_step_cnt : mono_natG Σ;
  wbheapGS_gstacksGS :> gstacksIG Σ;
  wbheapGS_traceGS :> traceGS Σ;
}.
Local Existing Instance wbheapGS_step_cnt.

Section steps.
  Context `{!wbheapGS Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own wbheapGS_step_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own wbheapGS_step_name n.

  Local Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Local Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Local Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_lb_own_le. Qed.

End steps.

Global Program Instance wbheapG_irisG `{!wbheapGS Σ} : irisGS_gen HasLc heap_lang Σ := {
  iris_invGS := wbheapGS_invGS;
  state_interp σ step_cnt κs _ :=
    (gen_heap_interp σ.(heap)
     ∗ trace_auth σ.(trace)
     ∗ proph_map_interp κs σ.(used_proph_id)
     ∗ steps_auth step_cnt)%I;
  fork_post _ := True%I;
  num_laters_per_step n := n
}.
Next Obligation.
  iIntros (?? σ ns κs nt)  "/= ($ & $ & $ & H)".
  by iMod (steps_auth_update_S with "H") as "$".
Qed.


(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
Notation "l ↦ dq v" := (mapsto (L:=loc) (V:=option val) l dq (Some v%V))
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{!wbheapGS Σ}.
  Definition inv_mapsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_mapsto_own l (Some v) (from_option I False).
  Definition inv_mapsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_mapsto l (from_option I False).
End definitions.

Global Instance: Params (@inv_mapsto_own) 4 := {}.
Global Instance: Params (@inv_mapsto) 3 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option val)).
Notation "l '↦_' I □" := (inv_mapsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_mapsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

Section lifting.
Context `{!wbheapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wp_lb_init s E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP e @ s; E {{ v, Φ v }}) -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (->) "Hwp".
  iIntros (σ1 ns κ κs m) "(Hσ & Ht & Hκ & Hsteps)".
  iDestruct (steps_lb_get with "Hsteps") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb0"; [lia|].
  iSpecialize ("Hwp" with "Hlb0"). iApply ("Hwp" $! σ1 ns κ κs m). iFrame.
Qed.

Lemma wp_lb_update s n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP e @ s; E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (->) "Hlb Hwp".
  iIntros (σ1 ns κ κs m) "(Hσ & Ht & Hκ & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hwp" $! σ1 ns κ κs m with "[$Hσ $Ht $Hκ $Hsteps]") as "[%Hs Hwp]".
  iModIntro. iSplit; [done|].
  iIntros (e2 σ2 efs Hstep) "Hcred".
  iMod ("Hwp" with "[//] Hcred") as "Hwp".
  iIntros "!> !>". iMod "Hwp" as "Hwp". iIntros "!>".
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp". iMod "Hwp" as "(($ & $ & $ & Hsteps)& Hwp & $)".
  iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
  iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
  iModIntro. iFrame "Hsteps".
  iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma wp_step_fupdN_lb s n E1 E2 e P Φ :
  TCEq (to_val e) None →
  E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hlb HP Hwp".
  iApply wp_step_fupdN; [done|].
  iSplit; [|by iFrame].
  iIntros (σ ns κs nt) "(? & ? & ? & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %Hle.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_". iPureIntro. rewrite /num_laters_per_step /=. lia.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb s E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ s; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first done.
  iIntros "!> _". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Specification for [emit]. Adds an event to the trace. *)
Lemma wp_emit s E tr v N (I: list val → Prop) :
  ↑N ⊆ E →
  I (tr ++ [v]) →
  {{{ trace_is tr ∗ trace_inv N I }}}
    Emit v @ s; E
  {{{ RET (LitV LitUnit); trace_is (tr ++ [v]) }}}.
Proof.
  iIntros (Hι HI φ) "[Ht Hi] Hφ".
  iInv "Hi" as ">Hi" "Hclose".
  iDestruct "Hi" as (tr') "[Htr' _]".
  iDestruct (trace_half_frag_agree with "Htr' Ht") as %->.
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 ? κ κs n) "(? & Hta & ? & Hsteps) !>";
    iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  iDestruct (trace_agree with "Hta Ht") as %<-.
  iMod (trace_add_event with "Hta Ht Htr'") as "(Hta&Ht&Htr')".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iFrame. iSplitL; last done.
  iMod ("Hclose" with "[Htr']"). { iNext. eauto. }
  iModIntro. by iApply "Hφ".
Qed.

(** Specification for [fresh]. Emits an event annotated with a fresh tag. *)
Lemma wp_fresh s E tr v N (I: list val → Prop) :
  ↑N ⊆ E →
  (∀ (tag:string), tag ∉ tags tr → I (tr ++ [(#tag, v)%V])) →
  {{{ trace_is tr ∗ trace_inv N I }}}
    Fresh v @ s; E
  {{{ (tag:string), RET (LitV tag); trace_is (tr ++ [(#tag, v)%V]) ∗ ⌜tag ∉ tags tr⌝}}}.
Proof.
  iIntros (Hι HI φ) "[Ht Hi] Hφ".
  iInv "Hi" as ">Hi" "Hclose".
  iDestruct "Hi" as (tr') "[Htr' _]".
  iDestruct (trace_half_frag_agree with "Htr' Ht") as %->.
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 ? κ κs n) "(? & Hta & ? & Hsteps) !>".
  pose proof (infinite_is_fresh (tags σ1.(trace))).
  iSplit; [ by eauto with head_step |]. iNext.
  iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  iDestruct (trace_agree with "Hta Ht") as %<-.
  iMod (trace_add_event with "Hta Ht Htr'") as "(Hta & Ht & Htr')".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iFrame. iSplitL; last done.
  iMod ("Hclose" with "[Htr']"). { iNext. eauto. }
  iModIntro. iApply "Hφ". eauto.
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 ns κ κs nt) "(?&?&?&Hsteps) !>"; iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_"; inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  by iFrame.
Qed.

Lemma twp_fork s E e Φ :
  WP e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP Fork e @ s; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1 ns κs nt) "(?&?&?&Hsteps) !>"; iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  by iFrame.
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [= ?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[= ?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. apply mapsto_persist. Qed.

Global Instance inv_mapsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto_own. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.
Global Instance inv_mapsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto. f_equiv=>-[w|]; last done.
  simpl. apply HI.
Qed.

Lemma make_inv_mapsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
Proof. iIntros (??) "#HI Hl". iApply make_inv_mapsto; done. Qed.
Lemma inv_mapsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_mapsto_own_inv. Qed.

Lemma inv_mapsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
      inv_mapsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_mapsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_acc with "Hinv Hl") as ([v|]) "(% & Hl & Hclose)"; [done| |done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.mapsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma twp_allocN_seq s E v n :
  (0 < n)%Z →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>"; iSplit; first by destruct n; auto with lia head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; do 2 (iSplit; first done). iFrame "Hσ Ht Hκs Hsteps". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.
Lemma wp_allocN_seq s E v n :
  (0 < n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN_seq; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_alloc s E v :
  [[{ True }]] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_allocN_seq; [auto with lia..|].
  iIntros (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.
Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_alloc; [by auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_free s E l v :
  [[{ l ↦ v }]] Free (Val $ LitV $ LitLoc l) @ s; E
  [[{ RET LitV LitUnit; True }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_free s E l v :
  {{{ ▷ l ↦ v }}} Free (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_free with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_load s E l dq v :
  [[{ l ↦{dq} v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{dq} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; [done|]. iSplit; [done|]. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_load s E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load with "H"). iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_store s E l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_xchg s E l v' v :
  [[{ l ↦ v' }]] Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET v'; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_xchg s E l v' v :
  {{{ ▷ l ↦ v' }}} Xchg (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET v'; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg with "H"); [by auto..|]. iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Ht & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ e2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done). iFrame. by iApply "HΦ".
Qed.
Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "(Hσ & Ht & HR & Hsteps) !>". iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep) "_". inv_head_step.
  rename select proph_id into p.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit; first done. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_head_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_head_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_head_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_head_step.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 ns κ κs nt) "(Hσ & Ht & Hκ & Hsteps)".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 ns [] κs nt with "[$Hσ $Ht $Hκ $Hsteps]") as "[Hs WPe]".
    iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_head_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -assoc.
    iMod ("WPe" $! σ1 ns _ _ nt with "[$Hσ $Ht $Hκ $Hsteps]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step) "Hcred". apply step_resolve in step; last done.
    inv_head_step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%] Hcred") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "WPe". iModIntro.
    iApply (step_fupdN_wand with "WPe"); iIntros "> [($ & $ & Hκ & $) WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

Lemma wbwp_lb_init E out e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WBWP e @ out; E {{ v, Φ v }}) -∗
  WBWP e @ out; E {{ Φ }}.
Proof.
  rewrite /wbwp. iIntros (?) "Hwp". iIntros (M) "HM".
  iApply (wp_lb_init  with "[Hwp HM]").
  iIntros "Hslb". iApply ("Hwp" with "[$] [$]").
Qed.

Lemma wbwp_lb_update n E out e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WBWP e @ out; E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  WBWP e @ out; E {{ Φ }}.
Proof.
  rewrite /wbwp. iIntros (?) "Hslb Hwp". iIntros (M) "HM".
  iApply (wp_lb_update  with "[$Hslb]").
  iApply (wp_wand with "[Hwp HM]"); first by iApply "Hwp".
  iIntros (?). iDestruct 1 as (?) "(?&?&H)". iIntros "Hslb".
  iExists _; iFrame; iApply "H"; done.
Qed.

Lemma wbwp_step_fupdN_lb n E1 E2 out e P Φ :
  TCEq (to_val e) None →
  E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  WBWP e @ out; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WBWP e @ out; E1 {{ Φ }}.
Proof.
  iIntros (He HE) "Hlb HP Hwp".
  rewrite /wbwp.
  iIntros (?) "HM".
  iApply (wp_step_fupdN_lb with "[$] [$]"); [done|].
  iApply (wp_wand with "[Hwp HM]"); first by iApply "Hwp".
  iIntros (?). iDestruct 1 as (?) "(?&?&H)". iIntros "HP".
  iMod ("H" with "HP"); iModIntro.
  iExists _; iFrame.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wbwp_rec_löb s E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WBWP (rec: f x := e)%V v @ s; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WBWP (subst' x v (subst' f (rec: f x := e) e)) @ s; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WBWP (rec: f x := e)%V v @ s; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply wbwp_pure_step_later; first done.
  iIntros "!> _". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(* Forks break well-bracketedness! *)
(* (** Fork: Not using Texan triples to avoid some unnecessary [True] *) *)
(* Lemma wp_fork s E e Φ : *)
(*   ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|]. *)
(*   iIntros (σ1 ns κ κs nt) "(?&?&Hsteps) !>"; iSplit; first by eauto with head_step. *)
(*   iIntros "!>" (v2 σ2 efs Hstep) "_"; inv_head_step. *)
(*   iMod (steps_auth_update_S with "Hsteps") as "Hsteps". *)
(*   by iFrame. *)
(* Qed. *)

(** Heap *)

Lemma wbwp_allocN_seq E out v n :
  (0 < n)%Z →
  {WB{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ out; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof. iIntros (Hn Φ) "_ HΦ"; iApply wp_wbwp; iApply wp_allocN_seq; done. Qed.

Lemma wbwp_alloc E out v :
  {WB{{ True }}} Alloc (Val v) @ out; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof. iIntros (Φ) "_ HΦ". iApply wp_wbwp; iApply wp_alloc; done. Qed.

Lemma wbwp_free E out l v :
  {WB{{ ▷ l ↦ v }}} Free (Val $ LitV (LitLoc l)) @ out; E
  {{{ RET LitV LitUnit; True }}}.
Proof. iIntros (Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_free with "[$] [$]"). Qed.

Lemma wbwp_load E out l dq v :
  {WB{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ out; E {{{ RET v; l ↦{dq} v }}}.
Proof. iIntros (Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_load with "[$] [$]"). Qed.

Lemma wbwp_store E out l v' v :
  {WB{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ out; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof. iIntros (Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_store with "[$] [$]"). Qed.

Lemma wbwp_xchg E out l v' v :
  {WB{{ ▷ l ↦ v' }}} Xchg (Val $ LitV (LitLoc l)) (Val v) @ out; E
  {{{ RET v'; l ↦ v }}}.
Proof. iIntros (Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_xchg with "[$] [$]"). Qed.

Lemma wbwp_cmpxchg_fail E out l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {WB{{ ▷ l ↦{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ out; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof. iIntros (? ? Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_cmpxchg_fail with "[$] [$]"); done. Qed.

Lemma wbwp_cmpxchg_suc E out l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {WB{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ out; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof. iIntros (?? Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_cmpxchg_suc with "[$] [$]"); done. Qed.

Lemma wbwp_faa E out l i1 i2 :
  {WB{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ out; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof. iIntros (Φ) ">H HΦ". iApply wp_wbwp; iApply (wp_faa with "[$] [$]"). Qed.

Lemma wbwp_new_proph E out :
  {WB{{ True }}}
    NewProph @ out; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof. iIntros (Φ) "_ HΦ". iApply wp_wbwp; iApply (wp_new_proph with "[$] [$]"). Qed.

(** Specification for [emit]. Adds an event to the trace. *)
Lemma wbwp_emit s E tr v N (I: list val → Prop) :
  ↑N ⊆ E →
  I (tr ++ [v]) →
  {WB{{ trace_is tr ∗ trace_inv N I }}}
    Emit v @ s; E
  {{{ RET (LitV LitUnit); trace_is (tr ++ [v]) }}}.
Proof. iIntros (? ? Φ) "? HΦ". iApply wp_wbwp; by iApply (wp_emit with "[$]"). Qed.

(** Specification for [fresh]. Emits an event annotated with a fresh tag. *)
Lemma wbwp_fresh s E tr v N (I: list val → Prop) :
  ↑N ⊆ E →
  (∀ (tag:string), tag ∉ tags tr → I (tr ++ [(#tag, v)%V])) →
  {WB{{ trace_is tr ∗ trace_inv N I }}}
    Fresh v @ s; E
  {{{ (tag:string), RET (LitV tag); trace_is (tr ++ [(#tag, v)%V]) ∗ ⌜tag ∉ tags tr⌝}}}.
Proof. iIntros (? ? Φ) "? HΦ". iApply wp_wbwp; by iApply (wp_fresh with "[$]"). Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma wbwp_resolve E out e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WBWP e @ out; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WBWP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ out; E {{ Φ }}.
Proof.
  iIntros (??) "Hpr HWBWP".
  rewrite /wbwp.
  iIntros (?) "HM". iApply (wp_resolve with "[$]"); first done.
  iApply (wp_wand with "[HWBWP HM]"); first by iApply "HWBWP".
  iIntros (?); iDestruct 1 as (?) "(?&?&H)".
  iIntros (? ?) "?".
  iExists _; iFrame.
  iApply "H"; done.
Qed.

End lifting.
