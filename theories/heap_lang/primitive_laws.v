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
From iris.heap_lang Require Export class_instances.
From iris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

Class wbheapGS Σ := WBHeapGS {
  wbheapGS_invGS : invGS_gen HasLc Σ;
  wbheapGS_gen_heapGS :: gen_heapGS loc (option val) Σ;
  wbheapGS_inv_heapGS :: inv_heapGS loc (option val) Σ;
  wbheapGS_proph_mapGS :: proph_mapGS proph_id (val * val) Σ;
  wbheapGS_step_name : gname;
  wbheapGS_step_cnt : mono_natG Σ;
  wbheapGS_gstacksGS :: gstacksIG Σ;
}.
Local Existing Instance wbheapGS_step_cnt.

Global Instance wbheapGS_heapGS `{!wbheapGS Σ} : heapGS Σ :=
  HeapGS HasLc Σ wbheapGS_invGS _ _ _ wbheapGS_step_name _.

Section lifting.
Context `{!wbheapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

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
Lemma wp_rec_löb s E f x e Φ Ψ :
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
