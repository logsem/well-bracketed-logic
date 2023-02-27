(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From WBLogrel.heap_lang Require Export primitive_laws.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

(** The [array] connective is a version of [mapsto] that works
with lists of values. *)

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context `{!wbheapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

(** * Rules for allocation *)

Lemma wbwp_allocN E out v n :
  (0 < n)%Z →
  {WB{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ out; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof. iIntros (? Φ) "_ HΦ". iApply wp_wbwp; iApply wp_allocN; done. Qed.

Lemma wbwp_allocN_vec E out v n :
  (0 < n)%Z →
  {WB{{ True }}}
    AllocN #n v @ out ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof. iIntros (? Φ) "_ HΦ". iApply wp_wbwp; iApply wp_allocN_vec; done. Qed.

(** * Rules for accessing array elements *)
Lemma wbwp_load_offset E out l dq off vs v :
  vs !! off = Some v →
  {WB{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ out; E {{{ RET v; l ↦∗{dq} vs }}}.
Proof.
  iIntros (? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_load_offset with "[$Hl] [$]"); first done.
Qed.

Lemma wbwp_load_offset_vec E out l dq sz (off : fin sz) (vs : vec val sz) :
  {WB{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ out; E {{{ RET vs !!! off; l ↦∗{dq} vs }}}.
Proof. apply wbwp_load_offset. by apply vlookup_lookup. Qed.

Lemma wbwp_store_offset E out l off vs v :
  is_Some (vs !! off) →
  {WB{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ out; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof. iIntros (? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_store_offset with "[$Hl] [$]"); done. Qed.

Lemma wbwp_store_offset_vec E out l sz (off : fin sz) (vs : vec val sz) v :
  {WB{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ out; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof. iIntros (Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_store_offset_vec with "[$] [$]"). Qed.

Lemma wbwp_xchg_offset E out l off vs v v' :
  vs !! off = Some v →
  {WB{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v' @ out; E {{{ RET v; l ↦∗ <[off:=v']> vs }}}.
Proof. iIntros (? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_xchg_offset with "[$Hl] [$]"); done. Qed.

Lemma wbwp_xchg_offset_vec E out l sz (off : fin sz) (vs : vec val sz) v :
   {WB{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v @ out; E {{{ RET (vs !!! off); l ↦∗ vinsert off v vs }}}.
Proof. iIntros (Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_xchg_offset_vec with "[$] [$]"). Qed.

Lemma wbwp_cmpxchg_suc_offset E out l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {WB{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ out; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (??? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_cmpxchg_suc_offset with "[$Hl] [$]"); done.
Qed.

Lemma wbwp_cmpxchg_suc_offset_vec E out l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {WB{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ out; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_cmpxchg_suc_offset_vec with "[$] [$]"); done.
Qed.

Lemma wbwp_cmpxchg_fail_offset E out l dq off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {WB{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ out; E
  {{{ RET (v0, #false); l ↦∗{dq} vs }}}.
Proof.
  iIntros (??? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_cmpxchg_fail_offset with "[$Hl] [$]"); done.
Qed.

Lemma wbwp_cmpxchg_fail_offset_vec E out l dq sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {WB{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ out; E
  {{{ RET (vs !!! off, #false); l ↦∗{dq} vs }}}.
Proof.
  intros. eapply wbwp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma wbwp_faa_offset E out l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {WB{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ out; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof. iIntros (? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_faa_offset with "[$Hl] [$]"); done. Qed.

Lemma wbwp_faa_offset_vec E out l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {WB{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ out; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof. iIntros (? Φ) "Hl HΦ". iApply wp_wbwp; iApply (wp_faa_offset_vec with "[$Hl] [$]"); done. Qed.

(** Derived prophecy laws *)

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wbwp_resolve_proph E out (p : proph_id) (pvs : list (val * val)) v :
  {WB{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ out; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof. iIntros (Φ) "Hp HΦ". iApply wp_wbwp; iApply (wp_resolve_proph with "[$] [$]"). Qed.

Lemma wbwp_resolve_cmpxchg_suc E out l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {WB{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ out; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (? Φ) "? HΦ". iApply wp_wbwp; iApply (wp_resolve_cmpxchg_suc with "[$] [$]"); done.
Qed.

Lemma wbwp_resolve_cmpxchg_fail E out l (p : proph_id) (pvs : list (val * val)) dq v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {WB{{ proph p pvs ∗ ▷ l ↦{dq} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ out; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) "? HΦ". iApply wp_wbwp; iApply (wp_resolve_cmpxchg_fail with "[$] [$]"); done.
Qed.

End lifting.
