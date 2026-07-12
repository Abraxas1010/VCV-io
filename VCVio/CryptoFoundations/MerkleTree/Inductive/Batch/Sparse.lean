/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Defs

/-! # Sparse Selectors for Batch Openings

Downstream consumers (FRI/STIR/WHIR-style query patterns) naturally hold a
**sparse list of leaf indices**, not a dense per-leaf mask. This file provides
the conversion `denseSelector : List (SkeletonLeafIndex s) → LeafData Bool s`
together with the two correspondence laws that make it transparent:

* `get_denseSelector_iff` — a leaf is selected iff its index is in the list;
* `anySelected_denseSelector_iff` — the selector opens something iff the list
  is nonempty.

Consumers can therefore work with index lists end-to-end and densify only at
the batch-opening API boundary, never paying for or exposing a full-tree mask.
-/

namespace InductiveMerkleTree

open BinaryTree

/-- Densify a sparse list of leaf indices into a selector: recursion on the
skeleton, routing each index into its subtree. -/
def denseSelector : {s : Skeleton} → List (SkeletonLeafIndex s) → LeafData Bool s
  | .leaf, idxs => .leaf (!idxs.isEmpty)
  | .internal _ _, idxs =>
    .internal
      (denseSelector (idxs.filterMap fun i => match i with
        | .ofLeft j => some j | .ofRight _ => none))
      (denseSelector (idxs.filterMap fun i => match i with
        | .ofRight j => some j | .ofLeft _ => none))

/-- **Correspondence**: a leaf is selected by the densified selector iff its
index occurs in the sparse list. -/
theorem get_denseSelector_iff {s : Skeleton} (idxs : List (SkeletonLeafIndex s))
    (i : SkeletonLeafIndex s) :
    (denseSelector idxs).get i = true ↔ i ∈ idxs := by
  induction i with
  | ofLeaf =>
    simp only [denseSelector, LeafData.get, Bool.not_eq_true']
    constructor
    · intro h
      match idxs, h with
      | j :: _, _ => cases j; exact List.mem_cons_self ..
    · intro h
      cases idxs with
      | nil => cases h
      | cons _ _ => rfl
  | ofLeft j ih =>
    simp only [denseSelector, LeafData.get, ih, List.mem_filterMap]
    constructor
    · rintro ⟨i', hi', hmatch⟩
      cases i' with
      | ofLeft j' => simp at hmatch; subst hmatch; exact hi'
      | ofRight _ => simp at hmatch
    · intro h
      exact ⟨.ofLeft j, h, rfl⟩
  | ofRight j ih =>
    simp only [denseSelector, LeafData.get, ih, List.mem_filterMap]
    constructor
    · rintro ⟨i', hi', hmatch⟩
      cases i' with
      | ofRight j' => simp at hmatch; subst hmatch; exact hi'
      | ofLeft _ => simp at hmatch
    · intro h
      exact ⟨.ofRight j, h, rfl⟩

/-- **Correspondence**: the densified selector opens at least one leaf iff the
sparse list is nonempty. -/
theorem anySelected_denseSelector_iff {s : Skeleton}
    (idxs : List (SkeletonLeafIndex s)) :
    (denseSelector idxs).anySelected = true ↔ idxs ≠ [] := by
  induction s with
  | leaf =>
    simp only [denseSelector, LeafData.anySelected, Bool.not_eq_true']
    constructor
    · intro h hnil; subst hnil; simp at h
    · intro h; cases idxs with
      | nil => exact absurd rfl h
      | cons _ _ => rfl
  | internal l r ihl ihr =>
    simp only [denseSelector, LeafData.anySelected, Bool.or_eq_true, ihl, ihr]
    constructor
    · rintro (h | h) hnil <;> subst hnil <;> simp at h
    · intro h
      match idxs, h with
      | i :: rest, _ =>
        cases i with
        | ofLeft j => left; simp
        | ofRight j => right; simp
