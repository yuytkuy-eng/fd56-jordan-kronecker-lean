/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.InvariantSubspaceGeneratorBound

/-! Large independent families exclude invariant subspaces in an output kernel. -/

namespace FD56
open Matrix

theorem no_invariant_output_kernel_of_large_independent_family
    {K F n m κ : Type*} [Field K] [Field F] [Algebra K F]
    [Fintype n] [DecidableEq n] [Fintype m] [Fintype κ]
    {x : κ → F} (hx : AlgebraicIndependent K x)
    (hc : Fintype.card n ^ 2 + Fintype.card m * Fintype.card n - 1 ≤ Fintype.card κ)
    (hm : 2 ≤ Fintype.card m) (M : Matrix n n F) (P : Matrix m n F)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤)
    (W : Submodule F (n → F)) (hW : W ≠ ⊥)
    (hinv : ∀ w ∈ W, M *ᵥ w ∈ W) (hker : ∀ w ∈ W, P *ᵥ w = 0) : False := by
  have hb := hc.trans (card_algebraicIndependent_le_invariantSubspace_bound hx
    M P W hinv (fun _ hw => hker _ hw) hgen)
  have hs : 0 < Module.finrank F W := by
    exact Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))
  have hsn : Module.finrank F W ≤ Fintype.card n := by
    simpa using Submodule.finrank_le W
  have he := Nat.sub_add_cancel hsn
  have hms : 2 ≤ Fintype.card m * Module.finrank F W := by nlinarith
  have hbig : 0 < Fintype.card n ^ 2 + Fintype.card m * Fintype.card n := by nlinarith
  have hb' : Fintype.card n ^ 2 + Fintype.card m * Fintype.card n ≤
      Fintype.card n ^ 2 + Fintype.card m * (Fintype.card n - Module.finrank F W) + 1 := by
    omega
  nlinarith

end FD56
