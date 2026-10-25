/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.InvariantSubspaceCoordinates
import FD56.LinearAlgebra.FullKrylovGeneratorBound

/-! Field generators for an invariant graph contained in an output kernel. -/

noncomputable section
namespace FD56
open Matrix

universe u v w w' w''

/-- The graph coordinates, three unrestricted state blocks, and the free output block. -/
abbrev InvariantGraphChartIndex (s t m : Type*) :=
  (t × s) ⊕ ((s × s) ⊕ ((s × t) ⊕ ((t × t) ⊕ (m × t))))

def invariantGraphChartGenerators {F s t m : Type*} [Field F]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (C : Matrix t s F) (M : Matrix (s ⊕ t) (s ⊕ t) F)
    (P : Matrix m (s ⊕ t) F) : InvariantGraphChartIndex s t m → F :=
  let N := graphCoordinateChange (-C) * M * graphCoordinateChange C
  let Q := P * graphCoordinateChange C
  Sum.elim (fun ij => C ij.1 ij.2)
    (Sum.elim (fun ij => N (Sum.inl ij.1) (Sum.inl ij.2))
      (Sum.elim (fun ij => N (Sum.inl ij.1) (Sum.inr ij.2))
        (Sum.elim (fun ij => N (Sum.inr ij.1) (Sum.inr ij.2))
          (fun ij => Q ij.1 (Sum.inr ij.2)))))

theorem matrix_mul_entries_mem_subfield {F a b c : Type*} [Field F] [Fintype b]
    (S : Subfield F) (A : Matrix a b F) (B : Matrix b c F)
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    ∀ i j, (A * B) i j ∈ S := by
  intro i j
  exact S.sum_mem (fun k _ => S.mul_mem (hA i k) (hB k j))

theorem graphCoordinateChange_entries_mem_subfield {F s t : Type*} [Field F]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (S : Subfield F) (C : Matrix t s F) (hC : ∀ i j, C i j ∈ S) :
    ∀ i j, graphCoordinateChange C i j ∈ S := by
  intro i j
  cases i <;> cases j <;>
    simp only [graphCoordinateChange, Matrix.fromBlocks, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.one_apply, Matrix.zero_apply]
  · split_ifs <;> first | exact S.one_mem | exact S.zero_mem
  · exact S.zero_mem
  · exact hC _ _
  · split_ifs <;> first | exact S.one_mem | exact S.zero_mem

/-- Reconstruction proves generation from the original entries and the two subspace conditions. -/
theorem invariantGraphChartGenerators_adjoin_eq_top
    {K : Type u} {F : Type v} {s : Type w} {t : Type w'} {m : Type w''}
    [Field K] [Field F] [Algebra K F] [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (C : Matrix t s F) (M : Matrix (s ⊕ t) (s ⊕ t) F)
    (P : Matrix m (s ⊕ t) F)
    (hinv : ∀ x ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)),
      M *ᵥ x ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)))
    (hker : P * graphSubspaceBasis C = 0)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    IntermediateField.adjoin K (Set.range (invariantGraphChartGenerators C M P)) = ⊤ := by
  classical
  let S := IntermediateField.adjoin K (Set.range (invariantGraphChartGenerators C M P))
  let N := graphCoordinateChange (-C) * M * graphCoordinateChange C
  let Q := P * graphCoordinateChange C
  have hC : ∀ i j, C i j ∈ S := by
    intro i j
    exact IntermediateField.subset_adjoin K _ ⟨Sum.inl (i, j), rfl⟩
  have hT := graphCoordinateChange_entries_mem_subfield S.toSubfield C hC
  have hU := graphCoordinateChange_entries_mem_subfield S.toSubfield (-C)
    (fun i j => S.neg_mem (hC i j))
  have hNzero := graph_invariant_lower_left_zero_of_range C M hinv
  have hN : ∀ i j, N i j ∈ S := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact IntermediateField.subset_adjoin K _ ⟨Sum.inr (Sum.inl (i, j)), rfl⟩
      | inr j =>
        exact IntermediateField.subset_adjoin K _ ⟨Sum.inr (Sum.inr (Sum.inl (i, j))), rfl⟩
    | inr i =>
      cases j with
      | inl j =>
        have hij : N (Sum.inr i) (Sum.inl j) = 0 :=
          congrArg (fun B => B i j) hNzero
        rw [hij]
        exact S.zero_mem
      | inr j =>
        exact IntermediateField.subset_adjoin K _
          ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))), rfl⟩
  have hQzero := graph_annihilator_left_zero C P hker
  have hQ : ∀ i j, Q i j ∈ S := by
    intro i j
    cases j with
    | inl j =>
      have hij : Q i (Sum.inl j) = 0 := congrArg (fun B => B i j) hQzero
      rw [hij]
      exact S.zero_mem
    | inr j =>
      exact IntermediateField.subset_adjoin K _
        ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, j)))), rfl⟩
  have hM : ∀ i j, M i j ∈ S := by
    rw [← graph_state_reconstruction C M]
    exact matrix_mul_entries_mem_subfield S.toSubfield _ _
      (matrix_mul_entries_mem_subfield S.toSubfield _ _ hT hN) hU
  have hP : ∀ i j, P i j ∈ S := by
    rw [← graph_output_reconstruction C P]
    exact matrix_mul_entries_mem_subfield S.toSubfield _ _ hQ hU
  have hle : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ij, rfl⟩
    cases ij with
    | inl ij => exact hM ij.1 ij.2
    | inr ij => exact hP ij.1 ij.2
  exact top_unique (hgen ▸ hle)

theorem invariantGraphChartIndex_card {s t m : Type*}
    [Fintype s] [Fintype t] [Fintype m] :
    Fintype.card (InvariantGraphChartIndex s t m) =
      (Fintype.card s + Fintype.card t) ^ 2 + Fintype.card m * Fintype.card t := by
  simp only [InvariantGraphChartIndex, Fintype.card_sum, Fintype.card_prod]
  ring

theorem invariantGraphChartIndex_card_eq_sub {s t m : Type*}
    [Fintype s] [Fintype t] [Fintype m] :
    Fintype.card (InvariantGraphChartIndex s t m) =
      (Fintype.card s + Fintype.card t) ^ 2 +
        Fintype.card m * (Fintype.card s + Fintype.card t) -
          Fintype.card m * Fintype.card s := by
  rw [invariantGraphChartIndex_card, Nat.mul_add]
  omega

/-- An invariant graph of dimension `s` removes `m*s` generators. -/
theorem trdeg_le_invariantGraphChart_bound
    {K : Type u} {F : Type v} {s : Type w} {t : Type w'} {m : Type w''}
    [Field K] [Field F] [Algebra K F] [Fintype s] [Fintype t] [Fintype m]
    [DecidableEq s] [DecidableEq t]
    (C : Matrix t s F) (M : Matrix (s ⊕ t) (s ⊕ t) F)
    (P : Matrix m (s ⊕ t) F)
    (hinv : ∀ x ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)),
      M *ᵥ x ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)))
    (hker : P * graphSubspaceBasis C = 0)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Algebra.trdeg K F ≤
      (((Fintype.card s + Fintype.card t) ^ 2 + Fintype.card m * Fintype.card t : ℕ) :
        Cardinal.{v}) := by
  rw [← invariantGraphChartIndex_card]
  exact trdeg_le_card_of_finite_field_generators (invariantGraphChartGenerators C M P)
    (invariantGraphChartGenerators_adjoin_eq_top C M P hinv hker hgen)

theorem card_algebraicIndependent_le_invariantGraphChart_bound
    {K : Type u} {F : Type v} {s : Type w} {t : Type w'} {m : Type w''} {κ : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype s] [Fintype t] [Fintype m] [Fintype κ]
    [DecidableEq s] [DecidableEq t]
    {x : κ → F} (hx : AlgebraicIndependent K x)
    (C : Matrix t s F) (M : Matrix (s ⊕ t) (s ⊕ t) F)
    (P : Matrix m (s ⊕ t) F)
    (hinv : ∀ z ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)),
      M *ᵥ z ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)))
    (hker : P * graphSubspaceBasis C = 0)
    (hgen : IntermediateField.adjoin K (Set.range (matrixEntryGenerators M P)) = ⊤) :
    Fintype.card κ ≤
      (Fintype.card s + Fintype.card t) ^ 2 + Fintype.card m * Fintype.card t := by
  rw [← invariantGraphChartIndex_card]
  exact card_le_card_of_algebraicIndependent_of_finite_field_generators hx
    (invariantGraphChartGenerators C M P)
    (invariantGraphChartGenerators_adjoin_eq_top C M P hinv hker hgen)

end FD56
