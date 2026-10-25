/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Explicit coordinates for an invariant subspace written as a graph. -/

namespace FD56
open Matrix
variable {R s t m : Type*} [CommRing R]
  [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]

def graphSubspaceBasis (C : Matrix t s R) : Matrix (s ⊕ t) s R :=
  Matrix.fromRows 1 C

def graphCoordinateChange (C : Matrix t s R) : Matrix (s ⊕ t) (s ⊕ t) R :=
  Matrix.fromBlocks 1 0 C 1

theorem graphCoordinateChange_mul_neg (C : Matrix t s R) :
    graphCoordinateChange C * graphCoordinateChange (-C) = 1 := by
  simp [graphCoordinateChange, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem graphCoordinateChange_neg_mul (C : Matrix t s R) :
    graphCoordinateChange (-C) * graphCoordinateChange C = 1 := by
  simpa using graphCoordinateChange_mul_neg (-C)

theorem graphCoordinateChange_basis (C : Matrix t s R) :
    graphCoordinateChange (-C) * graphSubspaceBasis C =
      Matrix.fromRows (1 : Matrix s s R) (0 : Matrix t s R) := by
  simp [graphCoordinateChange, graphSubspaceBasis, Matrix.fromBlocks_mul_fromRows]

theorem graphCoordinateChange_left_columns (C : Matrix t s R)
    (N : Matrix m (s ⊕ t) R) :
    (N * graphCoordinateChange C).submatrix id Sum.inl = N * graphSubspaceBasis C := by
  ext i j
  simp [Matrix.mul_apply, graphCoordinateChange, graphSubspaceBasis,
    Fintype.sum_sum_type]

theorem graph_invariant_lower_left_zero (C : Matrix t s R)
    (M : Matrix (s ⊕ t) (s ⊕ t) R) (B : Matrix s s R)
    (h : M * graphSubspaceBasis C = graphSubspaceBasis C * B) :
    (graphCoordinateChange (-C) * M * graphCoordinateChange C).toBlocks₂₁ = 0 := by
  have he := graphCoordinateChange_left_columns C (graphCoordinateChange (-C) * M)
  rw [Matrix.mul_assoc (graphCoordinateChange (-C)) M (graphSubspaceBasis C), h,
    ← Matrix.mul_assoc (graphCoordinateChange (-C)) (graphSubspaceBasis C) B,
    graphCoordinateChange_basis,
    Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul] at he
  ext i j
  exact congrArg (fun A => A (Sum.inr i) j) he

theorem graph_annihilator_left_zero (C : Matrix t s R) (P : Matrix m (s ⊕ t) R)
    (h : P * graphSubspaceBasis C = 0) :
    (P * graphCoordinateChange C).submatrix id Sum.inl = 0 := by
  rw [graphCoordinateChange_left_columns, h]

theorem graph_state_reconstruction (C : Matrix t s R)
    (M : Matrix (s ⊕ t) (s ⊕ t) R) :
    graphCoordinateChange C * (graphCoordinateChange (-C) * M * graphCoordinateChange C) *
      graphCoordinateChange (-C) = M := by
  calc
    _ = (graphCoordinateChange C * graphCoordinateChange (-C)) * M *
      (graphCoordinateChange C * graphCoordinateChange (-C)) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [graphCoordinateChange_mul_neg]; simp

theorem graph_output_reconstruction (C : Matrix t s R) (P : Matrix m (s ⊕ t) R) :
    (P * graphCoordinateChange C) * graphCoordinateChange (-C) = P := by
  rw [Matrix.mul_assoc, graphCoordinateChange_mul_neg, Matrix.mul_one]

omit [DecidableEq t] in
/-- Invariance of a matrix range gives a matrix for the restricted endomorphism. -/
theorem matrix_restriction_of_range_invariant (A : Matrix (s ⊕ t) s R)
    (M : Matrix (s ⊕ t) (s ⊕ t) R)
    (h : ∀ x ∈ LinearMap.range (Matrix.toLin' A),
      M *ᵥ x ∈ LinearMap.range (Matrix.toLin' A)) :
    ∃ B : Matrix s s R, M * A = A * B := by
  classical
  have hc (j : s) : ∃ w : s → R, A *ᵥ w = fun i => (M * A) i j := by
    have hr : A *ᵥ (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' A) :=
      ⟨Pi.single j 1, rfl⟩
    obtain ⟨w, hw⟩ := h _ hr
    refine ⟨w, ?_⟩
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] using hw
  choose w hw using hc
  refine ⟨fun i j => w j i, ?_⟩
  ext i j
  exact (congrFun (hw j) i).symm

theorem graph_invariant_lower_left_zero_of_range (C : Matrix t s R)
    (M : Matrix (s ⊕ t) (s ⊕ t) R)
    (h : ∀ x ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)),
      M *ᵥ x ∈ LinearMap.range (Matrix.toLin' (graphSubspaceBasis C))) :
    (graphCoordinateChange (-C) * M * graphCoordinateChange C).toBlocks₂₁ = 0 := by
  obtain ⟨B, hB⟩ := matrix_restriction_of_range_invariant (graphSubspaceBasis C) M h
  exact graph_invariant_lower_left_zero C M B hB

end FD56
