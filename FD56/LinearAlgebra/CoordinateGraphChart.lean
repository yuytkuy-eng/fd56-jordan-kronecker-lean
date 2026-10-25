/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.FullKrylovBound
import FD56.LinearAlgebra.InvariantSubspaceCoordinates

/-! Every independent column family admits a coordinate graph chart. -/

noncomputable section
namespace FD56
open Matrix

@[simp] theorem coordinateEmbeddingSumEquiv_inr {s n : Type*} (r : s ↪ n)
    (j : {i : n // i ∉ Set.range r}) :
    coordinateEmbeddingSumEquiv r (Sum.inr j) = j.val := by
  rfl

theorem range_toLin_mul_right_of_right_inverse {F n s : Type*} [Field F]
    [Fintype s] [DecidableEq s] (A : Matrix n s F) (U V : Matrix s s F)
    (hUV : U * V = 1) :
    LinearMap.range (Matrix.toLin' (A * U)) = LinearMap.range (Matrix.toLin' A) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨U *ᵥ x, ?_⟩
    exact Matrix.mulVec_mulVec x A U
  · rintro ⟨x, rfl⟩
    refine ⟨V *ᵥ x, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, hUV,
      Matrix.mul_one]

/-- The selected minor supplies the inverse and the graph, rather than assuming a chart. -/
theorem exists_coordinate_graph_chart {F n s : Type*} [Field F]
    [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq s]
    (A : Matrix n s F) (hA : Function.Injective A.mulVec) :
    ∃ (r : s ↪ n) (C : Matrix {i : n // i ∉ Set.range r} s F) (U : Matrix s s F),
      (A.submatrix r id) * U = 1 ∧ U * (A.submatrix r id) = 1 ∧
      A.submatrix (coordinateEmbeddingSumEquiv r) id * U = graphSubspaceBasis C ∧
      LinearMap.range (Matrix.toLin' (A.submatrix (coordinateEmbeddingSumEquiv r) id)) =
        LinearMap.range (Matrix.toLin' (graphSubspaceBasis C)) := by
  classical
  obtain ⟨r, hr⟩ := exists_nonsingular_coordinate_embedding A hA
  let B := A.submatrix r id
  let U := B⁻¹
  let C : Matrix {i : n // i ∉ Set.range r} s F :=
    A.submatrix Subtype.val id * U
  have hBU : B * U = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hr)
  have hUB : U * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hr)
  have hchart : A.submatrix (coordinateEmbeddingSumEquiv r) id * U =
      graphSubspaceBasis C := by
    ext i j
    cases i with
    | inl i => exact congrArg (fun Q => Q i j) hBU
    | inr i => rfl
  refine ⟨r, C, U, hBU, hUB, hchart, ?_⟩
  rw [← hchart]
  exact (range_toLin_mul_right_of_right_inverse _ U B hUB).symm

end FD56
