/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RectangularBlocks
import FD56.Stabilizer.BidiagonalSL

/-! A long rectangular block forces low-degree scalar corrections to vanish. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem mul_rectangularBlockPencil_transpose (e : ι → ℕ)
    (U : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i + 1)) K[X])
    (j : Σ i, Fin (e i)) (i : ι) (k : Fin (e i)) :
    (show Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i)) K[X] from
      U * (rectangularBlockPencil e).transpose) j ⟨i, k⟩ =
      (bidiagonalPencil (e i) *ᵥ (fun l => U j ⟨i, l⟩)) k := by
  simpa only [rectangularBlockPencil, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, mul_comm] using
      blockDiagonal_mulVec (fun i => bidiagonalPencil (K := K) (e i)) (U j) i k

theorem rectangular_scalar_low_degree_zero (e : ι → ℕ) (d : ℕ)
    (hmin : ∀ i, d < e i) (hlong : ∃ i, d + 1 < e i)
    (U : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i + 1)) K[X]) (c : K[X])
    (hU : U * (rectangularBlockPencil e).transpose =
      c • (1 : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i)) K[X]))
    (hdeg : DegreeBound U d) : U = 0 ∧ c = 0 := by
  obtain ⟨i, hi⟩ := hlong
  let V : Matrix (Fin (e i)) (Fin (e i + 1)) K[X] := fun j k => U ⟨i, j⟩ ⟨i, k⟩
  have hV : V * (bidiagonalPencil (e i)).transpose =
      c • (1 : Matrix (Fin (e i)) (Fin (e i)) K[X]) := by
    funext j k
    have hh := congrArg (fun A : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i)) K[X] =>
      A ⟨i, j⟩ ⟨i, k⟩) hU
    have hh' := (mul_rectangularBlockPencil_transpose e U ⟨i, j⟩ i k).symm.trans hh
    simpa [V, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.one_apply] using hh'
  have hc : c = 0 := (bidiagonal_scalar_low_degree_zero (e i) d hi V c hV
    (fun j k => hdeg ⟨i, j⟩ ⟨i, k⟩)).2
  refine ⟨?_, hc⟩
  funext j ⟨i, k⟩
  have hk : bidiagonalPencil (e i) *ᵥ (fun l => U j ⟨i, l⟩) = 0 := by
    funext l
    rw [← mul_rectangularBlockPencil_transpose]
    have hh := congrArg (fun A : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i)) K[X] =>
      A j ⟨i, l⟩) hU
    simpa [hc] using hh
  have hz := (bidiagonalPencil_degree_iff (e i) d (fun l => U j ⟨i, l⟩) hk).mp
    (fun l => hdeg j ⟨i, l⟩)
  have hz₀ : U j ⟨i, 0⟩ = 0 := by
    rcases hz with h | h
    · exact h
    · have := hmin i
      omega
  rw [bidiagonalPencil_kernel_coordinates (e i) _ hk k, hz₀, mul_zero]
  rfl

theorem rectangular_scalar_low_degree_zero_reindex {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a]
    (e : ι → ℕ) (er : a ≃ (Σ i, Fin (e i))) (ec : b ≃ (Σ i, Fin (e i + 1)))
    (d : ℕ) (hmin : ∀ i, d < e i) (hlong : ∃ i, d + 1 < e i)
    (U : Matrix a b K[X]) (c : K[X])
    (hU : U * ((rectangularBlockPencil e).submatrix er ec).transpose =
      c • (1 : Matrix a a K[X])) (hdeg : DegreeBound U d) : U = 0 ∧ c = 0 := by
  let V : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i + 1)) K[X] :=
    U.submatrix er.symm ec.symm
  have hV : V * (rectangularBlockPencil e).transpose =
      c • (1 : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i)) K[X]) := by
    have hh := Matrix.submatrix_mul_equiv U
      ((rectangularBlockPencil e).submatrix er ec).transpose er.symm ec.symm er.symm
    have he : (((rectangularBlockPencil e).submatrix er ec).transpose).submatrix
        ec.symm er.symm = (rectangularBlockPencil (K := K) e).transpose := by
      ext i j
      simp
    rw [he, hU] at hh
    simpa only [V, Matrix.submatrix_smul, Pi.smul_apply, Matrix.submatrix_one_equiv] using hh
  obtain ⟨hzero, hc⟩ := rectangular_scalar_low_degree_zero e d hmin hlong V c hV
    (fun i j => hdeg (er.symm i) (ec.symm j))
  refine ⟨?_, hc⟩
  funext i j
  have hh := congrArg (fun A : Matrix (Σ i, Fin (e i)) (Σ i, Fin (e i + 1)) K[X] =>
    A (er i) (ec j)) hzero
  simpa [V] using hh

end FD56
