/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformKroneckerIdentification
import FD56.Hilbert.UniformKroneckerClassification

/-! Uniform minimal degrees with a full dimension budget give actual Kronecker blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] {e r : ℕ}

theorem uniform_kronecker_congruence_to_blocks (A B : Matrix n n K)
    (G : Matrix n ((Fin (e + 1) × Fin r) ⊕ (Fin e × Fin r)) K)
    (J : Matrix ((Fin (e + 1) × Fin r) ⊕ (Fin e × Fin r)) n K)
    (hGJ : G * J = 1) (hJG : J * G = 1)
    (hGA : G.transpose * A * G =
      Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) 0)
    (hGB : G.transpose * B * G =
      Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) 0) :
    ∃ T : Matrix n ((Fin e ⊕ Fin (e + 1)) × Fin r) K,
    ∃ S : Matrix ((Fin e ⊕ Fin (e + 1)) × Fin r) n K,
      T * S = 1 ∧ S * T = 1 ∧
      (T.map C).transpose * affineMatrixPencil A B * T.map C =
        Matrix.blockDiagonal (fun _ : Fin r => kroneckerBlockPencil (K := K) e) := by
  let o := uniformKroneckerOrder e r
  let D := uniformKroneckerSigns (K := K) e r
  let H := G.submatrix id o
  let I := J.submatrix o id
  have hDD : D * D = 1 := uniformKroneckerSigns_inverse e r
  have hHI : H * I = 1 := by
    dsimp only [H, I]
    rw [Matrix.submatrix_mul_equiv, hGJ, Matrix.submatrix_id_id]
  have hIH : I * H = 1 := by
    change J.submatrix o (Equiv.refl n) * G.submatrix (Equiv.refl n) o = 1
    rw [Matrix.submatrix_mul_equiv, hJG]
    exact Matrix.submatrix_one_equiv o
  have hreindex (F : Matrix n n K) :
      H.transpose * F * H = (G.transpose * F * G).submatrix o o := by
    change G.transpose.submatrix o (Equiv.refl n) *
      F.submatrix (Equiv.refl n) (Equiv.refl n) * G.submatrix (Equiv.refl n) o = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have hHA : H.transpose * A * H =
      (Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) 0).submatrix o o := by
    rw [hreindex, hGA]
  have hHB : H.transpose * B * H =
      (Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) 0).submatrix o o := by
    rw [hreindex, hGB]
  have hH : (H.map C).transpose * affineMatrixPencil A B * H.map C =
      (uniformCorrectedPencil (K := K) e r).submatrix o o := by
    rw [affineMatrixPencil_constant_congruence, hHA, hHB]
    rfl
  refine ⟨H * D, D * I, ?_, ?_, ?_⟩
  · calc
      H * D * (D * I) = H * (D * D) * I := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hHI]
  · calc
      D * I * (H * D) = D * (I * H) * D := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hIH, Matrix.mul_one, hDD]
  · have hDt : D.transpose = D := by simp [D, uniformKroneckerSigns]
    have hDCt : (D.map C).transpose = D.map C := by rw [← Matrix.transpose_map, hDt]
    calc
      ((H * D).map C).transpose * affineMatrixPencil A B * (H * D).map C =
          D.map C * ((H.map C).transpose * affineMatrixPencil A B * H.map C) * D.map C := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, hDCt,
          Matrix.mul_assoc]
      _ = _ := by
        rw [hH]
        exact uniform_corrected_pencil_is_kronecker_blocks e r

theorem exists_uniform_kronecker_canonical (A B : Matrix n n K)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) (List.replicate r e))
    (hcard : Fintype.card n = r * (2 * e + 1))
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ T : Matrix n ((Fin e ⊕ Fin (e + 1)) × Fin r) K,
    ∃ S : Matrix ((Fin e ⊕ Fin (e + 1)) × Fin r) n K,
      T * S = 1 ∧ S * T = 1 ∧
      (T.map C).transpose * affineMatrixPencil A B * T.map C =
        Matrix.blockDiagonal (fun _ : Fin r => kroneckerBlockPencil (K := K) e) := by
  obtain ⟨G, J, hGJ, hJG, hGA, hGB⟩ :=
    uniform_minimal_degrees_constant_congruence A B hmin hcard hA hB hAltA hAltB
  exact uniform_kronecker_congruence_to_blocks A B G J hGJ hJG hGA hGB

end FD56
