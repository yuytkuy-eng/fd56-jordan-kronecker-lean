/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedKroneckerIdentification
import FD56.Hilbert.MixedKroneckerClassification

/-! Actual mixed minimal degrees with a full dimension budget give standard Kronecker blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] {r : ℕ}

theorem mixed_kronecker_congruence_to_blocks (d : Fin r → ℕ) (A B : Matrix n n K)
    (G : Matrix n ((Σ j, Fin (d j + 1)) ⊕ (Σ j, Fin (d j))) K)
    (J : Matrix ((Σ j, Fin (d j + 1)) ⊕ (Σ j, Fin (d j))) n K)
    (hGJ : G * J = 1) (hJG : J * G = 1)
    (hGA : G.transpose * A * G =
      Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0)
    (hGB : G.transpose * B * G =
      Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0) :
    ∃ T : Matrix n (Σ j, Fin (d j) ⊕ Fin (d j + 1)) K,
    ∃ S : Matrix (Σ j, Fin (d j) ⊕ Fin (d j + 1)) n K,
      T * S = 1 ∧ S * T = 1 ∧
      (T.map C).transpose * affineMatrixPencil A B * T.map C =
        Matrix.blockDiagonal' (fun j : Fin r => kroneckerBlockPencil (K := K) (d j)) := by
  let o := mixedKroneckerOrder d
  let D := mixedKroneckerSigns (K := K) d
  let H := G.submatrix id o
  let I := J.submatrix o id
  have hDD : D * D = 1 := mixedKroneckerSigns_inverse d
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
      (Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0).submatrix o o := by
    rw [hreindex, hGA]
  have hHB : H.transpose * B * H =
      (Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0).submatrix o o := by
    rw [hreindex, hGB]
  have hH : (H.map C).transpose * affineMatrixPencil A B * H.map C =
      (mixedCorrectedPencil (K := K) d).submatrix o o := by
    rw [affineMatrixPencil_constant_congruence, hHA, hHB]
    rfl
  refine ⟨H * D, D * I, ?_, ?_, ?_⟩
  · calc
      H * D * (D * I) = H * (D * D) * I := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hHI]
  · calc
      D * I * (H * D) = D * (I * H) * D := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hIH, Matrix.mul_one, hDD]
  · have hDt : D.transpose = D := by simp [D, mixedKroneckerSigns]
    have hDCt : (D.map C).transpose = D.map C := by rw [← Matrix.transpose_map, hDt]
    calc
      ((H * D).map C).transpose * affineMatrixPencil A B * (H * D).map C =
          D.map C * ((H.map C).transpose * affineMatrixPencil A B * H.map C) * D.map C := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, hDCt, Matrix.mul_assoc]
      _ = _ := by
        rw [hH]
        exact mixed_corrected_pencil_is_kronecker_blocks d

theorem exists_mixed_kronecker_canonical (A B : Matrix n n K) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) xs)
    (hcard : Fintype.card n = (xs.map (fun e => 2 * e + 1)).sum)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (List.ofFn d).Perm xs ∧
    ∃ T : Matrix n (Σ j, Fin (d j) ⊕ Fin (d j + 1)) K,
    ∃ S : Matrix (Σ j, Fin (d j) ⊕ Fin (d j + 1)) n K,
      T * S = 1 ∧ S * T = 1 ∧
      (T.map C).transpose * affineMatrixPencil A B * T.map C =
        Matrix.blockDiagonal' (fun j : Fin r => kroneckerBlockPencil (K := K) (d j)) := by
  obtain ⟨s, d, hperm, G, J, hGJ, hJG, hGA, hGB⟩ :=
    mixed_minimal_degrees_constant_congruence A B xs hmin hcard hA hB hAltA hAltB
  refine ⟨s, d, hperm, ?_⟩
  exact mixed_kronecker_congruence_to_blocks d A B G J hGJ hJG hGA hGB

end FD56
