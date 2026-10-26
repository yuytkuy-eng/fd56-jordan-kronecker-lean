/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.UniformKroneckerBasis
import FD56.LinearAlgebra.MixedKroneckerCongruence

/-! Assemble an actual constant congruence from mixed chain coefficients
and their independent pairing functionals under the exact dimension budget. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] {r : ℕ}

theorem exists_mixed_kronecker_basis (d : Fin r → ℕ) (A B : Matrix n n K)
    (W : Matrix n (Σ j, Fin (d j+1)) K) (L : Matrix (Σ j, Fin (d j)) n K)
    (hcard : Fintype.card n = ∑ j, (2*d j+1))
    (hW : Function.Injective W.mulVec) (hL : Function.Surjective L.mulVec)
    (hLW : L * W = 0)
    (hWA : W.transpose * A = mixedCrossFirst d * L)
    (hWB : W.transpose * B = mixedCrossSecond d * L)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ G : Matrix n ((Σ j, Fin (d j+1)) ⊕ (Σ j, Fin (d j))) K,
    ∃ J : Matrix ((Σ j, Fin (d j+1)) ⊕ (Σ j, Fin (d j))) n K,
      G * J = 1 ∧ J * G = 1 ∧
      G.transpose * A * G =
        Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0 ∧
      G.transpose * B * G =
        Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0 := by
  have hcard' : Fintype.card n = Fintype.card (Σ j, Fin (d j+1)) +
      Fintype.card (Σ j, Fin (d j)) := by
    rw [hcard]
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    omega
  obtain ⟨Q, J, hHJ, hJH, hLQ⟩ := exists_dual_complement_of_cardEq W L hcard' hLW hW hL
  let H := Matrix.fromCols W Q
  let S := Q.transpose * A * Q
  let T := Q.transpose * B * Q
  have hHA : H.transpose * A * H =
      Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) S :=
    dual_complement_congruence A W L Q (mixedCrossFirst d) hA hLW hLQ hWA
  have hHB : H.transpose * B * H =
      Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) T :=
    dual_complement_congruence B W L Q (mixedCrossSecond d) hB hLW hLQ hWB
  obtain ⟨hS, hSd⟩ := complement_restriction_alternating A Q hA hAltA
  obtain ⟨hT, hTd⟩ := complement_restriction_alternating B Q hB hAltB
  obtain ⟨hXY, hYX, hAS, hBT⟩ := mixed_kronecker_block_congruence d S T hS hSd hT hTd
  let X := complementShift (mixedFiniteCorrection d S T)
  let Y := complementShift (-mixedFiniteCorrection d S T)
  refine ⟨H * X, Y * J, ?_, ?_, ?_, ?_⟩
  · calc
      H * X * (Y * J) = H * (X * Y) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hXY, Matrix.mul_one]; exact hHJ
  · calc
      Y * J * (H * X) = Y * (J * H) * X := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJH, Matrix.mul_one]; exact hYX
  · calc
      (H * X).transpose * A * (H * X) = X.transpose * (H.transpose * A * H) * X := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hHA]; exact hAS
  · calc
      (H * X).transpose * B * (H * X) = X.transpose * (H.transpose * B * H) * X := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hHB]; exact hBT

end FD56
