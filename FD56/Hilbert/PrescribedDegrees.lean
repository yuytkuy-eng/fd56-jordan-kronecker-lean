/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DualPrescribed
import FD56.Hilbert.Basis
import FD56.Hilbert.BalancedRectangular

/-! Dual reduced polynomial bases realize arbitrary degree lists of equal sum. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r s : Type*} [Field K] [Fintype r] [Fintype s]
  [DecidableEq r] [DecidableEq s]

theorem exists_polynomial_matrix_with_prescribed_dual_degrees
    (e : r → ℕ) (f : s → ℕ) (hsum : ∑ j, e j = ∑ i, f i) :
    ∃ F : Matrix (r ⊕ s) r K[X],
      (∀ x j, (F x j).natDegree ≤ e j) ∧
      Function.Injective (Matrix.mulVec
        (show Matrix (r ⊕ s) r K from fun x j => (F x j).coeff (e j))) ∧
      (∀ x : K, Function.Injective (F.map (Polynomial.evalRingHom x)).mulVec) ∧
      ∀ d, Module.finrank K (polynomialKernelAtDegree F.transpose d) =
        ∑ i, (d + 1 - f i) := by
  obtain ⟨U, V, hUV, hVU, hU, hV, hLU, hLV⟩ :=
    exists_normalized_dual_pair K e f hsum
  let F := U.submatrix id Sum.inl
  let T := V.submatrix Sum.inr id
  let BF := inversePairKernelBasis U V hUV hVU
  let BT := inversePairDualKernelBasis U V hUV hVU
  have hBF : polynomialKernelBasisMatrix T BF = F :=
    polynomialKernelBasisMatrix_inversePair U V hUV hVU
  have hBT : polynomialKernelBasisMatrix F.transpose BT = T.transpose :=
    polynomialKernelBasisMatrix_inversePairDual U V hUV hVU
  have hFinj : Function.Injective (Matrix.mulVec
      (show Matrix (r ⊕ s) r K from fun x j => (F x j).coeff (e j))) := by
    intro b c hbc
    funext j
    have h := congrFun hbc (Sum.inl j)
    simpa [F, Matrix.submatrix_apply, Matrix.mulVec, dotProduct, hLU] using h
  have hTinj : Function.Injective (Matrix.mulVec
      (show Matrix (r ⊕ s) s K from fun x i => (T i x).coeff (f i))) := by
    intro b c hbc
    funext i
    have h := congrFun hbc (Sum.inr i)
    simpa [T, Matrix.submatrix_apply, Matrix.mulVec, dotProduct, hLV] using h
  refine ⟨F, hU, hFinj, ?_, ?_⟩
  · intro x
    rw [← hBF]
    exact polynomialKernelBasisMatrix_pointwise_injective T BF x
  · intro d
    apply polynomial_kernel_basis_hilbert F.transpose BT f d
    · rw [hBT]
      exact fun x i => hV i x
    · rw [hBT]
      exact hTinj

theorem exists_prescribed_column_matrix_balanced_kernel
    {a : Type*} [Fintype a] [DecidableEq a]
    (e : r → ℕ) (hra : Fintype.card r < Fintype.card a) :
    ∃ F : Matrix a r K[X],
      (∀ x j, (F x j).natDegree ≤ e j) ∧
      ∀ d, Module.finrank K (polynomialKernelAtDegree F.transpose d) =
        (Fintype.card a - Fintype.card r) * (d + 1) - ∑ j, e j := by
  classical
  let D := ∑ j, e j
  let S := Fintype.card a - Fintype.card r
  have hS : 0 < S := by dsimp [S]; omega
  let b := Fin (D % S) ⊕ Fin (S - D % S)
  let f : b → ℕ := rectangularBlockLengths D S
  have hf : ∑ i, f i = D := by
    simpa [f, b, rectangularBlockLengths, Fintype.sum_sum_type] using
      (rectangular_balanced_rows D S hS).symm
  have hb : Fintype.card b = S := by
    simp only [b, Fintype.card_sum, Fintype.card_fin]
    have hmod := Nat.mod_lt D hS
    omega
  let er : a ≃ r ⊕ b := Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, hb]
    dsimp [S]
    omega)
  obtain ⟨F, hF, _, _, hH⟩ := exists_polynomial_matrix_with_prescribed_dual_degrees
    (K := K) e f (by exact hf.symm)
  refine ⟨F.submatrix er id, fun x j => hF (er x) j, ?_⟩
  intro d
  change Module.finrank K (polynomialKernelAtDegree
    (F.transpose.submatrix (Equiv.refl r) er) d) = _
  rw [reindex_kernel_hilbert, hH]
  simpa [f, b, rectangularBlockLengths, Fintype.sum_sum_type, S, D] using
    rectangular_balanced_hilbert_sizes D S d hS

end FD56
