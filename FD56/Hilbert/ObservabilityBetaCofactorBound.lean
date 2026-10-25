/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaKernel

/-! A large final coordinate of a left-relation generator excludes bounded beta relations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n]

/-- Combine the previous-block coefficients and the terminal coefficients into one relation. -/
def observabilityBetaRelationVector (q : ℕ) (E : m → K[X]) (F : Fin q × m → K[X]) :
    Fin (q + 1) × m → K[X] :=
  fun ij => Fin.lastCases (E ij.2) (fun k => -F (k, ij.2)) ij.1

theorem observabilityBetaRelationVector_identity (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (E : m → K[X]) (F : Fin q × m → K[X]) :
    (observabilityMatrix M P (q + 1)).transpose *ᵥ observabilityBetaRelationVector q E F =
      (P * M ^ q).transpose *ᵥ E - (observabilityMatrix M P q).transpose *ᵥ F := by
  funext j
  simp [observabilityBetaRelationVector, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    observabilityMatrix, Fintype.sum_prod_type, Fin.sum_univ_castSucc, sub_eq_add_neg, add_comm]
  simp only [← Matrix.transpose_pow, ← Matrix.transpose_mul, Matrix.transpose_apply]

/-- A generator whose final block exceeds the bound forces the entire beta kernel to vanish. -/
theorem boundedObservabilityBetaKernel_eq_bot_of_relation_generator
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ)
    (c : Fin (q + 1) × m → K[X])
    (hgen : ∀ y : Fin (q + 1) × m → K[X],
      (observabilityMatrix M P (q + 1)).transpose *ᵥ y = 0 →
        ∃ h : K[X], y = h • c)
    (j : m) (hc : c (Fin.last q, j) ≠ 0) (hdeg : d < (c (Fin.last q, j)).natDegree) :
    boundedObservabilityBetaKernel q M P d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  let w : boundedObservabilityBetaKernel q M P d := ⟨z, hz⟩
  let y := observabilityBetaRelationVector q (fun i => (z.1 i).val) (fun i => (z.2 i).val)
  have hyker : (observabilityMatrix M P (q + 1)).transpose *ᵥ y = 0 := by
    rw [observabilityBetaRelationVector_identity,
      boundedObservabilityBetaKernel_relation q M P d w, sub_self]
  obtain ⟨h, hh⟩ := hgen y hyker
  have he : (z.1 j).val = h * c (Fin.last q, j) := by
    simpa [y, observabilityBetaRelationVector] using congrFun hh (Fin.last q, j)
  have hzero : h = 0 := by
    by_contra hn
    have hb := boundedPoly_degree d (z.1 j)
    rw [he, Polynomial.natDegree_mul hn hc] at hb
    omega
  have hy : y = 0 := by rw [hh, hzero, zero_smul]
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa [y, observabilityBetaRelationVector] using congrFun hy (Fin.last q, i)
  · funext i
    apply Subtype.ext
    simpa [y, observabilityBetaRelationVector] using congrFun hy (i.1.castSucc, i.2)

theorem boundedObservabilityBetaKernel_finrank_zero_of_relation_generator
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ)
    (c : Fin (q + 1) × m → K[X])
    (hgen : ∀ y : Fin (q + 1) × m → K[X],
      (observabilityMatrix M P (q + 1)).transpose *ᵥ y = 0 →
        ∃ h : K[X], y = h • c)
    (j : m) (hc : c (Fin.last q, j) ≠ 0) (hdeg : d < (c (Fin.last q, j)).natDegree) :
    Module.finrank K (boundedObservabilityBetaKernel q M P d) = 0 := by
  rw [boundedObservabilityBetaKernel_eq_bot_of_relation_generator q M P d c hgen j hc hdeg,
    finrank_bot]

end FD56
