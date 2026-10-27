/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SeparableSpecialization
import FD56.Hilbert.GenericKernelExtension
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Stabilizer.ScalarObservabilityDegree

/-! Full-degree separable observability determinants transfer from affine field witnesses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L n m : Type*} [Field K] [Field L]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [Fintype m] [DecidableEq m] in
theorem generic_selected_observability_separable_of_witness
    (σ : K →+* L) (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (level : n → ℕ) (row : n → m)
    (hd : (observabilitySelectedMatrix M P level row).det.natDegree =
      ∑ i, (level i + 1))
    (hs : (observabilitySelectedMatrix M P level row).det.Separable) :
    let A := observabilitySelectedMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) level row
    A.det.natDegree = (∑ i, (level i + 1)) ∧ A.det.Separable := by
  dsimp only
  let R := MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K
  let F := AffineCoefficientField K (MatrixParameters n m)
  let φ := affinePairFieldSpecialization σ M P
  let ψ : R →+* F := algebraMap R F
  let A := observabilitySelectedMatrix (universalAffineSquare K n m)
    (universalAffineRows K n m) level row
  have hmapφ : A.det.map φ = (observabilitySelectedMatrix M P level row).det := by
    rw [show A.det.map φ = (Polynomial.mapRingHom φ) A.det from rfl, RingHom.map_det]
    change (A.map (Polynomial.mapRingHom φ)).det = _
    dsimp only [A]
    rw [observabilitySelectedMatrix_map,
      universalAffineSquare_field_specialization σ M P hM,
      universalAffineRows_field_specialization σ M P hP]
  have hmapψ : A.det.map ψ = (observabilitySelectedMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) level row).det := by
    rw [show A.det.map ψ = (Polynomial.mapRingHom ψ) A.det from rfl, RingHom.map_det]
    change (A.map (Polynomial.mapRingHom ψ)).det = _
    dsimp only [A]
    rw [observabilitySelectedMatrix_map,
      universalAffineSquare_generic, universalAffineRows_generic]
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  have hbound : A.det.natDegree ≤ ∑ i, (level i + 1) := by
    rw [← Polynomial.natDegree_map_eq_of_injective hψ, hmapψ]
    apply polynomial_det_natDegree_le_row_sum
    intro i j
    have hp : DegreeBound ((genericAffineSquare K n m) ^ level i) (level i) := by
      simpa using degreeBound_pow _ 1 (genericAffineSquare_degree K n m) (level i)
    exact (degreeBound_mul (genericAffineRows_degree K n m) hp (row i) j).trans (by omega)
  have hdegree : A.det.natDegree = ∑ i, (level i + 1) := by
    apply Nat.le_antisymm hbound
    rw [← hd, ← hmapφ]
    exact Polynomial.natDegree_map_le
  constructor
  · rw [← hmapψ, Polynomial.natDegree_map_eq_of_injective hψ, hdegree]
  · rw [← hmapψ]
    apply separable_of_degree_preserving_specialization A.det φ ψ hψ
    · rw [hmapφ, hd, hdegree]
    · rwa [hmapφ]

theorem generic_scalar_observability_separable (K : Type*) [Field K] (N : ℕ) :
    let A := observabilitySelectedMatrix (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1)) Fin.val (fun _ => 0)
    A.det.natDegree = (∑ i : Fin N, (i.val + 1)) ∧ A.det.Separable := by
  let L := FractionRing (MvPolynomial (Fin N) K)
  let ι : MvPolynomial (Fin N) K →+* L := algebraMap _ _
  let a : Fin N → L := fun i => ι (MvPolynomial.X i)
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have ha : Function.Injective a := hι.comp MvPolynomial.X_injective
  apply generic_selected_observability_separable_of_witness
    (ι.comp MvPolynomial.C) (scalarDiagonalState a) (scalarDiagonalOutput a)
    (scalarDiagonalState_degree a) (scalarDiagonalOutput_degree a) Fin.val (fun _ => 0)
  · rw [← scalarDiagonalObservability_eq_selected]
    exact scalarDiagonalObservability_natDegree a ha
  · rw [← scalarDiagonalObservability_eq_selected]
    exact scalarDiagonalObservability_separable N ι hι

end FD56
