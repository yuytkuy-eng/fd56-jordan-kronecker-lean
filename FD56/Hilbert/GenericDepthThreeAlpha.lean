/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericDepthTwoAlpha

/-! Depth-three alpha kernels when the independent linear/quadratic prefix
has enough affine input coefficients for simultaneous realization. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

abbrev DepthThreeWitnessField (K n m : Type*) [Field K] :=
  PrescribedMatrixField K n (fun ij : Fin 3 × m => ij.1.val + 1)

theorem exists_depth_three_alpha_witness
    (hmn : 3 * Fintype.card m < Fintype.card n)
    (hcapacity : 7 * Fintype.card m ≤ 2 * Fintype.card n) :
    ∃ (M : Matrix n n (DepthThreeWitnessField K n m)[X])
      (P : Matrix m n (DepthThreeWitnessField K n m)[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧
      ∀ d, Module.finrank (DepthThreeWitnessField K n m)
        (polynomialKernelAtDegree (observabilityMatrix M P 3) d) =
        (Fintype.card n - 3 * Fintype.card m) * (d + 1) - 6 * Fintype.card m := by
  let e : Fin 3 × m → ℕ := fun ij => ij.1.val + 1
  let G := genericPrescribedMatrix K n e
  let R : Fin 3 → Matrix m n (DepthThreeWitnessField K n m)[X] := fun i x j => G (i,x) j
  let u : (Fin 2 × m) ↪ Fin 3 × m :=
    ⟨fun x => (x.1.castSucc, x.2), by
      intro i j h
      exact Prod.ext (Fin.castSucc_injective 2 (congrArg Prod.fst h))
        (congrArg (fun x : Fin 3 × m => x.2) h)⟩
  have hR : ∀ i x j, (R i x j).natDegree ≤ i.val + 1 :=
    fun i x j => genericPrescribedMatrix_degree e (i,x) j
  have hP : DegreeBound (R 0) 1 := fun x j => hR 0 x j
  have hpref : observabilityRealizationPrefix R = G.submatrix u id := rfl
  have hsum₂ : ∑ ij : Fin 2 × m, e (u ij) = 3 * Fintype.card m := by
    change (∑ ij : Fin 2 × m, (ij.1.val + 1)) = _
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
    omega
  have hH : Module.finrank (DepthThreeWitnessField K n m)
      (polynomialKernelAtDegree (observabilityRealizationPrefix R) 1) =
      (Fintype.card n - 2 * Fintype.card m) * 2 - 3 * Fintype.card m := by
    have hh := generic_prescribed_submatrix_kernel_hilbert (K := K) (n := n) e u
      (by simp only [Fintype.card_prod, Fintype.card_fin]; omega) 1
    rw [← hpref] at hh
    simpa only [Fintype.card_prod, Fintype.card_fin, hsum₂] using hh
  have hs : Function.Surjective (observabilityRealizationCoefficientMatrix R).mulVec := by
    apply weighted_coefficient_surjective_of_kernel_finrank
    · intro ij j
      change (R ij.1.castSucc ij.2 j).natDegree + 1 ≤ ij.1.val + 2
      have h := hR ij.1.castSucc ij.2 j
      change (R ij.1.castSucc ij.2 j).natDegree ≤ ij.1.val + 1 at h
      omega
    · rw [weighted_uniform_kernel, hH]
      have hout : (∑ ij : Fin 2 × m, (ij.1.val + 2 + 1)) = 7 * Fintype.card m := by
        simp [Fintype.sum_prod_type, Fin.sum_univ_two]
        omega
      rw [hout]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      omega
  obtain ⟨M, hM, hstep, _⟩ :=
    affine_observability_realization_of_coefficient_surjective (q := 2) R hR hs
  have hO : observabilityMatrix M (R 0) 3 = G :=
    observabilityMatrix_eq_of_matrix_family_recurrence R M hstep
  refine ⟨M, R 0, hM, hP, ?_⟩
  intro d
  rw [hO]
  have hh := generic_prescribed_kernel_hilbert (K := K) e
    (by simpa only [Fintype.card_prod, Fintype.card_fin] using hmn) d
  have hsum : ∑ ij : Fin 3 × m, e ij = 6 * Fintype.card m := by
    simp [e, Fintype.sum_prod_type, Fin.sum_univ_succ]
    omega
  simpa only [Fintype.card_prod, Fintype.card_fin, hsum] using hh

theorem generic_depth_three_alpha_hilbert
    (hmn : 3 * Fintype.card m < Fintype.card n)
    (hcapacity : 7 * Fintype.card m ≤ 2 * Fintype.card n) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3) d) =
      (Fintype.card n - 3 * Fintype.card m) * (d + 1) - 6 * Fintype.card m := by
  apply le_antisymm
  · obtain ⟨M, P, hM, hP, hH⟩ := exists_depth_three_alpha_witness (K := K) hmn hcapacity
    let σ : K →+* DepthThreeWitnessField K n m :=
      (algebraMap (MvPolynomial (PrescribedMatrixParameters n
        (fun ij : Fin 3 × m => ij.1.val + 1)) K) _).comp MvPolynomial.C
    exact (generic_observability_kernel_le_field_witness σ M P hM hP 3 d).trans_eq (hH d)
  · have hh := prescribed_matrix_kernel_lower
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 3)
      (fun ij => ij.1.val + 1)
      (fun i j => (observability_polynomial_degree_top _ _ 3
        (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1)
      (by simpa only [Fintype.card_prod, Fintype.card_fin] using hmn.le) d
    have hsum : ∑ ij : Fin 3 × m, (ij.1.val + 1) = 6 * Fintype.card m := by
      simp [Fintype.sum_prod_type, Fin.sum_univ_succ]
      omega
    simpa only [Fintype.card_prod, Fintype.card_fin, hsum] using hh

theorem generic_depth_three_alpha_minimal_degrees
    (hmn : 3 * Fintype.card m < Fintype.card n)
    (hcapacity : 7 * Fintype.card m ≤ 2 * Fintype.card n) :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) 3)
      (balancedDegreeList (6 * Fintype.card m)
        (Fintype.card n - 3 * Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_alpha_hilbert hmn hcapacity d,
    balancedDegreeList_hilbert _ _ d (by omega)]

end FD56
