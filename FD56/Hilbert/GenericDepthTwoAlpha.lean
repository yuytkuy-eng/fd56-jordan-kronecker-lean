/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericPrescribedMatrix
import FD56.Hilbert.GenericKernelExtension
import FD56.Hilbert.MinimalProfile
import FD56.Hilbert.BalancedDegrees
import FD56.Stabilizer.ObservabilityRealization
import FD56.Stabilizer.StructuredLeading

/-! Balanced alpha kernels at observability depth two, obtained by an actual
affine realization of an independent linear and quadratic matrix stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L n m : Type*} [Field K] [Field L]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_observability_kernel_le_field_witness (σ : K →+* L)
    (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (q d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q) d) ≤
      Module.finrank L (polynomialKernelAtDegree (observabilityMatrix M P q) d) := by
  let ψ := affinePairFieldSpecialization σ M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let A := observabilityMatrix (universalAffineSquare K n m) (universalAffineRows K n m) q
  let C := weightedCoefficientMatrix A (fun _ => d) (fun ij => d + (ij.1.val + 1))
  have he : C.map ψ = weightedCoefficientMatrix (observabilityMatrix M P q)
      (fun _ => d) (fun ij => d + (ij.1.val + 1)) := by
    dsimp only [C, A, ψ]
    rw [← weightedCoefficientMatrix_map, observabilityMatrix_map,
      universalAffineSquare_field_specialization σ M P hM,
      universalAffineRows_field_specialization σ M P hP]
  have hg : C.map φ = weightedCoefficientMatrix (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q)
      (fun _ => d) (fun ij => d + (ij.1.val + 1)) := by
    dsimp only [C, A, φ]
    rw [← weightedCoefficientMatrix_map, observabilityMatrix_map,
      universalAffineSquare_generic, universalAffineRows_generic]
  have hs := matrix_kernel_finrank_le_of_field_specialization ψ φ
    (IsFractionRing.injective _ _) C
  rw [he, hg, weighted_coefficient_kernel_finrank _ _ _ (by
    intro i j
    have := (observability_polynomial_degree_top _ _ q
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1
    omega), weighted_coefficient_kernel_finrank _ _ _ (by
      intro i j
      have := (observability_polynomial_degree_top M P q hM hP i j).1
      omega)] at hs
  exact hs

abbrev DepthTwoWitnessField (K n m : Type*) [Field K] :=
  PrescribedMatrixField K n (fun ij : Fin 2 × m => ij.1.val + 1)

theorem exists_depth_two_alpha_witness
    (hmn : 2 * Fintype.card m < Fintype.card n) :
    ∃ (M : Matrix n n (DepthTwoWitnessField K n m)[X])
      (P : Matrix m n (DepthTwoWitnessField K n m)[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧
      ∀ d, Module.finrank (DepthTwoWitnessField K n m)
        (polynomialKernelAtDegree (observabilityMatrix M P 2) d) =
        (Fintype.card n - 2 * Fintype.card m) * (d + 1) - 3 * Fintype.card m := by
  let e : Fin 2 × m → ℕ := fun ij => ij.1.val + 1
  let G := genericPrescribedMatrix K n e
  let R : Fin 2 → Matrix m n (DepthTwoWitnessField K n m)[X] := fun i x j => G (i,x) j
  let u : m ↪ Fin 2 × m := ⟨fun x => (0,x), fun _ _ h => congrArg Prod.snd h⟩
  have hR : ∀ i x j, (R i x j).natDegree ≤ i.val + 1 :=
    fun i x j => genericPrescribedMatrix_degree e (i,x) j
  have hP : DegreeBound (R 0) 1 := fun x j => hR 0 x j
  have hH : Module.finrank (DepthTwoWitnessField K n m)
      (polynomialKernelAtDegree (R 0) 1) =
      (Fintype.card n - Fintype.card m) * 2 - Fintype.card m := by
    have hh := generic_prescribed_submatrix_kernel_hilbert (K := K) (n := n) e u (by omega) 1
    change Module.finrank (DepthTwoWitnessField K n m)
      (polynomialKernelAtDegree (R 0) 1) =
      (Fintype.card n - Fintype.card m) * 2 - ∑ _ : m, 1 at hh
    simpa using hh
  have hs : Function.Surjective (weightedCoefficientMatrix (R 0)
      (fun _ => 1) (fun _ => 2)).mulVec := by
    apply column_coefficient_surjective_of_kernel_hilbert (R 0).transpose (fun _ => 1) 1
      (fun j i => hP i j) (by omega)
    · simp
      omega
    · simpa using hH
  obtain ⟨M, hM, hstep, _⟩ := affine_observability_realization_of_preimages (q := 1) R hR (by
    intro w hw
    obtain ⟨v, hv, he⟩ := weighted_coefficient_surjective_lift (R 0)
      (fun _ => 1) (fun _ => 2) (fun i j => by
        change (R 0 i j).natDegree + 1 ≤ 2
        have := hP i j
        omega) hs
      (w 0) (hw 0)
    refine ⟨v, hv, ?_⟩
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact he)
  have hO : observabilityMatrix M (R 0) 2 = G :=
    observabilityMatrix_eq_of_matrix_family_recurrence R M hstep
  refine ⟨M, R 0, hM, hP, ?_⟩
  intro d
  rw [hO]
  have hh := generic_prescribed_kernel_hilbert (K := K) e
    (by simpa only [Fintype.card_prod, Fintype.card_fin] using hmn) d
  have hsum : ∑ ij : Fin 2 × m, e ij = 3 * Fintype.card m := by
    simp [e, Fintype.sum_prod_type, Fin.sum_univ_two]
    omega
  simpa only [Fintype.card_prod, Fintype.card_fin, hsum] using hh

theorem generic_depth_two_alpha_hilbert
    (hmn : 2 * Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 2) d) =
      (Fintype.card n - 2 * Fintype.card m) * (d + 1) - 3 * Fintype.card m := by
  apply le_antisymm
  · obtain ⟨M, P, hM, hP, hH⟩ := exists_depth_two_alpha_witness (K := K) hmn
    let σ : K →+* DepthTwoWitnessField K n m :=
      (algebraMap (MvPolynomial (PrescribedMatrixParameters n
        (fun ij : Fin 2 × m => ij.1.val + 1)) K) _).comp MvPolynomial.C
    exact (generic_observability_kernel_le_field_witness σ M P hM hP 2 d).trans_eq (hH d)
  · have hh := prescribed_matrix_kernel_lower
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 2)
      (fun ij => ij.1.val + 1)
      (fun i j => (observability_polynomial_degree_top _ _ 2
        (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i j).1)
      (by simpa only [Fintype.card_prod, Fintype.card_fin] using hmn.le) d
    have hsum : ∑ ij : Fin 2 × m, (ij.1.val + 1) = 3 * Fintype.card m := by
      simp [Fintype.sum_prod_type, Fin.sum_univ_two]
      omega
    simpa only [Fintype.card_prod, Fintype.card_fin, hsum] using hh

theorem generic_depth_two_alpha_minimal_degrees
    (hmn : 2 * Fintype.card m < Fintype.card n) :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) 2)
      (balancedDegreeList (3 * Fintype.card m)
        (Fintype.card n - 2 * Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_two_alpha_hilbert hmn d,
    balancedDegreeList_hilbert _ _ d (by omega)]

end FD56
