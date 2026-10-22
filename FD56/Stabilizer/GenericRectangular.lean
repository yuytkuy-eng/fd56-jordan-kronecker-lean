/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericRows
import FD56.Hilbert.Coefficients
import FD56.Hilbert.BalancedRectangular

/-! Specializing the transpose of a generic affine rectangular pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem universal_transpose_affine_specialization (Q : Matrix n m K[X])
    (hQ : DegreeBound Q 1) :
    (universalAffineRows K n m).transpose.map
      (Polynomial.mapRingHom (affineRowsSpecialization
        (fun i j => (Q j i).coeff 0) (fun i j => (Q j i).coeff 1))) = Q := by
  rw [Matrix.transpose_map, universalAffineRows_specialization]
  have he := congrArg Matrix.transpose
    (affineMatrixPencil_coefficients Q.transpose (fun i j => hQ j i))
  simpa only [Matrix.transpose_apply, Matrix.transpose_transpose] using he

theorem generic_transpose_coefficient_injective_of_witness
    (Q : Matrix n m K[X]) (d : ℕ) (hQ : DegreeBound Q 1)
    (hi : Function.Injective (polynomialCoefficientMatrix Q d).mulVec) :
    Function.Injective (polynomialCoefficientMatrix
      (genericAffineRows K n m).transpose d).mulVec := by
  let ψ := affineRowsSpecialization (fun i j => (Q j i).coeff 0)
    (fun i j => (Q j i).coeff 1)
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  have hg : (universalAffineRows K n m).transpose.map (Polynomial.mapRingHom φ) =
      (genericAffineRows K n m).transpose := by
    rw [Matrix.transpose_map, universalAffineRows_generic]
  rw [← hg, polynomialCoefficientMatrix_map]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ (IsFractionRing.injective _ _)
  rw [← polynomialCoefficientMatrix_map, universal_transpose_affine_specialization Q hQ]
  exact hi

theorem generic_transpose_coefficient_surjective_of_witness
    (Q : Matrix n m K[X]) (d : ℕ) (hQ : DegreeBound Q 1)
    (hs : Function.Surjective (polynomialCoefficientMatrix Q d).mulVec) :
    Function.Surjective (polynomialCoefficientMatrix
      (genericAffineRows K n m).transpose d).mulVec := by
  let ψ := affineRowsSpecialization (fun i j => (Q j i).coeff 0)
    (fun i j => (Q j i).coeff 1)
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  have hg : (universalAffineRows K n m).transpose.map (Polynomial.mapRingHom φ) =
      (genericAffineRows K n m).transpose := by
    rw [Matrix.transpose_map, universalAffineRows_generic]
  rw [← hg, polynomialCoefficientMatrix_map]
  apply matrix_surjective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ (IsFractionRing.injective _ _)
  rw [← polynomialCoefficientMatrix_map, universal_transpose_affine_specialization Q hQ]
  exact hs

theorem generic_transpose_coefficient_injective
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ)
    (hd : (Fintype.card m - Fintype.card n) * (d + 1) ≤ Fintype.card n) :
    Function.Injective (polynomialCoefficientMatrix
      (genericAffineRows K n m).transpose d).mulVec :=
  generic_transpose_coefficient_injective_of_witness (balancedRectangularWitness hnm) d
    (balancedRectangularWitness_degree hnm)
    (balancedRectangularWitness_coefficient_injective hnm d hd)

theorem generic_transpose_coefficient_surjective
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ)
    (hd : Fintype.card n ≤ (Fintype.card m - Fintype.card n) * (d + 1)) :
    Function.Surjective (polynomialCoefficientMatrix
      (genericAffineRows K n m).transpose d).mulVec :=
  generic_transpose_coefficient_surjective_of_witness (balancedRectangularWitness hnm) d
    (balancedRectangularWitness_degree hnm)
    (balancedRectangularWitness_coefficient_surjective hnm d hd)

theorem generic_transpose_kernel_hilbert
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (genericAffineRows K n m).transpose d) =
        (Fintype.card m - Fintype.card n) * (d + 1) - Fintype.card n := by
  by_cases hd : Fintype.card n ≤ (Fintype.card m - Fintype.card n) * (d + 1)
  · rw [polynomial_kernel_hilbert_of_coefficient_surjective (genericAffineRows K n m).transpose d
      (fun i j => genericAffineRows_degree K n m j i)
      (generic_transpose_coefficient_surjective hnm d hd)]
    have hm : Fintype.card m = Fintype.card n + (Fintype.card m - Fintype.card n) := by omega
    rw [hm]
    simp only [Nat.add_sub_cancel_left]
    exact rectangular_coefficient_difference _ _ d
  · rw [polynomial_kernel_hilbert_of_coefficient_injective (genericAffineRows K n m).transpose d
      (generic_transpose_coefficient_injective hnm d (by omega))]
    exact (Nat.sub_eq_zero_of_le (by omega)).symm

theorem generic_rows_coefficient_injective_of_witness
    (P : Matrix m n K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hi : Function.Injective (polynomialCoefficientMatrix P d).mulVec) :
    Function.Injective (polynomialCoefficientMatrix (genericAffineRows K n m) d).mulVec := by
  let ψ := affineRowsSpecialization (fun i j => (P i j).coeff 0)
    (fun i j => (P i j).coeff 1)
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  have he : (universalAffineRows K n m).map (Polynomial.mapRingHom ψ) = P := by
    rw [universalAffineRows_specialization]
    exact affineMatrixPencil_coefficients P hP
  rw [← universalAffineRows_generic, polynomialCoefficientMatrix_map]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ (IsFractionRing.injective _ _)
  rw [← polynomialCoefficientMatrix_map, he]
  exact hi

theorem generic_rows_coefficient_injective
    (hmn : Fintype.card m < Fintype.card n) (d : ℕ)
    (hd : (Fintype.card n - Fintype.card m) * (d + 1) ≤ Fintype.card m) :
    Function.Injective (polynomialCoefficientMatrix (genericAffineRows K n m) d).mulVec :=
  generic_rows_coefficient_injective_of_witness (balancedRectangularWitness hmn) d
    (balancedRectangularWitness_degree hmn)
    (balancedRectangularWitness_coefficient_injective hmn d hd)

theorem generic_rows_coefficient_surjective
    (hmn : Fintype.card m < Fintype.card n) (d : ℕ)
    (hd : Fintype.card m ≤ (Fintype.card n - Fintype.card m) * (d + 1)) :
    Function.Surjective (polynomialCoefficientMatrix (genericAffineRows K n m) d).mulVec := by
  rw [← universalAffineRows_generic]
  apply universal_affine_rows_coefficient_of_witness (balancedRectangularWitness hmn) d
    (balancedRectangularWitness_degree hmn)
    (balancedRectangularWitness_coefficient_surjective hmn d hd)
    (algebraMap _ _) (IsFractionRing.injective _ _)

theorem generic_rows_kernel_hilbert
    (hmn : Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (genericAffineRows K n m) d) =
        (Fintype.card n - Fintype.card m) * (d + 1) - Fintype.card m := by
  by_cases hd : Fintype.card m ≤ (Fintype.card n - Fintype.card m) * (d + 1)
  · rw [polynomial_kernel_hilbert_of_coefficient_surjective (genericAffineRows K n m) d
      (genericAffineRows_degree K n m) (generic_rows_coefficient_surjective hmn d hd)]
    have hn : Fintype.card n = Fintype.card m + (Fintype.card n - Fintype.card m) := by omega
    rw [hn]
    simp only [Nat.add_sub_cancel_left]
    exact rectangular_coefficient_difference _ _ d
  · rw [polynomial_kernel_hilbert_of_coefficient_injective (genericAffineRows K n m) d
      (generic_rows_coefficient_injective hmn d (by omega))]
    exact (Nat.sub_eq_zero_of_le (by omega)).symm

end FD56
