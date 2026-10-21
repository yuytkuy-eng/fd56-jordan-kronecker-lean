/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Tall
import FD56.Hilbert.EquationDegree
import FD56.Stabilizer.BidiagonalSL
import FD56.Stabilizer.GenericRows

/-! Low-degree vanishing for the actual generic SL radical when m = n + 1. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_one_extra_transpose_coefficient_injective (n d : ℕ) (hd : d < n) :
    Function.Injective (polynomialCoefficientMatrix
      (genericAffineRows K (Fin n) (Fin (n + 1))).transpose d).mulVec := by
  classical
  let P := (bidiagonalPencil (K := K) n).transpose
  let A : Matrix (Fin (n + 1)) (Fin n) K := fun i j => (P i j).coeff 0
  let B : Matrix (Fin (n + 1)) (Fin n) K := fun i j => (P i j).coeff 1
  let ψ := affineRowsSpecialization A B
  let φ := algebraMap (MvPolynomial (MatrixParameters (Fin n) (Fin (n + 1)) ⊕
    MatrixParameters (Fin n) (Fin (n + 1))) K)
      (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
  have hP : DegreeBound P 1 := fun i j => bidiagonalPencil_degree n j i
  have he : (universalAffineRows K (Fin n) (Fin (n + 1))).transpose.map
      (Polynomial.mapRingHom ψ) = bidiagonalPencil n := by
    rw [Matrix.transpose_map, universalAffineRows_specialization,
      affineMatrixPencil_coefficients P hP, Matrix.transpose_transpose]
  have hg : (universalAffineRows K (Fin n) (Fin (n + 1))).transpose.map
      (Polynomial.mapRingHom φ) = (genericAffineRows K (Fin n) (Fin (n + 1))).transpose := by
    dsimp only [φ]
    rw [Matrix.transpose_map, universalAffineRows_generic]
  rw [← hg, polynomialCoefficientMatrix_map]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ (IsFractionRing.injective _ _)
  rw [← polynomialCoefficientMatrix_map, he]
  apply coefficient_matrix_injective_of_bounded_kernel_zero _ d (bidiagonalPencil_degree n)
  intro v hv hdeg
  have hz := (bidiagonalPencil_degree_iff n d v hv).mp hdeg
  have hz₀ : v 0 = 0 := by rcases hz with h | h; exact h; omega
  funext j
  rw [bidiagonalPencil_kernel_coordinates n v hv j, hz₀, mul_zero]
  rfl

theorem generic_one_extra_gl_kernel_low (n d : ℕ) (hd : d < n) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K (Fin n) (Fin (n + 1)))
        (genericAffineRows K (Fin n) (Fin (n + 1)))) d) = 0 := by
  let M := genericAffineSquare K (Fin n) (Fin (n + 1))
  let P := genericAffineRows K (Fin n) (Fin (n + 1))
  have hp : Function.Injective P.mulVec := generic_affine_rows_polynomial_injective K _ _ (by simp)
  have hk : polynomialKernelAtDegree (glEquationMatrix M P) d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have he := (gl_kernel_equations_of_injective M P hp _).mp hv
    have hU : (fun i j => (v (.inr (i, j))).val) = (0 : Matrix (Fin n) (Fin (n + 1)) _) := by
      funext i j
      have hker : P.transpose *ᵥ (fun j => (v (.inr (i, j))).val) = 0 := by
        funext k
        have hh := congrArg (fun U : Matrix (Fin n) (Fin n) _ => U i k) he.2
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using hh
      have hz := bounded_kernel_zero_of_coefficient_matrix_injective P.transpose d
        (generic_one_extra_transpose_coefficient_injective (K := K) n d hd)
        _ hker (fun j => boundedPoly_degree d (v (.inr (i, j))))
      exact congrFun hz j
    funext j
    apply Subtype.ext
    rcases j with ij | ij
    · exact congrArg (fun U : Matrix (Fin n) (Fin n) _ => U ij.1 ij.2) he.1
    · exact congrArg (fun U : Matrix (Fin n) (Fin (n + 1)) _ => U ij.1 ij.2) hU
  change Module.finrank _ (polynomialKernelAtDegree (glEquationMatrix M P) d) = 0
  rw [hk, finrank_bot]

theorem bidiagonal_sl_bounded_kernel_zero (n d : ℕ) (hn : 0 < n) (hd : d + 1 < n)
    (v : SLInput (Fin n) (Fin (n + 1)) → K[X])
    (hv : slEquationMatrix 0 (bidiagonalPencil n).transpose ⟨0, hn⟩ *ᵥ v = 0)
    (hdeg : ∀ j, (v j).natDegree ≤ d) : v = 0 := by
  obtain ⟨Q, hQ⟩ := bidiagonalPencil_right_inverse (K := K) n
  have hR : (show Matrix (Fin n) (Fin n) K[X] from
      Q.transpose * (bidiagonalPencil (K := K) n).transpose) = 1 := by
    rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  have hs := (slEquationMatrix_kernel_iff 0 (bidiagonalPencil n).transpose ⟨0, hn⟩ v).mp hv
  obtain ⟨hX, c, hc⟩ := (tall_slRadical_iff 0 (bidiagonalPencil n).transpose
    Q.transpose hR ⟨0, hn⟩ _ _).mp hs
  have hz := (bidiagonal_scalar_low_degree_zero n d hd _ c hc
    (fun i j => hdeg (.inr (i, j)))).1
  funext j
  rcases j with ij | ij
  · exact congrArg (fun A : Matrix (Fin n) (Fin n) K[X] => A ij.1 ij.2) hX
  · exact congrArg (fun A : Matrix (Fin n) (Fin (n + 1)) K[X] => A ij.1 ij.2) hz

theorem generic_one_extra_sl_coefficient_injective (n d : ℕ)
    (hn : 0 < n) (hd : d + 1 < n) :
    Function.Injective (polynomialCoefficientMatrix
      (slEquationMatrix (genericAffineSquare K (Fin n) (Fin (n + 1)))
        (genericAffineRows K (Fin n) (Fin (n + 1))) ⟨0, hn⟩) d).mulVec := by
  classical
  let P := (bidiagonalPencil (K := K) n).transpose
  let A : Matrix (Fin (n + 1)) (Fin n) K := fun i j => (P i j).coeff 0
  let B : Matrix (Fin (n + 1)) (Fin n) K := fun i j => (P i j).coeff 1
  let ψ := affineRowsSpecialization A B
  let φ := algebraMap (MvPolynomial (MatrixParameters (Fin n) (Fin (n + 1)) ⊕
    MatrixParameters (Fin n) (Fin (n + 1))) K)
      (AffineCoefficientField K (MatrixParameters (Fin n) (Fin (n + 1))))
  let S := slEquationMatrix (universalAffineSquare K (Fin n) (Fin (n + 1)))
    (universalAffineRows K (Fin n) (Fin (n + 1))) ⟨0, hn⟩
  have hP : DegreeBound P 1 := fun i j => bidiagonalPencil_degree n j i
  have heP : (universalAffineRows K (Fin n) (Fin (n + 1))).map
      (Polynomial.mapRingHom ψ) = P := by
    rw [universalAffineRows_specialization]
    exact affineMatrixPencil_coefficients P hP
  have heM : (universalAffineSquare K (Fin n) (Fin (n + 1))).map
      (Polynomial.mapRingHom ψ) = 0 := by
    funext i j
    simp [universalAffineSquare, affineMatrixPencil, ψ, affineRowsSpecialization]
  have he : S.map (Polynomial.mapRingHom ψ) = slEquationMatrix 0 P ⟨0, hn⟩ := by
    dsimp only [S]
    rw [slEquationMatrix_map, heM, heP]
  have hg : S.map (Polynomial.mapRingHom φ) = slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin (n + 1)))
      (genericAffineRows K (Fin n) (Fin (n + 1))) ⟨0, hn⟩ := by
    dsimp only [S, φ]
    rw [slEquationMatrix_map, universalAffineSquare_generic, universalAffineRows_generic]
  rw [← hg, polynomialCoefficientMatrix_map]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ (IsFractionRing.injective _ _)
  rw [← polynomialCoefficientMatrix_map, he]
  apply coefficient_matrix_injective_of_bounded_kernel_zero _ d
    (slEquationMatrix_degree 0 P ⟨0, hn⟩ (fun _ _ => by simp) hP)
  exact bidiagonal_sl_bounded_kernel_zero n d hn hd

theorem generic_one_extra_slHilbert_low (n d : ℕ) (hn : 0 < n) (hd : d + 1 < n) :
    slHilbert (genericAffineSquare K (Fin n) (Fin (n + 1)))
      (genericAffineRows K (Fin n) (Fin (n + 1))) d = 0 := by
  rw [slHilbert_eq_matrix_kernel _ _ ⟨0, hn⟩]
  have hk : polynomialKernelAtDegree (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin (n + 1)))
      (genericAffineRows K (Fin n) (Fin (n + 1))) ⟨0, hn⟩) d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hz := bounded_kernel_zero_of_coefficient_matrix_injective _ d
      (generic_one_extra_sl_coefficient_injective (K := K) n d hn hd)
      (fun j => (v j).val) hv (fun j => boundedPoly_degree d (v j))
    funext j
    exact Subtype.ext (congrFun hz j)
  rw [hk, finrank_bot]

end FD56
