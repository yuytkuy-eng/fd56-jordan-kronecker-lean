/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.EquationDegree
import FD56.Stabilizer.GenericRows

/-! Low-degree translation vanishing at one affine witness implies
low-degree vanishing for the actual generic SL stabilizer. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem sl_bounded_kernel_zero_of_translation (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hPi : Function.Injective P.mulVec) (i₀ : n) (d : ℕ)
    (hlow : ∀ (U : Matrix n m K[X]) (c : K[X]),
      U * P = c • (1 : Matrix n n K[X]) → DegreeBound U d → U = 0)
    (v : SLInput n m → K[X]) (hv : slEquationMatrix M P i₀ *ᵥ v = 0)
    (hdeg : ∀ j, (v j).natDegree ≤ d) : v = 0 := by
  letI : Nonempty n := ⟨i₀⟩
  have hs := (slEquationMatrix_kernel_iff M P i₀ v).mp hv
  obtain ⟨_, hPX, c, hc⟩ := (slRadical_iff_equations M P _ _).mp hs
  have hX : (show Matrix n n K[X] from fun i j => v (.inl (i, j))) = 0 := by
    funext i j
    have hz : P *ᵥ (fun k => v (.inl (k, j))) = 0 := by
      funext k
      exact congrArg (fun A : Matrix m n K[X] => A k j) hPX
    exact congrFun (hPi (hz.trans (Matrix.mulVec_zero P).symm)) i
  have hUP : (show Matrix n m K[X] from fun i j => v (.inr (i, j))) * P =
      (-c) • (1 : Matrix n n K[X]) := by
    change (fun i j => v (.inl (i, j))) = (0 : Matrix n n K[X]) at hX
    rw [hX] at hc
    have hh : (show Matrix n m K[X] from fun i j => v (.inr (i, j))) * P +
        c • (1 : Matrix n n K[X]) = 0 := by simpa using hc.symm
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hh
  have hU := hlow (fun i j => v (.inr (i, j))) (-c) hUP
    (fun i j => hdeg (.inr (i, j)))
  funext j
  rcases j with ij | ij
  · exact congrArg (fun A : Matrix n n K[X] => A ij.1 ij.2) hX
  · exact congrArg (fun A : Matrix n m K[X] => A ij.1 ij.2) hU

theorem generic_sl_coefficient_injective_of_witness (P : Matrix m n K[X])
    (hP : DegreeBound P 1) (hPi : Function.Injective P.mulVec) (i₀ : n) (d : ℕ)
    (hlow : ∀ (U : Matrix n m K[X]) (c : K[X]),
      U * P = c • (1 : Matrix n n K[X]) → DegreeBound U d → U = 0) :
    Function.Injective (polynomialCoefficientMatrix
      (slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀) d).mulVec := by
  classical
  let A : Matrix m n K := fun i j => (P i j).coeff 0
  let B : Matrix m n K := fun i j => (P i j).coeff 1
  let ψ := affineRowsSpecialization A B
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let S := slEquationMatrix (universalAffineSquare K n m) (universalAffineRows K n m) i₀
  have heP : (universalAffineRows K n m).map (Polynomial.mapRingHom ψ) = P := by
    rw [universalAffineRows_specialization]
    exact affineMatrixPencil_coefficients P hP
  have heM : (universalAffineSquare K n m).map (Polynomial.mapRingHom ψ) = 0 := by
    funext i j
    simp [universalAffineSquare, affineMatrixPencil, ψ, affineRowsSpecialization]
  have he : S.map (Polynomial.mapRingHom ψ) = slEquationMatrix 0 P i₀ := by
    dsimp only [S]
    rw [slEquationMatrix_map, heM, heP]
  have hg : S.map (Polynomial.mapRingHom φ) =
      slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀ := by
    dsimp only [S, φ]
    rw [slEquationMatrix_map, universalAffineSquare_generic, universalAffineRows_generic]
  rw [← hg, polynomialCoefficientMatrix_map]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => by simp [ψ, affineRowsSpecialization]) φ (IsFractionRing.injective _ _)
  rw [← polynomialCoefficientMatrix_map, he]
  apply coefficient_matrix_injective_of_bounded_kernel_zero _ d
    (slEquationMatrix_degree 0 P i₀ (fun _ _ => by simp) hP)
  exact sl_bounded_kernel_zero_of_translation 0 P hPi i₀ d hlow

theorem generic_slHilbert_zero_of_witness (P : Matrix m n K[X])
    (hP : DegreeBound P 1) (hPi : Function.Injective P.mulVec) (i₀ : n) (d : ℕ)
    (hlow : ∀ (U : Matrix n m K[X]) (c : K[X]),
      U * P = c • (1 : Matrix n n K[X]) → DegreeBound U d → U = 0) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d = 0 := by
  rw [slHilbert_eq_matrix_kernel _ _ i₀]
  have hk : polynomialKernelAtDegree (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hz := bounded_kernel_zero_of_coefficient_matrix_injective _ d
      (generic_sl_coefficient_injective_of_witness P hP hPi i₀ d hlow)
      (fun j => (v j).val) hv (fun j => boundedPoly_degree d (v j))
    funext j
    exact Subtype.ext (congrFun hz j)
  rw [hk, finrank_bot]

end FD56
