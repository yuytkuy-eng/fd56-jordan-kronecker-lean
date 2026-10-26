/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineKernelCoefficientGap
import FD56.LinearAlgebra.PredictableDegree
import FD56.LinearAlgebra.KernelBasis

/-! All coefficients of a reduced polynomial kernel basis of an affine pencil
are jointly independent, including bases with unequal column degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def mixedReversePolynomial (E d : ℕ) (c : Fin (d+1) → K) : K[X] :=
  ∑ k, Polynomial.monomial (E-k.val) (c k)

theorem mixedReversePolynomial_coeff (E d : ℕ) (hd : d ≤ E)
    (c : Fin (d+1) → K) (k : Fin (d+1)) :
    (mixedReversePolynomial E d c).coeff (E-k.val) = c k := by
  classical
  have hi (l : Fin (d+1)) : E-l.val = E-k.val ↔ l = k := by
    constructor
    · intro h
      apply Fin.ext
      have hl := l.isLt
      have hk := k.isLt
      omega
    · rintro rfl
      rfl
  simp only [mixedReversePolynomial, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial, hi, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {a n j : Type*} [Fintype n] [DecidableEq n] [Fintype j]

omit [Fintype n] [DecidableEq n] in
theorem mixed_kernel_combination_middle_coefficient (V : Matrix n j K[X])
    (d : j → ℕ) (E : ℕ) (hd : ∀ j, d j ≤ E)
    (c : (Σ j, Fin (d j+1)) → K) (i : n) :
    ((V *ᵥ fun j => mixedReversePolynomial E (d j) (fun k => c ⟨j,k⟩)) i).coeff E =
      ((fun i (jk : Σ j, Fin (d j+1)) => (V i jk.1).coeff jk.2.val) *ᵥ c) i := by
  simp only [Matrix.mulVec, dotProduct, mixedReversePolynomial, Finset.mul_sum,
    Polynomial.finset_sum_coeff, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hE : k.val + (E-k.val) = E := by have := hd j; have := k.isLt; omega
  simpa only [hE] using
    Polynomial.coeff_mul_monomial (V i j) (E-k.val) k.val (c ⟨j,k⟩)

/-- Joint coefficient independence follows from reducedness and the actual
basis of the affine polynomial kernel. No alternating-form hypothesis is needed. -/
theorem mixed_kernel_basis_coefficients_injective (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j)))) :
    Function.Injective (Matrix.mulVec
      (fun i (jk : Σ j, Fin (d j+1)) =>
        (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i jk.1).coeff jk.2.val)) := by
  classical
  let V := polynomialKernelBasisMatrix (affineMatrixPencil A B) basis
  have hV : Function.Injective V.mulVec := by
    intro x y hxy
    change polynomialKernelBasisMatrix _ basis *ᵥ x =
      polynomialKernelBasisMatrix _ basis *ᵥ y at hxy
    rw [polynomialKernelBasisMatrix_mulVec, polynomialKernelBasisMatrix_mulVec] at hxy
    exact basis.equivFun.symm.injective (Subtype.ext hxy)
  have hAV : affineMatrixPencil A B * V = 0 := polynomialKernelBasisMatrix_mul _ basis
  let E := Finset.univ.sup d + 1
  have hE : 0 < E := by dsimp [E]; omega
  have hdE (j : j) : d j ≤ E := by
    have h := Finset.le_sup (f := d) (Finset.mem_univ j)
    dsimp [E]
    omega
  have hz (c : (Σ j, Fin (d j+1)) → K)
      (hc : (fun i (jk : Σ j, Fin (d j+1)) => (V i jk.1).coeff jk.2.val) *ᵥ c = 0) : c = 0 := by
    let p : j → K[X] := fun j => mixedReversePolynomial E (d j) (fun k => c ⟨j,k⟩)
    let v := V *ᵥ p
    have hv : affineMatrixPencil A B *ᵥ v = 0 := by
      dsimp only [v]
      rw [Matrix.mulVec_mulVec, hAV, Matrix.zero_mulVec]
    have hgap (i : n) : (v i).coeff E = 0 :=
      (mixed_kernel_combination_middle_coefficient V d E hdE c i).trans (congrFun hc i)
    let low : LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B)) :=
      ⟨fun i => polynomialPrefix E (v i),
        affine_kernel_prefix_of_coefficient_zero A B v E hv hgap⟩
    let high : LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B)) :=
      ⟨fun i => polynomialTail (E+1) (v i),
        affine_kernel_tail_of_coefficient_zero A B v E hv hgap⟩
    let lowC := basis.equivFun low
    let highC := basis.equivFun high
    have hlow : V *ᵥ lowC = low.val := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (basis.equivFun.symm_apply_apply low)
    have hhigh : V *ᵥ highC = high.val := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (basis.equivFun.symm_apply_apply high)
    have hp : p = lowC + (X ^ (E+1) : K[X]) • highC := by
      apply hV
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hlow, hhigh]
      funext i
      exact (polynomial_coefficient_gap_split E (v i) (hgap i)).trans
        (by simp only [low, high, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm])
    have hlowDegree : ∀ j, lowC j = 0 ∨
        (d j ≤ E-1 ∧ (lowC j).natDegree ≤ E-1-d j) := by
      apply (polynomial_combination_degree_iff V d lowC (E-1) hdegree hlead).mp
      rw [hlow]
      intro i
      have h := polynomialPrefix_natDegree_lt E hE (v i)
      change (polynomialPrefix E (v i)).natDegree ≤ E-1
      omega
    funext jk
    have hlowCoeff : (lowC jk.1).coeff (E-jk.2.val) = 0 := by
      rcases hlowDegree jk.1 with hl | ⟨hle, hdeg⟩
      · simp [hl]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hk := jk.2.isLt
        have hd := hdE jk.1
        omega
    have hread := congrArg (fun q : j → K[X] => (q jk.1).coeff (E-jk.2.val)) hp
    simpa only [p, mixedReversePolynomial_coeff E (d jk.1) (hdE jk.1),
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_pow_mul', show ¬ E+1 ≤ E-jk.2.val by omega,
      if_false, hlowCoeff, add_zero] using hread
  intro x y hxy
  have h := hz (x-y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

end FD56
