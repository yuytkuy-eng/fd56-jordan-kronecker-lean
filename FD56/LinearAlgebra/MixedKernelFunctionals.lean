/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MixedKernelCoefficients

/-! Pairing functionals of a reduced affine kernel basis are independent for unequal degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a n j : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype j]

theorem mixed_kernel_basis_functionals_injective_of_coefficients (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hcoeff : Function.Injective (Matrix.mulVec (fun i (jk : Σ j, Fin (d j + 1)) =>
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i jk.1).coeff jk.2.val))) :
    Function.Injective (Matrix.mulVec (fun i (jk : Σ j, Fin (d j)) =>
      (A *ᵥ fun x => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis x jk.1).coeff
        (jk.2.val + 1)) i)) := by
  classical
  let V := polynomialKernelBasisMatrix (affineMatrixPencil A B) basis
  have hAV : affineMatrixPencil A B * V = 0 := polynomialKernelBasisMatrix_mul _ basis
  have hcol (l : j) : affineMatrixPencil A B *ᵥ (fun i => V i l) = 0 := by
    funext i
    exact congrFun (congrFun hAV i) l
  have hz (c : (Σ j, Fin (d j)) → K)
      (hc : (fun i (jk : Σ j, Fin (d j)) =>
        (A *ᵥ fun x => (V x jk.1).coeff (jk.2.val + 1)) i) *ᵥ c = 0) : c = 0 := by
    let u : n → K[X] := fun i =>
      ∑ jk : Σ j, Fin (d j), Polynomial.C (c jk) * polynomialTail (jk.2.val + 1) (V i jk.1)
    have hucoeff (i : n) (k : ℕ) :
        (u i).coeff k = ∑ jk : Σ j, Fin (d j), c jk * (V i jk.1).coeff (k + (jk.2.val + 1)) := by
      simp only [u, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, polynomialTail_coeff]
    have huker : affineMatrixPencil A B *ᵥ u = 0 := by
      funext i
      apply Polynomial.ext
      intro k
      simp only [Pi.zero_apply, Polynomial.coeff_zero]
      cases k with
      | zero =>
        rw [affineMatrixPencil_mulVec_coeff_zero]
        have h := congrFun hc i
        simp only [Matrix.mulVec, dotProduct, hucoeff, zero_add, Finset.mul_sum] at h ⊢
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul] at h
        simpa only [mul_assoc, mul_comm, mul_left_comm, Pi.zero_apply] using h
      | succ k =>
        rw [affineMatrixPencil_mulVec_coeff_succ]
        simp only [Matrix.mulVec, dotProduct, hucoeff, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun x (jk : Σ j, Fin (d j)) =>
          A i x * (c jk * (V x jk.1).coeff ((k + 1) + (jk.2.val + 1)))),
          Finset.sum_comm (f := fun x (jk : Σ j, Fin (d j)) =>
          B i x * (c jk * (V x jk.1).coeff (k + (jk.2.val + 1))))]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro jk _
        have h := congrArg (fun z : a → K[X] => (z i).coeff ((k + (jk.2.val + 1)) + 1))
          (hcol jk.1)
        dsimp only at h
        rw [affineMatrixPencil_mulVec_coeff_succ] at h
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Polynomial.coeff_zero] at h
        have hmul := congrArg (fun x : K => c jk * x) h
        simpa only [mul_add, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm,
          Nat.add_right_comm k 1 (jk.2.val + 1), mul_zero] using hmul
    let up : LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B)) := ⟨u, huker⟩
    let p := basis.equivFun up
    have hup : V *ᵥ p = u := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (basis.equivFun.symm_apply_apply up)
    have hconstant (i : n) :
        (∑ jk : Σ j, Fin (d j), c jk * (V i jk.1).coeff (jk.2.val + 1)) =
          ∑ l : j, (V i l).coeff 0 * (p l).coeff 0 := by
      have h := congrArg (fun q : K[X] => q.coeff 0) (congrFun hup i)
      simpa only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff,
        Polynomial.mul_coeff_zero, hucoeff, zero_add] using h.symm
    let c' : (Σ j, Fin (d j + 1)) → K := fun jk =>
      Fin.cases (-(p jk.1).coeff 0) (fun k => c ⟨jk.1,k⟩) jk.2
    have hc' : c' = 0 := by
      apply hcoeff
      rw [Matrix.mulVec_zero]
      funext i
      change (∑ jk : Σ j, Fin (d j + 1), (V i jk.1).coeff jk.2.val * c' jk) = 0
      simp only [Fintype.sum_sigma, Fin.sum_univ_succ, c', Fin.cases_zero,
        Fin.cases_succ, Fin.val_zero, Fin.val_succ, mul_neg, Finset.sum_add_distrib]
      rw [Finset.sum_neg_distrib]
      have hs : (∑ l : j, ∑ k : Fin (d l), (V i l).coeff (k.val + 1) * c ⟨l,k⟩) =
          ∑ jk : Σ j, Fin (d j), c jk * (V i jk.1).coeff (jk.2.val + 1) := by
        simp only [Fintype.sum_sigma, mul_comm]
      rw [hs, hconstant, neg_add_cancel]
    funext jk
    exact congrFun hc' ⟨jk.1,jk.2.succ⟩
  intro x y hxy
  have h := hz (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

theorem mixed_kernel_basis_functionals_injective (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j)))) :
    Function.Injective (Matrix.mulVec (fun i (jk : Σ j, Fin (d j)) =>
      (A *ᵥ fun x => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis x jk.1).coeff
        (jk.2.val + 1)) i)) :=
  mixed_kernel_basis_functionals_injective_of_coefficients A B basis d
    (mixed_kernel_basis_coefficients_injective A B basis d hdegree hlead)

end FD56
