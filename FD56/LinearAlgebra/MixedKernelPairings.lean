/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MixedKernelFunctionals
import FD56.LinearAlgebra.MixedKroneckerCongruence
import FD56.LinearAlgebra.KernelCoefficientIsotropy
import FD56.LinearAlgebra.DualBasis

/-! Actual reduced kernel chains provide the mixed coefficient and pairing matrices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] {r : ℕ}

def mixedKernelCoefficientMatrix (V : Matrix n (Fin r) K[X]) (d : Fin r → ℕ) :
    Matrix n (Σ j, Fin (d j + 1)) K := fun i jk => (V i jk.1).coeff jk.2.val

def mixedKernelPairingMatrix (A : Matrix n n K) (V : Matrix n (Fin r) K[X])
    (d : Fin r → ℕ) : Matrix (Σ j, Fin (d j)) n K :=
  ((mixedKernelCoefficientMatrix V d).submatrix id mixedNext).transpose * A

private theorem mixedNext_injective (d : Fin r → ℕ) :
    Function.Injective (mixedNext (d := d)) := by
  rintro ⟨j,k⟩ ⟨l,h⟩ he
  have hj : j = l := congrArg Sigma.fst he
  subst l
  have hk := congrArg (fun a : Σ j, Fin (d j + 1) => a.2.val) he
  simp only [mixedNext, Fin.val_succ, Nat.add_right_cancel_iff] at hk
  cases Fin.ext hk
  rfl

private theorem mixedCurrent_injective (d : Fin r → ℕ) :
    Function.Injective (mixedCurrent (d := d)) := by
  rintro ⟨j,k⟩ ⟨l,h⟩ he
  have hj : j = l := congrArg Sigma.fst he
  subst l
  have hk := congrArg (fun a : Σ j, Fin (d j + 1) => a.2.val) he
  simp only [mixedCurrent, Fin.coe_castSucc] at hk
  cases Fin.ext hk
  rfl

omit [Fintype n] [DecidableEq n] in
private theorem mixedCrossFirst_mul_zero (d : Fin r → ℕ)
    (L : Matrix (Σ j, Fin (d j)) n K) (j : Fin r) (i : n) :
    (mixedCrossFirst (R := K) d * L) ⟨j,0⟩ i = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hne : (⟨j,0⟩ : Σ j, Fin (d j + 1)) ≠ mixedNext a := by
    intro h
    have hh := congrArg (fun a : Σ j, Fin (d j + 1) => a.2.val) h
    simp [mixedNext] at hh
  simp [mixedCrossFirst, Matrix.submatrix_apply, Matrix.one_apply, hne]

omit [Fintype n] [DecidableEq n] in
private theorem mixedCrossFirst_mul_succ (d : Fin r → ℕ)
    (L : Matrix (Σ j, Fin (d j)) n K) (j : Fin r) (k : Fin (d j)) (i : n) :
    (mixedCrossFirst (R := K) d * L) ⟨j,k.succ⟩ i = L ⟨j,k⟩ i := by
  change (∑ a, (if mixedNext ⟨j,k⟩ = mixedNext a then (1 : K) else 0) * L a i) = _
  simp only [(mixedNext_injective d).eq_iff, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype n] [DecidableEq n] in
private theorem mixedCrossSecond_mul_last (d : Fin r → ℕ)
    (L : Matrix (Σ j, Fin (d j)) n K) (j : Fin r) (i : n) :
    (mixedCrossSecond (R := K) d * L) ⟨j,Fin.last (d j)⟩ i = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hne : (⟨j,Fin.last (d j)⟩ : Σ j, Fin (d j + 1)) ≠ mixedCurrent a := by
    rcases a with ⟨l,k⟩
    intro h
    have hj : j = l := congrArg Sigma.fst h
    subst l
    have hh := congrArg (fun a : Σ j, Fin (d j + 1) => a.2.val) h
    simp only [mixedCurrent, Fin.val_last, Fin.coe_castSucc] at hh
    have hk := k.isLt
    omega
  simp [mixedCrossSecond, Matrix.submatrix_apply, Matrix.one_apply, hne]

omit [Fintype n] [DecidableEq n] in
private theorem mixedCrossSecond_mul_castSucc (d : Fin r → ℕ)
    (L : Matrix (Σ j, Fin (d j)) n K) (j : Fin r) (k : Fin (d j)) (i : n) :
    (mixedCrossSecond (R := K) d * L) ⟨j,k.castSucc⟩ i = -L ⟨j,k⟩ i := by
  change (∑ a, -(if mixedCurrent ⟨j,k⟩ = mixedCurrent a then (1 : K) else 0) * L a i) = _
  simp only [(mixedCurrent_injective d).eq_iff, neg_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [DecidableEq n] in
private theorem mixed_skew_row_pairing (A : Matrix n n K) (hA : A.transpose = -A)
    (v : n → K) (i : n) : (∑ j, v j * A j i) = -(A *ᵥ v) i := by
  have ha (j : n) : A j i = -A i j := congrArg (fun M => M i j) hA
  simp [ha, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq n] in
theorem mixed_kernel_pairing_identities (d : Fin r → ℕ)
    (A B : Matrix n n K) (V : Matrix n (Fin r) K[X])
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAV : affineMatrixPencil A B * V = 0)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j) :
    (mixedKernelCoefficientMatrix V d).transpose * A =
        mixedCrossFirst (R := K) d * mixedKernelPairingMatrix A V d ∧
    (mixedKernelCoefficientMatrix V d).transpose * B =
        mixedCrossSecond (R := K) d * mixedKernelPairingMatrix A V d := by
  have hcol (j : Fin r) : affineMatrixPencil A B *ᵥ (fun i => V i j) = 0 := by
    funext i
    exact congrArg (fun M => M i j) hAV
  have hz (i : n) (j : Fin r) : (A *ᵥ fun x => (V x j).coeff 0) i = 0 :=
    congrFun (affine_kernel_coefficient_initial A B _ (hcol j)) i
  have hs (i : n) (j : Fin r) (k : ℕ) :
      (A *ᵥ fun x => (V x j).coeff (k + 1)) i +
        (B *ᵥ fun x => (V x j).coeff k) i = 0 :=
    congrFun (affine_kernel_coefficient_recurrence A B _ (hcol j) k) i
  have hl (i : n) (j : Fin r) : (B *ᵥ fun x => (V x j).coeff (d j)) i = 0 := by
    have h := hs i j (d j)
    have hzero : (fun x => (V x j).coeff (d j + 1)) = 0 := by
      funext x
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have := hdegree x j
      omega
    simpa only [hzero, Matrix.mulVec_zero, Pi.zero_apply, zero_add] using h
  constructor
  · funext jk i
    rcases jk with ⟨j,k⟩
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [mixedCrossFirst_mul_zero]
      change (∑ x, (V x j).coeff 0 * A x i) = 0
      rw [mixed_skew_row_pairing A hA, hz, neg_zero]
    · rw [mixedCrossFirst_mul_succ]
      rfl
  · funext jk i
    rcases jk with ⟨j,k⟩
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [mixedCrossSecond_mul_last]
      change (∑ x, (V x j).coeff (d j) * B x i) = 0
      rw [mixed_skew_row_pairing B hB, hl, neg_zero]
    · rw [mixedCrossSecond_mul_castSucc]
      change (∑ x, (V x j).coeff k.val * B x i) =
        -(∑ x, (V x j).coeff (k.val + 1) * A x i)
      rw [mixed_skew_row_pairing B hB, mixed_skew_row_pairing A hA, neg_neg]
      exact (eq_neg_of_add_eq_zero_left (hs i j k.val)).symm

theorem mixed_kernel_basis_pairing_surjective (A B : Matrix n n K)
    (basis : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : Fin r → ℕ) (hA : A.transpose = -A)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j)))) :
    Function.Surjective (mixedKernelPairingMatrix A
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis) d).mulVec := by
  let V := polynomialKernelBasisMatrix (affineMatrixPencil A B) basis
  have hf := mixed_kernel_basis_functionals_injective A B basis d hdegree hlead
  have hinj : Function.Injective
      (A * (mixedKernelCoefficientMatrix V d).submatrix id mixedNext).mulVec := hf
  apply matrix_surjective_of_transpose_injective
  have ht : (mixedKernelPairingMatrix A V d).transpose =
      -(A * (mixedKernelCoefficientMatrix V d).submatrix id mixedNext) := by
    simp [mixedKernelPairingMatrix, Matrix.transpose_mul, hA]
  intro x y hxy
  apply hinj
  change (mixedKernelPairingMatrix A V d).transpose *ᵥ x =
    (mixedKernelPairingMatrix A V d).transpose *ᵥ y at hxy
  simpa only [ht, Matrix.neg_mulVec, neg_inj] using hxy

omit [DecidableEq n] in
theorem mixed_kernel_pairing_annihilates_coefficients (d : Fin r → ℕ)
    (A B : Matrix n n K) (V : Matrix n (Fin r) K[X])
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAV : affineMatrixPencil A B * V = 0) :
    mixedKernelPairingMatrix A V d * mixedKernelCoefficientMatrix V d = 0 := by
  have hiso := (kernel_coefficient_matrix_isotropic (s := Σ j, Fin (d j + 1))
    A B hA hB V hAV Sigma.fst (fun jk => jk.2.val)).1
  have h := congrArg (fun M => M.submatrix mixedNext id) hiso
  simpa only [mixedKernelPairingMatrix, mixedKernelCoefficientMatrix,
    Matrix.transpose_submatrix, Matrix.submatrix_mul _ _ _ id id Function.bijective_id,
    Matrix.submatrix_id_id, Matrix.submatrix_zero] using h

end FD56
