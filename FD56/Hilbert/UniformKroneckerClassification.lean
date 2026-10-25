/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile
import FD56.LinearAlgebra.UniformKernelFunctionals
import FD56.LinearAlgebra.UniformKroneckerBasis
import FD56.LinearAlgebra.DualBasis
import FD56.LinearAlgebra.KernelCoefficientIsotropy

/-! Uniform minimal kernel degrees provide the actual polynomial chains used
in the full-dimension constant-congruence construction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A reduced kernel basis of uniform degree admits no shorter kernel vector. -/
theorem uniform_kernel_basis_no_short_vectors {r e : ℕ}
    (P : Matrix a n K[X])
    (B : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix P B i j).natDegree ≤ e)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix P B i j).coeff e))) :
    ∀ v : n → K[X], P *ᵥ v = 0 → (∀ i, (v i).natDegree < e) → v = 0 := by
  intro v hv hd
  by_cases he : 0 < e
  · let v' : LinearMap.ker (Matrix.toLin' P) := ⟨v, hv⟩
    let c := B.equivFun v'
    have hc : polynomialKernelBasisMatrix P B *ᵥ c = v := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (B.equivFun.symm_apply_apply v')
    have hcdegree := (polynomial_combination_degree_iff
      (polynomialKernelBasisMatrix P B) (fun _ => e) c (e-1) hdegree hlead).mp
        (by rw [hc]; intro i; have := hd i; omega)
    have hczero : c = 0 := by
      funext j
      rcases hcdegree j with hj | hj
      · exact hj
      · omega
    rw [hczero, Matrix.mulVec_zero] at hc
    exact hc.symm
  · funext i
    have := hd i
    omega

/-- Extract a uniform family from the actual reduced kernel basis promised
by the minimal-degree predicate. -/
theorem exists_uniform_kernel_matrix_of_minimal_degrees {r e : ℕ}
    (P : Matrix a n K[X]) (hP : HasMinimalKernelDegrees P (List.replicate r e)) :
    ∃ V : Matrix n (Fin r) K[X], P * V = 0 ∧ Function.Injective V.mulVec ∧
      (∀ i j, (V i j).natDegree ≤ e) ∧
      Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff e)) ∧
      ∀ v : n → K[X], P *ᵥ v = 0 → (∀ i, (v i).natDegree < e) → v = 0 := by
  obtain ⟨s, B, d, hdegree, hlead, hperm⟩ := hP
  have hs : s = r := by simpa using hperm.length_eq
  subst s
  have hd : d = fun _ => e := by
    funext j
    have hj : d j ∈ List.replicate r e :=
      hperm.mem_iff.mp (List.mem_ofFn.mpr ⟨j, rfl⟩)
    exact (List.mem_replicate.mp hj).2
  have hdegree' : ∀ i j, (polynomialKernelBasisMatrix P B i j).natDegree ≤ e := by
    simpa only [hd] using hdegree
  have hlead' : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix P B i j).coeff e)) := by
    simpa only [hd] using hlead
  refine ⟨polynomialKernelBasisMatrix P B, polynomialKernelBasisMatrix_mul P B,
    ?_, hdegree', hlead', uniform_kernel_basis_no_short_vectors P B hdegree' hlead'⟩
  intro x y hxy
  rw [polynomialKernelBasisMatrix_mulVec, polynomialKernelBasisMatrix_mulVec] at hxy
  exact B.equivFun.symm.injective (Subtype.ext hxy)

def uniformKernelCoefficientMatrix {r : ℕ} (V : Matrix n (Fin r) K[X]) (e : ℕ) :
    Matrix n (Fin (e+1) × Fin r) K := fun i kj => (V i kj.2).coeff kj.1.val

def uniformKernelPairingMatrix {r : ℕ} (A : Matrix n n K)
    (V : Matrix n (Fin r) K[X]) (e : ℕ) : Matrix (Fin e × Fin r) n K :=
  ((uniformKernelCoefficientMatrix V e).submatrix id uniformNext).transpose * A

omit [Fintype n] [DecidableEq n] in
private theorem uniformCrossFirst_mul_zero {e r : ℕ}
    (L : Matrix (Fin e × Fin r) n K) (j : Fin r) (i : n) :
    (uniformCrossFirst (R := K) (e := e) (r := r) * L) (0,j) i = 0 := by
  simp [uniformCrossFirst, uniformNext, Matrix.mul_apply, Matrix.submatrix,
    Matrix.one_apply, Prod.mk.injEq, eq_comm]

omit [Fintype n] [DecidableEq n] in
private theorem uniformCrossFirst_mul_succ {e r : ℕ}
    (L : Matrix (Fin e × Fin r) n K) (j : Fin r) (k : Fin e) (i : n) :
    (uniformCrossFirst (R := K) (e := e) (r := r) * L) (k.succ,j) i = L (k,j) i := by
  simp [uniformCrossFirst, uniformNext, Matrix.mul_apply, Matrix.submatrix,
    Matrix.one_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and, eq_comm]

omit [Fintype n] [DecidableEq n] in
private theorem uniformCrossSecond_mul_last {e r : ℕ}
    (L : Matrix (Fin e × Fin r) n K) (j : Fin r) (i : n) :
    (uniformCrossSecond (R := K) (e := e) (r := r) * L) (Fin.last e,j) i = 0 := by
  simp [uniformCrossSecond, uniformCurrent, Matrix.mul_apply, Matrix.submatrix,
    Matrix.one_apply, Prod.mk.injEq, eq_comm]

omit [Fintype n] [DecidableEq n] in
private theorem uniformCrossSecond_mul_castSucc {e r : ℕ}
    (L : Matrix (Fin e × Fin r) n K) (j : Fin r) (k : Fin e) (i : n) :
    (uniformCrossSecond (R := K) (e := e) (r := r) * L) (k.castSucc,j) i = -L (k,j) i := by
  simp [uniformCrossSecond, uniformCurrent, Matrix.mul_apply, Matrix.submatrix,
    Matrix.one_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and, eq_comm]

omit [DecidableEq n] in
private theorem skew_row_pairing (A : Matrix n n K) (hA : A.transpose = -A)
    (v : n → K) (i : n) : (∑ j, v j * A j i) = -(A *ᵥ v) i := by
  have ha (j : n) : A j i = -A i j := congrArg (fun M => M i j) hA
  simp [ha, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq n] in
theorem uniform_kernel_pairing_identities {e r : ℕ}
    (A B : Matrix n n K) (V : Matrix n (Fin r) K[X])
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAV : affineMatrixPencil A B * V = 0)
    (hdegree : ∀ i j, (V i j).natDegree ≤ e) :
    (uniformKernelCoefficientMatrix V e).transpose * A =
        uniformCrossFirst * uniformKernelPairingMatrix A V e ∧
    (uniformKernelCoefficientMatrix V e).transpose * B =
        uniformCrossSecond * uniformKernelPairingMatrix A V e := by
  have hcol (j : Fin r) : affineMatrixPencil A B *ᵥ (fun i => V i j) = 0 := by
    funext i
    exact congrArg (fun M => M i j) hAV
  have hz (i : n) (j : Fin r) : (A *ᵥ fun x => (V x j).coeff 0) i = 0 := by
    have h := congrArg (fun v : n → K[X] => (v i).coeff 0) (hcol j)
    simpa only [affineMatrixPencil_mulVec_coeff_zero, Pi.zero_apply,
      Polynomial.coeff_zero] using h
  have hs (i : n) (j : Fin r) (k : ℕ) :
      (A *ᵥ fun x => (V x j).coeff (k+1)) i +
        (B *ᵥ fun x => (V x j).coeff k) i = 0 := by
    have h := congrArg (fun v : n → K[X] => (v i).coeff (k+1)) (hcol j)
    simpa only [affineMatrixPencil_mulVec_coeff_succ, Pi.zero_apply,
      Polynomial.coeff_zero] using h
  have hl (i : n) (j : Fin r) : (B *ᵥ fun x => (V x j).coeff e) i = 0 := by
    have h := hs i j e
    have hzero : (fun x => (V x j).coeff (e+1)) = 0 := by
      funext x
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have := hdegree x j
      omega
    simpa only [hzero, Matrix.mulVec_zero, Pi.zero_apply, zero_add] using h
  constructor
  · funext kj i
    rcases kj with ⟨k,j⟩
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [uniformCrossFirst_mul_zero]
      change (∑ x, (V x j).coeff 0 * A x i) = 0
      rw [skew_row_pairing A hA, hz, neg_zero]
    · rw [uniformCrossFirst_mul_succ]
      rfl
  · funext kj i
    rcases kj with ⟨k,j⟩
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [uniformCrossSecond_mul_last]
      change (∑ x, (V x j).coeff e * B x i) = 0
      rw [skew_row_pairing B hB, hl, neg_zero]
    · rw [uniformCrossSecond_mul_castSucc]
      change (∑ x, (V x j).coeff k.val * B x i) =
        -(∑ x, (V x j).coeff (k.val+1) * A x i)
      rw [skew_row_pairing B hB, skew_row_pairing A hA, neg_neg]
      exact (eq_neg_of_add_eq_zero_left (hs i j k.val)).symm

omit [Fintype n] [DecidableEq n] in
private theorem mulVec_injective_column_equiv {s t : Type*}
    [Fintype s] [Fintype t] (M : Matrix n s K) (c : t ≃ s)
    (hM : Function.Injective M.mulVec) :
    Function.Injective (M.submatrix id c).mulVec := by
  intro x y hxy
  rw [Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv] at hxy
  have h : x ∘ c.symm = y ∘ c.symm := hM hxy
  funext i
  simpa only [Function.comp_apply, c.symm_apply_apply] using congrFun h (c i)

theorem uniform_kernel_pairing_surjective {e r : ℕ}
    (A B : Matrix n n K) (V : Matrix n (Fin r) K[X])
    (hA : A.transpose = -A) (hAV : affineMatrixPencil A B * V = 0)
    (hdegree : ∀ i j, (V i j).natDegree ≤ e)
    (hshort : ∀ v : n → K[X], affineMatrixPencil A B *ᵥ v = 0 →
      (∀ i, (v i).natDegree < e) → v = 0)
    (hcoeff : Function.Injective (Matrix.mulVec
      (fun i (jk : Fin r × Fin (e+1)) => (V i jk.1).coeff jk.2.val))) :
    Function.Surjective (uniformKernelPairingMatrix A V e).mulVec := by
  have hf := uniform_kernel_functionals_injective A B V e hAV hdegree hshort hcoeff
  have hinj : Function.Injective
      (A * (uniformKernelCoefficientMatrix V e).submatrix id uniformNext).mulVec := by
    exact mulVec_injective_column_equiv _ (Equiv.prodComm (Fin e) (Fin r)) hf
  apply matrix_surjective_of_transpose_injective
  have ht : (uniformKernelPairingMatrix A V e).transpose =
      -(A * (uniformKernelCoefficientMatrix V e).submatrix id uniformNext) := by
    simp [uniformKernelPairingMatrix, Matrix.transpose_mul, hA]
  intro x y hxy
  apply hinj
  simpa only [ht, Matrix.neg_mulVec, neg_inj] using hxy

/-- Uniform minimal kernel degrees and the exact dimension budget imply an
actual simultaneous constant congruence. No decomposition is assumed. -/
theorem uniform_minimal_degrees_constant_congruence {e r : ℕ}
    (A B : Matrix n n K)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) (List.replicate r e))
    (hcard : Fintype.card n = r * (2*e+1))
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ G : Matrix n ((Fin (e+1) × Fin r) ⊕ (Fin e × Fin r)) K,
    ∃ J : Matrix ((Fin (e+1) × Fin r) ⊕ (Fin e × Fin r)) n K,
      G * J = 1 ∧ J * G = 1 ∧
      G.transpose * A * G =
        Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) 0 ∧
      G.transpose * B * G =
        Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) 0 := by
  obtain ⟨V, hAV, hV, hdegree, _, hshort⟩ :=
    exists_uniform_kernel_matrix_of_minimal_degrees (affineMatrixPencil A B) hmin
  have hcoeff := uniform_kernel_coefficients_injective A B V e hAV hV hdegree hshort
  have hW : Function.Injective (uniformKernelCoefficientMatrix V e).mulVec :=
    mulVec_injective_column_equiv _ (Equiv.prodComm (Fin (e+1)) (Fin r)) hcoeff
  have hL := uniform_kernel_pairing_surjective A B V hA hAV hdegree hshort hcoeff
  have hiso := (uniform_kernel_coefficient_matrix_isotropic A B hA hB V hAV e).1
  have hLW : uniformKernelPairingMatrix A V e * uniformKernelCoefficientMatrix V e = 0 := by
    have h := congrArg (fun M => M.submatrix uniformNext id) hiso
    simpa only [uniformKernelPairingMatrix, uniformKernelCoefficientMatrix,
      Matrix.transpose_submatrix, Matrix.submatrix_mul _ _ _ id id Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.submatrix_zero] using h
  obtain ⟨hWA, hWB⟩ := uniform_kernel_pairing_identities A B V hA hB hAV hdegree
  apply exists_uniform_kronecker_basis A B (uniformKernelCoefficientMatrix V e)
    (uniformKernelPairingMatrix A V e) _ hW hL hLW hWA hWB hA hB hAltA hAltB
  rw [hcard]
  ring

end FD56
