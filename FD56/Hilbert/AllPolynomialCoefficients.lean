/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CoefficientMatrix
import FD56.Hilbert.KernelDimension

/-! Using every output coefficient detects bounded polynomial kernels over
any commutative ring, without a bound on the matrix degree. The input column
set remains finite even though the output coefficient index is infinite. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R S K a b : Type*} [CommRing R] [CommRing S] [Field K]

def allPolynomialCoefficientMatrix (P : Matrix a b R[X]) (d : ℕ) :
    Matrix (a × ℕ) (b × Fin (d+1)) R :=
  fun ik jl => (P ik.1 jl.1*X^jl.2.val).coeff ik.2

theorem allPolynomialCoefficientMatrix_mulVec [Fintype b] [DecidableEq R]
    (P : Matrix a b R[X]) (d : ℕ) (v : b × Fin (d+1) → R)
    (i : a) (k : ℕ) :
    (allPolynomialCoefficientMatrix P d*ᵥv) (i,k)=
      ((P*ᵥcoefficientVectorPolynomial d v) i).coeff k := by
  simp only [allPolynomialCoefficientMatrix,Matrix.mulVec,dotProduct,
    coefficientVectorPolynomial,Polynomial.ofFn_eq_sum_monomial,
    Finset.mul_sum,Polynomial.finset_sum_coeff,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have hh : P i j*Polynomial.monomial l.val (v (j,l))=
      C (v (j,l))*(P i j*X^l.val) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    ring
  rw [hh,Polynomial.coeff_C_mul]
  exact mul_comm _ _

theorem allPolynomialCoefficientMatrix_kernel_iff [Fintype b] [DecidableEq R]
    (P : Matrix a b R[X]) (d : ℕ) (v : b × Fin (d+1) → R) :
    allPolynomialCoefficientMatrix P d*ᵥv=0 ↔ P*ᵥcoefficientVectorPolynomial d v=0 := by
  constructor
  · intro h
    funext i
    apply Polynomial.ext
    intro k
    exact (allPolynomialCoefficientMatrix_mulVec P d v i k).symm.trans
      (congrFun h (i,k))
  · intro h
    funext ik
    rw [allPolynomialCoefficientMatrix_mulVec,h]
    rfl

theorem allPolynomialCoefficientMatrix_map (P : Matrix a b R[X]) (d : ℕ)
    (φ : R →+* S) :
    allPolynomialCoefficientMatrix (P.map (Polynomial.mapRingHom φ)) d=
      (allPolynomialCoefficientMatrix P d).map φ := by
  funext i j
  simp [allPolynomialCoefficientMatrix,← Polynomial.coeff_map,Polynomial.map_mul]

theorem coefficientVectorPolynomial_map [DecidableEq R] [DecidableEq S]
    (d : ℕ) (v : b × Fin (d+1) → R) (φ : R →+* S) :
    coefficientVectorPolynomial d (fun jl => φ (v jl))=
      fun j => (coefficientVectorPolynomial d v j).map φ := by
  funext j
  apply Polynomial.ext
  intro k
  by_cases hk : k<d+1
  · simp [coefficientVectorPolynomial,hk]
  · simp [coefficientVectorPolynomial,Nat.le_of_not_lt hk]

def allCoefficientKernelEquiv [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (d : ℕ) :
    LinearMap.ker (Matrix.toLin' (allPolynomialCoefficientMatrix P d)) ≃ₗ[K]
      polynomialKernelAtDegree P d := by
  classical
  exact {
    toFun := fun v => ⟨fun j => boundedPolyOf (coefficientVectorPolynomial d v.val j)
      (coefficientVectorPolynomial_degree d v.val j),
        (allPolynomialCoefficientMatrix_kernel_iff P d v.val).mp v.property⟩
    invFun := fun v => ⟨fun jl => (v.val jl.1).val.coeff jl.2.val, by
      have he : coefficientVectorPolynomial d
          (fun jl => (v.val jl.1).val.coeff jl.2.val)=fun j => (v.val j).val := by
        funext j
        exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
          (p:=(v.val j).val) (n:=d+1)
          (by have := boundedPoly_degree d (v.val j); omega)
      apply (allPolynomialCoefficientMatrix_kernel_iff P d _).mpr
      rw [he]
      exact v.property⟩
    left_inv := fun v => by
      apply Subtype.ext
      funext jl
      simp [coefficientVectorPolynomial,boundedPolyOf]
    right_inv := fun v => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (p:=(v.val j).val) (n:=d+1)
        (by have := boundedPoly_degree d (v.val j); omega)
    map_add' := fun v w => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      change Polynomial.ofFn (d+1) _=_
      exact map_add (Polynomial.ofFn (d+1)) _ _
    map_smul' := fun c v => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      change Polynomial.ofFn (d+1) _=_
      exact map_smul (Polynomial.ofFn (d+1)) c _ }

theorem all_coefficient_kernel_finrank [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (d : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (allPolynomialCoefficientMatrix P d)))=
      Module.finrank K (polynomialKernelAtDegree P d) :=
  (allCoefficientKernelEquiv P d).finrank_eq

end FD56
