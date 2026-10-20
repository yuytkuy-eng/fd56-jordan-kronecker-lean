/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BidiagonalPencil
import FD56.LinearAlgebra.RankSpecialization
import Mathlib.Algebra.Polynomial.ofFn

/-! Finite coefficient matrices detect bounded polynomial solutions and
provide polynomial right inverses for affine rectangular pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R K a b : Type*} [CommRing R] [Field K]

def polynomialCoefficientMatrix (P : Matrix a b R[X]) (d : ℕ) :
    Matrix (a × Fin (d + 2)) (b × Fin (d + 1)) R :=
  fun ik jl => (P ik.1 jl.1 * Polynomial.X ^ jl.2.val).coeff ik.2.val

def coefficientVectorPolynomial [DecidableEq R] (d : ℕ)
    (v : b × Fin (d + 1) → R) : b → R[X] :=
  fun j => Polynomial.ofFn (d + 1) (fun l => v (j, l))

theorem coefficientVectorPolynomial_degree [DecidableEq R] (d : ℕ)
    (v : b × Fin (d + 1) → R) (j : b) :
    (coefficientVectorPolynomial d v j).natDegree ≤ d := by
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)

theorem polynomialCoefficientMatrix_mulVec [Fintype b] [DecidableEq R]
    (P : Matrix a b R[X]) (d : ℕ) (v : b × Fin (d + 1) → R)
    (i : a) (k : Fin (d + 2)) :
    (polynomialCoefficientMatrix P d *ᵥ v) (i, k) =
      ((P *ᵥ coefficientVectorPolynomial d v) i).coeff k.val := by
  simp only [polynomialCoefficientMatrix, Matrix.mulVec, dotProduct,
    coefficientVectorPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Finset.mul_sum, Polynomial.finset_sum_coeff, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have hh : P i j * Polynomial.monomial l.val (v (j, l)) =
      Polynomial.C (v (j, l)) * (P i j * Polynomial.X ^ l.val) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    ring
  rw [hh, Polynomial.coeff_C_mul]
  exact mul_comm _ _

theorem polynomialCoefficientMatrix_map (P : Matrix a b R[X]) (d : ℕ)
    (φ : R →+* K) :
    polynomialCoefficientMatrix (P.map (Polynomial.mapRingHom φ)) d =
      (polynomialCoefficientMatrix P d).map φ := by
  funext i j
  simp [polynomialCoefficientMatrix, ← Polynomial.coeff_map, Polynomial.map_mul]

theorem polynomial_mulVec_degree [Fintype b] (P : Matrix a b K[X])
    (v : b → K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hv : ∀ j, (v j).natDegree ≤ d) (i : a) :
    ((P *ᵥ v) i).natDegree ≤ d + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_mul_le (p := P i j) (q := v j)).trans
    (by have := hP i j; have := hv j; omega)

theorem coefficient_matrix_kernel_zero [Fintype b] [DecidableEq K]
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (v : b × Fin (d + 1) → K) (hv : polynomialCoefficientMatrix P d *ᵥ v = 0) :
    P *ᵥ coefficientVectorPolynomial d v = 0 := by
  funext i
  apply Polynomial.ext
  intro k
  by_cases hk : k < d + 2
  · have h := congrFun hv (i, ⟨k, hk⟩)
    rw [polynomialCoefficientMatrix_mulVec] at h
    exact h
  · change ((P *ᵥ coefficientVectorPolynomial d v) i).coeff k = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (polynomial_mulVec_degree P _ d hP (coefficientVectorPolynomial_degree d v) i)
      (by omega))

theorem bidiagonal_coefficient_matrix_injective [DecidableEq K] (d : ℕ) :
    Function.Injective (polynomialCoefficientMatrix (bidiagonalPencil (K := K) (d + 1)) d).mulVec := by
  change Function.Injective (Matrix.toLin' (polynomialCoefficientMatrix
    (bidiagonalPencil (K := K) (d + 1)) d))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hz := bidiagonalPencil_bounded_kernel_zero d (coefficientVectorPolynomial d v)
    (coefficient_matrix_kernel_zero _ d (bidiagonalPencil_degree _) v hv)
    (coefficientVectorPolynomial_degree d v)
  funext jl
  have h := congrArg (fun p : K[X] => p.coeff jl.2.val) (congrFun hz jl.1)
  simpa [coefficientVectorPolynomial] using h

theorem bidiagonal_coefficient_matrix_surjective (d : ℕ) :
    Function.Surjective (polynomialCoefficientMatrix (bidiagonalPencil (K := K) (d + 1)) d).mulVec := by
  classical
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := Matrix.toLin' (polynomialCoefficientMatrix (bidiagonalPencil (K := K) (d + 1)) d)) ?_).mp
  · exact bidiagonal_coefficient_matrix_injective d
  · simp [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, mul_comm]

def appendColumnMatrix {c : Type*} (P : Matrix a b R) (Q : Matrix a c R) :
    Matrix a (b ⊕ c) R := fun i j => Sum.elim (P i) (Q i) j

theorem coefficient_matrix_surjective_append {c : Type*}
    [Fintype b] [Fintype c] (P : Matrix a b K[X]) (Q : Matrix a c K[X]) (d : ℕ)
    (hs : Function.Surjective (polynomialCoefficientMatrix P d).mulVec) :
    Function.Surjective (polynomialCoefficientMatrix (appendColumnMatrix P Q) d).mulVec := by
  intro y
  obtain ⟨v, hv⟩ := hs y
  refine ⟨fun jl => Sum.elim (fun j => v (j, jl.2)) (fun _ => 0) jl.1, ?_⟩
  rw [← hv]
  funext ik
  simp [polynomialCoefficientMatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fintype.sum_sum_type, appendColumnMatrix]

theorem coefficient_matrix_surjective_reindex {c e : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (P : Matrix a b K[X]) (er : c ≃ a) (ec : e ≃ b) (d : ℕ)
    (hs : Function.Surjective (polynomialCoefficientMatrix P d).mulVec) :
    Function.Surjective (polynomialCoefficientMatrix (P.submatrix er ec) d).mulVec := by
  intro y
  obtain ⟨v, hv⟩ := hs (fun ik => y (er.symm ik.1, ik.2))
  refine ⟨fun jl => v (ec jl.1, jl.2), ?_⟩
  funext ik
  have hh := congrFun hv (er ik.1, ik.2)
  simp only [Equiv.symm_apply_apply] at hh
  rw [← hh]
  simp only [polynomialCoefficientMatrix, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, Fintype.sum_prod_type]
  exact Equiv.sum_comp ec (fun j => ∑ l : Fin (d + 1),
    (P (er ik.1) j * Polynomial.X ^ l.val).coeff ik.2.val * v (j, l))

theorem polynomial_preimage_of_coefficient_surjective [Fintype b]
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hs : Function.Surjective (polynomialCoefficientMatrix P d).mulVec)
    (y : a → K[X]) (hy : ∀ i, (y i).natDegree ≤ d + 1) :
    ∃ v : b → K[X], (∀ j, (v j).natDegree ≤ d) ∧ P *ᵥ v = y := by
  classical
  obtain ⟨c, hc⟩ := hs (fun ik => (y ik.1).coeff ik.2.val)
  refine ⟨coefficientVectorPolynomial d c, coefficientVectorPolynomial_degree d c, ?_⟩
  funext i
  apply Polynomial.ext
  intro k
  by_cases hk : k < d + 2
  · have hh := congrFun hc (i, ⟨k, hk⟩)
    rw [polynomialCoefficientMatrix_mulVec] at hh
    exact hh
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (polynomial_mulVec_degree P _ d hP (coefficientVectorPolynomial_degree d c) i)
        (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hy i) (by omega))]

theorem polynomial_right_inverse_of_coefficient_surjective
    [Fintype a] [Fintype b] [DecidableEq a]
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hs : Function.Surjective (polynomialCoefficientMatrix P d).mulVec) :
    ∃ Q : Matrix b a K[X], DegreeBound Q d ∧ P * Q = 1 := by
  classical
  have ht (i : a) : ∃ v : b → K[X], (∀ j, (v j).natDegree ≤ d) ∧
      P *ᵥ v = Pi.single i 1 := by
    apply polynomial_preimage_of_coefficient_surjective P d hP hs
    intro j
    by_cases h : j = i <;> simp [Pi.single_apply, h, eq_comm]
  choose v hv he using ht
  refine ⟨fun j i => v i j, fun j i => hv i j, ?_⟩
  funext i j
  have hh := congrFun (he j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
    Pi.single_apply, eq_comm] using hh

theorem polynomial_right_inverse_pointwise [Fintype a] [Fintype b]
    [DecidableEq a] (P : Matrix a b K[X]) (Q : Matrix b a K[X]) (hQ : P * Q = 1)
    {F : Type*} [Field F] (φ : K[X] →+* F) :
    Function.Surjective (P.map φ).mulVec := by
  intro y
  refine ⟨Q.map φ *ᵥ y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ]
  simp

end FD56
