/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.GenericCyclicCoprime
import Mathlib.Data.Fin.Rev
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Coprimality for the literal first and last cyclic determinants. -/

noncomputable section
namespace FD56
open Matrix
variable {R K : Type*} [CommRing R] [Field K] {n : ℕ}

def lastCyclicMatrix (M : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    Matrix (Fin (n+1)) (Fin (n+1)) R := fun i j => (M^i.val) (Fin.last n) j

theorem firstCyclicMatrix_reverse (M : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    firstCyclicMatrix (M.submatrix Fin.rev Fin.rev) =
      (lastCyclicMatrix M).submatrix id Fin.rev := by
  have hp : ∀ k : ℕ, (M.submatrix Fin.rev Fin.rev)^k = (M^k).submatrix Fin.rev Fin.rev := by
    intro k
    induction k with
    | zero => exact (Matrix.submatrix_one_equiv (α := R) Fin.revPerm).symm
    | succ k ih =>
      rw [pow_succ,ih]
      exact Matrix.submatrix_mul_equiv (M^k) M Fin.rev Fin.revPerm Fin.rev
  funext i j
  change ((M.submatrix Fin.rev Fin.rev)^i.val) 0 j = (M^i.val) (Fin.last n) j.rev
  rw [hp]
  simp only [Matrix.submatrix_apply,Fin.rev_zero]

theorem generic_endpoint_cyclic_common_divisor_isUnit
    (p : MvPolynomial (Fin (n+1) × Fin (n+1)) K)
    (hfirst : p ∣ (firstCyclicMatrix (cyclicVariableMatrix id)).det)
    (hlast : p ∣ (lastCyclicMatrix (cyclicVariableMatrix id)).det) : IsUnit p := by
  apply generic_cyclic_common_divisor_isUnit n p hfirst
  change p ∣ (firstCyclicMatrix
    ((cyclicVariableMatrix (K := K) id).submatrix Fin.rev Fin.rev)).det
  rw [firstCyclicMatrix_reverse]
  change p ∣ ((lastCyclicMatrix (cyclicVariableMatrix (K := K) id)).submatrix id Fin.revPerm).det
  rw [Matrix.det_permute']
  exact dvd_mul_of_dvd_right hlast _

theorem generic_endpoint_cyclic_isRelPrime :
    IsRelPrime (firstCyclicMatrix (cyclicVariableMatrix (K := K) (n := n) id)).det
      (lastCyclicMatrix (cyclicVariableMatrix (K := K) (n := n) id)).det :=
  fun _ hf hl => generic_endpoint_cyclic_common_divisor_isUnit _ hf hl

theorem generic_endpoint_cyclic_powers_common_divisor_isUnit (a b : ℕ)
    (p : MvPolynomial (Fin (n+1) × Fin (n+1)) K)
    (hfirst : p ∣ (firstCyclicMatrix (cyclicVariableMatrix id)).det^a)
    (hlast : p ∣ (lastCyclicMatrix (cyclicVariableMatrix id)).det^b) : IsUnit p :=
  (generic_endpoint_cyclic_isRelPrime (K := K) (n := n)).pow hfirst hlast

end FD56
