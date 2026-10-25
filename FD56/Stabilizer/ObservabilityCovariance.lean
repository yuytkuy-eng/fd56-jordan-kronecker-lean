/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityMatrix
import Mathlib.Algebra.Group.Semiconj.Units
import FD56.LinearAlgebra.MaximalMinorDivisors
import FD56.LinearAlgebra.FiniteGCDCovariance

/-! State-coordinate changes and maximal minors of observability stacks. -/

noncomputable section
namespace FD56
open Matrix
variable {R n m : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem observabilityMatrix_state_change (M : Matrix n n R) (P : Matrix m n R)
    (S : (Matrix n n R)ˣ) (q : ℕ) :
    observabilityMatrix ((((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) : Matrix n n R) * M * (S : Matrix n n R)) (P * (S : Matrix n n R)) q =
      observabilityMatrix M P q * (S : Matrix n n R) := by
  ext i j
  change ((P * (S : Matrix n n R)) * ((((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) : Matrix n n R) * M * (S : Matrix n n R))^i.1.val) i.2 j = _
  rw [S.conj_pow']
  have hh : (P * (S : Matrix n n R)) * ((((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) : Matrix n n R) * M^i.1.val * (S : Matrix n n R)) =
      (P * M^i.1.val) * (S : Matrix n n R) := by
    calc
      _ = (P * (((S : Matrix n n R) : Matrix n n R) * ((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R))) * M^i.1.val * (S : Matrix n n R) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp
  rw [hh]
  rfl

theorem observabilityMatrix_state_change_minor (M : Matrix n n R) (P : Matrix m n R)
    (S : (Matrix n n R)ˣ) (q : ℕ) (r : n → Fin q × m) :
    ((observabilityMatrix ((((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) : Matrix n n R) * M * (S : Matrix n n R)) (P * (S : Matrix n n R)) q).submatrix r id).det =
      ((observabilityMatrix M P q).submatrix r id).det * ((S : Matrix n n R) : Matrix n n R).det := by
  rw [observabilityMatrix_state_change]
  have he : (observabilityMatrix M P q * (S : Matrix n n R)).submatrix r id =
      (observabilityMatrix M P q).submatrix r id * (S : Matrix n n R) := by
    ext i j
    rfl
  rw [he, Matrix.det_mul]

theorem observabilityMatrix_state_change_minor_dvd (M : Matrix n n R) (P : Matrix m n R)
    (S : (Matrix n n R)ˣ) (q : ℕ) (r : n → Fin q × m) (d : R) :
    d ∣ ((observabilityMatrix (((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) * M * (S : Matrix n n R))
      (P * (S : Matrix n n R)) q).submatrix r id).det ↔
      d ∣ ((observabilityMatrix M P q).submatrix r id).det := by
  rw [observabilityMatrix_state_change_minor]
  exact (S.isUnit.map Matrix.detMonoidHom).dvd_mul_right

def observabilityOutputAction [DecidableEq m] (q : ℕ) (T : Matrix m m R) :
    Matrix (Fin q × m) (Fin q × m) R :=
  fun i j => if i.1 = j.1 then T i.2 j.2 else 0

theorem observabilityMatrix_output_change [Fintype m] [DecidableEq m]
    (M : Matrix n n R) (P : Matrix m n R) (T : Matrix m m R) (q : ℕ) :
    observabilityMatrix M (T * P) q = observabilityOutputAction q T * observabilityMatrix M P q := by
  ext i j
  change ((T * P) * M^i.1.val) i.2 j = _
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, observabilityOutputAction, observabilityMatrix,
    Fintype.sum_prod_type]

theorem observabilityOutputAction_mul [Fintype m] [DecidableEq m]
    (q : ℕ) (T U : Matrix m m R) :
    observabilityOutputAction q (T * U) =
      observabilityOutputAction q T * observabilityOutputAction q U := by
  ext i j
  by_cases h : i.1 = j.1
  · simp [Matrix.mul_apply, observabilityOutputAction, Fintype.sum_prod_type, h]
  · simp [Matrix.mul_apply, observabilityOutputAction, Fintype.sum_prod_type, h]

theorem observabilityOutputAction_one [DecidableEq m] (q : ℕ) :
    observabilityOutputAction q (1 : Matrix m m R) = 1 := by
  ext i j
  simp [observabilityOutputAction, Matrix.one_apply, Prod.ext_iff, ite_and]

theorem observabilityMatrix_output_change_minor_divisors [Fintype m] [DecidableEq m]
    (M : Matrix n n R) (P : Matrix m n R) (T U : Matrix m m R)
    (hUT : U * T = 1) (q : ℕ) (d : R) :
    (∀ r : n → Fin q × m, d ∣ ((observabilityMatrix M (T * P) q).submatrix r id).det) ↔
      (∀ r : n → Fin q × m, d ∣ ((observabilityMatrix M P q).submatrix r id).det) := by
  rw [observabilityMatrix_output_change]
  apply maximal_minor_common_divisor_mul_left_iff _ _ (observabilityOutputAction q U)
  rw [← observabilityOutputAction_mul, hUT, observabilityOutputAction_one]

def observabilityMinorGCD [Fintype m] [IsDomain R] [NormalizedGCDMonoid R]
    (M : Matrix n n R) (P : Matrix m n R) (q : ℕ) : R :=
  Finset.univ.gcd (fun r : n → Fin q × m => ((observabilityMatrix M P q).submatrix r id).det)

theorem observabilityMinorGCD_state_change [Fintype m] [IsDomain R] [NormalizedGCDMonoid R]
    (M : Matrix n n R) (P : Matrix m n R) (S : (Matrix n n R)ˣ) (q : ℕ) :
    Associated (observabilityMinorGCD
      (((S⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) * M * (S : Matrix n n R))
      (P * (S : Matrix n n R)) q) (observabilityMinorGCD M P q) := by
  apply finite_gcd_associated_of_common_divisors
  intro d
  exact forall_congr' (fun r => observabilityMatrix_state_change_minor_dvd M P S q r d)

theorem observabilityMinorGCD_output_change [Fintype m] [DecidableEq m]
    [IsDomain R] [NormalizedGCDMonoid R] (M : Matrix n n R) (P : Matrix m n R)
    (T U : Matrix m m R) (hUT : U * T = 1) (q : ℕ) :
    Associated (observabilityMinorGCD M (T * P) q) (observabilityMinorGCD M P q) := by
  apply finite_gcd_associated_of_common_divisors
  intro d
  exact observabilityMatrix_output_change_minor_divisors M P T U hUT q d

end FD56
