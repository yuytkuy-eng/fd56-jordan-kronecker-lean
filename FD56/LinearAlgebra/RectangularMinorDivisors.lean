/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RectangularCofactors
import Mathlib.Data.Fintype.EquivFin

/-! Row-deletion cofactors and all maximal minors have the same common divisors. -/

namespace FD56
open Matrix

variable {R : Type*} [CommRing R] {N : ℕ}

theorem dvd_rectangularCofactor_iff (A : Matrix (Fin (N + 1)) (Fin N) R)
    (d : R) (i : Fin (N + 1)) :
    d ∣ rectangularCofactors A i ↔ d ∣ (A.submatrix i.succAbove id).det := by
  exact (isUnit_neg_one.pow i.val).dvd_mul_left

theorem rectangular_maximal_minors_dvd_of_row_minors
    (A : Matrix (Fin (N + 1)) (Fin N) R) (d : R)
    (hd : ∀ i : Fin (N + 1), d ∣ (A.submatrix i.succAbove id).det) :
    ∀ r : Fin N → Fin (N + 1), d ∣ (A.submatrix r id).det := by
  classical
  intro r
  by_cases hr : Function.Injective r
  · have hns : ¬ Function.Surjective r := by
      intro hs
      have hc := Fintype.card_le_of_surjective r hs
      simp only [Fintype.card_fin] at hc
      exact Nat.not_succ_le_self N hc
    have hmiss : ∃ i : Fin (N + 1), ∀ j, r j ≠ i := by
      simpa only [Function.Surjective, not_forall, not_exists] using hns
    obtain ⟨i, hi⟩ := hmiss
    choose f hf using fun j => Fin.exists_succAbove_eq (hi j)
    have hfi : Function.Injective f := by
      intro j k hjk
      apply hr
      rw [← hf j, ← hf k, hjk]
    let e : Equiv.Perm (Fin N) := Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, rfl⟩)
    have he : A.submatrix r id = (A.submatrix i.succAbove id).submatrix e id := by
      ext j k
      change A (r j) k = A (i.succAbove (f j)) k
      rw [hf]
    rw [he, Matrix.det_permute]
    exact dvd_mul_of_dvd_right (hd i) _
  · have he : (A.submatrix r id).det = 0 := by
      obtain ⟨i, j, hrij, hij⟩ := Function.not_injective_iff.mp hr
      apply Matrix.det_zero_of_row_eq hij
      funext k
      change A (r i) k = A (r j) k
      rw [hrij]
    rw [he]
    exact dvd_zero d

theorem rectangularCofactors_common_divisors_iff
    (A : Matrix (Fin (N + 1)) (Fin N) R) (d : R) :
    (∀ i, d ∣ rectangularCofactors A i) ↔
      ∀ r : Fin N → Fin (N + 1), d ∣ (A.submatrix r id).det := by
  constructor
  · intro hd
    exact rectangular_maximal_minors_dvd_of_row_minors A d
      (fun i => (dvd_rectangularCofactor_iff A d i).mp (hd i))
  · intro hd i
    exact (dvd_rectangularCofactor_iff A d i).mpr (hd i.succAbove)

/-- Primitivity of all maximal minors supplies the unique polynomial cofactor generator. -/
theorem rectangularCofactors_kernel_iff_unique_of_maximal_minors_units
    [IsPrincipalIdealRing R] (A : Matrix (Fin (N + 1)) (Fin N) R)
    (hp : ∀ d : R,
      (∀ r : Fin N → Fin (N + 1), d ∣ (A.submatrix r id).det) → IsUnit d)
    (y : Fin (N + 1) → R) :
    A.transpose *ᵥ y = 0 ↔ ∃! h : R, y = h • rectangularCofactors A := by
  apply rectangularCofactors_kernel_iff_unique_of_common_divisors_units A _ y
  intro d hd
  exact hp d ((rectangularCofactors_common_divisors_iff A d).mp hd)

end FD56
