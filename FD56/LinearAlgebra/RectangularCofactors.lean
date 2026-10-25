/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.GCDMonoid.Finset

/-! Signed maximal minors generate the left kernel when they satisfy a Bezout identity. -/

namespace FD56
open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] {N : ℕ}

/-- The signed minor obtained by deleting each row of a matrix with one excess row. -/
def rectangularCofactors (A : Matrix (Fin (N + 1)) (Fin N) R) : Fin (N + 1) → R :=
  fun i => (-1) ^ i.val * (A.submatrix i.succAbove id).det

/-- Add a first column to a matrix with one excess row. -/
def cofactorCompletion (A : Matrix (Fin (N + 1)) (Fin N) R)
    (w : Fin (N + 1) → R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i => Fin.cases (w i) (A i)

theorem cofactorCompletion_det (A : Matrix (Fin (N + 1)) (Fin N) R)
    (w : Fin (N + 1) → R) :
    (cofactorCompletion A w).det = ∑ i, w i * rectangularCofactors A i := by
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hsub : (cofactorCompletion A w).submatrix i.succAbove Fin.succ =
      A.submatrix i.succAbove id := rfl
  rw [hsub]
  simp [cofactorCompletion, rectangularCofactors, mul_comm, mul_left_comm, mul_assoc]

theorem rectangularCofactors_relation (A : Matrix (Fin (N + 1)) (Fin N) R) :
    A.transpose *ᵥ rectangularCofactors A = 0 := by
  funext j
  have hz : (cofactorCompletion A (fun i => A i j)).det = 0 :=
    Matrix.det_zero_of_column_eq (Fin.succ_ne_zero j).symm (fun _ => rfl)
  rw [cofactorCompletion_det] at hz
  exact hz

/-- A primitive cofactor vector generates the entire left kernel, including uniqueness. -/
theorem rectangularCofactors_kernel_iff_unique
    (A : Matrix (Fin (N + 1)) (Fin N) R) (w : Fin (N + 1) → R)
    (hw : ∑ i, w i * rectangularCofactors A i = 1) (y : Fin (N + 1) → R) :
    A.transpose *ᵥ y = 0 ↔ ∃! h : R, y = h • rectangularCofactors A := by
  let B := cofactorCompletion A w
  have hdet : IsUnit B.transpose.det := by
    rw [Matrix.det_transpose, cofactorCompletion_det, hw]
    exact isUnit_one
  have hi : Function.Injective B.transpose.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det B.transpose).mpr hdet)
  have hc := rectangularCofactors_relation A
  constructor
  · intro hy
    let h := ∑ i, w i * y i
    have he : y = h • rectangularCofactors A := by
      apply hi
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · change (∑ i, w i * y i) = ∑ i, w i * (h * rectangularCofactors A i)
        simp_rw [mul_left_comm (w _) h]
        rw [← Finset.mul_sum, hw, mul_one]
      · change (A.transpose *ᵥ y) j =
          (A.transpose *ᵥ (h • rectangularCofactors A)) j
        rw [hy, Matrix.mulVec_smul, hc, smul_zero]
    refine ⟨h, he, ?_⟩
    intro k hk
    have hh := congrArg (fun z : Fin (N + 1) → R => ∑ i, w i * z i) hk
    change h = ∑ i, w i * (k * rectangularCofactors A i) at hh
    simp_rw [mul_left_comm (w _) k] at hh
    rw [← Finset.mul_sum, hw, mul_one] at hh
    exact hh.symm
  · rintro ⟨h, rfl, _⟩
    rw [Matrix.mulVec_smul, hc, smul_zero]

/-- In a principal ideal ring, a finite family with only unit common divisors has Bezout weights. -/
theorem bezout_of_common_divisors_are_units [IsPrincipalIdealRing R]
    {ι : Type*} [Fintype ι] (p : ι → R)
    (hp : ∀ d : R, (∀ i, d ∣ p i) → IsUnit d) :
    ∃ w : ι → R, ∑ i, w i * p i = 1 := by
  classical
  let I := Ideal.span (Set.range p)
  let g := Submodule.IsPrincipal.generator I
  have hg : IsUnit g := hp g (fun i =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_range_self i)))
  have htop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I
    (Submodule.IsPrincipal.generator_mem I) hg
  apply Ideal.mem_span_range_iff_exists_fun.mp
  change (1 : R) ∈ I
  rw [htop]
  trivial

theorem rectangularCofactors_kernel_iff_unique_of_common_divisors_units
    [IsPrincipalIdealRing R] (A : Matrix (Fin (N + 1)) (Fin N) R)
    (hp : ∀ d : R, (∀ i, d ∣ rectangularCofactors A i) → IsUnit d)
    (y : Fin (N + 1) → R) :
    A.transpose *ᵥ y = 0 ↔ ∃! h : R, y = h • rectangularCofactors A := by
  obtain ⟨w, hw⟩ := bezout_of_common_divisors_are_units (rectangularCofactors A) hp
  exact rectangularCofactors_kernel_iff_unique A w hw y

theorem rectangularCofactors_kernel_iff_unique_of_unit_gcd
    [IsPrincipalIdealRing R] [IsDomain R] [NormalizedGCDMonoid R]
    (A : Matrix (Fin (N + 1)) (Fin N) R)
    (hg : IsUnit (Finset.univ.gcd (rectangularCofactors A))) (y : Fin (N + 1) → R) :
    A.transpose *ᵥ y = 0 ↔ ∃! h : R, y = h • rectangularCofactors A := by
  apply rectangularCofactors_kernel_iff_unique_of_common_divisors_units A _ y
  intro d hd
  exact isUnit_of_dvd_unit (Finset.dvd_gcd (fun i _ => hd i)) hg

end FD56
