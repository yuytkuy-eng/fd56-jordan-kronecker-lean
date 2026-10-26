/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Primitive kernel generators and terminal coordinates of split row relations. -/

namespace FD56
open Matrix
open scoped BigOperators

variable {R a b : Type*} [CommRing R] [IsDomain R] [Fintype b]

theorem kernel_generator_common_divisor_isUnit (A : Matrix a b R) (c : b → R)
    (hc : A *ᵥ c = 0)
    (hgen : ∀ y : b → R, A *ᵥ y = 0 ↔ ∃! h : R, y = h • c)
    (d : R) (hd : ∀ i, d ∣ c i) : IsUnit d := by
  obtain ⟨h, hh, hu⟩ := (hgen c).mp hc
  have h1 : (1 : R) = h := hu 1 (one_smul R c).symm
  have hcn : c ≠ 0 := by
    intro hz
    have h0 : (0 : R) = h := hu 0 (by change c = (0 : R) • c; simp [hz])
    exact zero_ne_one (h0.trans h1.symm)
  choose w hw using hd
  have he : c = d • w := by funext i; exact hw i
  have hdn : d ≠ 0 := by
    intro hz
    apply hcn
    rw [he, hz, zero_smul]
  have hwker : A *ᵥ w = 0 := by
    rw [he, Matrix.mulVec_smul] at hc
    funext i
    exact (mul_eq_zero.mp (congrFun hc i)).resolve_left hdn
  obtain ⟨k, hk, _⟩ := (hgen w).mp hwker
  have hdk : d * k = h := hu (d*k) (by
    change c = (d*k) • c
    calc
      c = d • w := he
      _ = d • (k • c) := congrArg (fun z => d • z) hk
      _ = (d*k) • c := (MulAction.mul_smul d k c).symm)
  exact isUnit_of_mul_eq_one d k (hdk.trans h1.symm)

omit [IsDomain R] in
theorem terminal_divisor_controls_split_relation {n : Type*} [Fintype a] [Fintype n]
    [DecidableEq a] (A : Matrix a n R) (B : Matrix b n R)
    (T : Matrix n a R) (hT : A * T = 1) (x : a → R) (y : b → R)
    (hrel : A.transpose *ᵥ x + B.transpose *ᵥ y = 0)
    (d : R) (hd : ∀ j, d ∣ y j) : ∀ i, d ∣ x i := by
  have h := congrArg (fun z => T.transpose *ᵥ z) hrel
  dsimp only at h
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hT,
    Matrix.transpose_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  intro i
  have he : x i = -(T.transpose *ᵥ (B.transpose *ᵥ y)) i :=
    eq_neg_of_add_eq_zero_left (congrFun h i)
  rw [he]
  apply dvd_neg.mpr
  rw [Matrix.mulVec_mulVec]
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right (hd j) _

end FD56
