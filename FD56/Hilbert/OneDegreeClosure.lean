/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerDimensionBound

/-! A degree gap and an odd ambient dimension determine a singleton minimal degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem skew_pencil_one_degree_of_kernel_vanishing
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (d : ℕ) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) xs)
    (hlen : xs.length=1) (hcard : Fintype.card n=2*d+3)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hzero : Module.finrank K (polynomialKernelAtDegree (affineMatrixPencil A B) d)=0) :
    xs=[d+1] := by
  have hb := skew_pencil_minimal_degrees_dimension_bound A B xs hmin hA hB
  rw [hcard] at hb
  have hz := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d
  rw [hzero] at hz
  rcases xs with _ | ⟨a,xs⟩
  · simp at hlen
  have ht : xs=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
  subst xs
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hb hz
  have ha : a=d+1 := by omega
  simp [ha]

end FD56
