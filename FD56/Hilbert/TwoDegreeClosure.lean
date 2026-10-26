/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerDimensionBound

/-! Two minimal degrees are forced by low-degree vanishing and the ambient dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem skew_pencil_two_degrees_of_kernel_vanishing
    (A B : Matrix n n K) (d : ℕ) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) xs)
    (hlen : xs.length=2) (hcard : Fintype.card n=4*d+6)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hzero : Module.finrank K (polynomialKernelAtDegree (affineMatrixPencil A B) d)=0) :
    xs=[d+1,d+1] := by
  have hb := skew_pencil_minimal_degrees_dimension_bound A B xs hmin hA hB
  rw [hcard] at hb
  have hz := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d
  rw [hzero] at hz
  rcases xs with _ | ⟨a,xs⟩
  · simp at hlen
  rcases xs with _ | ⟨b,xs⟩
  · simp at hlen
  have ht : xs=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
  subst xs
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hb hz
  have ha : a=d+1 := by omega
  have hb' : b=d+1 := by omega
  simp [ha,hb']

end FD56
