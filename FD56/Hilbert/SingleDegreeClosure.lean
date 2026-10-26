/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerDimensionBound

/-! Low-degree vanishing forces a single maximal Kronecker block in odd dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem skew_pencil_single_degree_of_kernel_vanishing
    (A B : Matrix n n K) (d : ℕ) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) xs)
    (hne : xs≠[]) (hcard : Fintype.card n=2*d+3)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hzero : Module.finrank K (polynomialKernelAtDegree (affineMatrixPencil A B) d)=0) :
    xs=[d+1] := by
  have hb := skew_pencil_minimal_degrees_dimension_bound A B xs hmin hA hB
  rw [hcard] at hb
  have hz := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d
  rw [hzero] at hz
  have hlo (e : ℕ) (he : e ∈ xs) : d+1≤e := by
    have hh := List.le_sum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩ :
      d+1-e ∈ xs.map (fun a => d+1-a))
    omega
  rcases xs with _ | ⟨a,xs⟩
  · exact (hne rfl).elim
  have ha := hlo a (by simp)
  rcases xs with _ | ⟨b,xs⟩
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hb
    have he : a=d+1 := by omega
    simp [he]
  · have hb' := hlo b (by simp)
    simp only [List.map_cons,List.sum_cons] at hb
    omega

end FD56
