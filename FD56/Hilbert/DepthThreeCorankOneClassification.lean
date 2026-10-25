/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeCorankOne
import FD56.Hilbert.DepthThreeGL

/-! The complete generic GL minimal-degree list in the third-depth corank-one family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- At `n = 4m - 1`, the first auxiliary degrees are shifted by `10m - 1`. -/
theorem generic_corank_one_depth_three_gl_minimal_degrees
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m))
      ((balancedDegreeList (6 * Fintype.card m) (Fintype.card m - 1)).map
        (fun a => a + (10 * Fintype.card m - 1))) := by
  have hmn : 3 * Fintype.card m < Fintype.card n := by omega
  have hshape : Fintype.card n - 3 * Fintype.card m = Fintype.card m - 1 := by omega
  obtain ⟨r, Bv, a, hV, hVL, hperm⟩ :=
    generic_depth_three_alpha_minimal_degrees (K := K) hmn
  have hr : r = Fintype.card n - 3 * Fintype.card m := by
    simpa only [List.length_ofFn, balancedDegreeList_length (6 * Fintype.card m)
      (Fintype.card n - 3 * Fintype.card m) (by omega)] using hperm.length_eq
  subst r
  obtain ⟨s, Bt, b, hT, hTL, hpermT⟩ :=
    generic_corank_one_depth_three_beta_degrees hm hn Bv
  have hs : s = 1 := by simpa using hpermT.length_eq
  subst s
  have hb (i : Fin 1) : b i = 10 * Fintype.card m - 4 := by
    have hi := hpermT.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simpa using hi
  have hshift : 10 * Fintype.card m - 4 + 3 = 10 * Fintype.card m - 1 := by omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases hmn (by omega)
    Bv Bt a b hV hT hVL hTL d]
  simp only [Fintype.sum_prod_type, hb, Nat.add_assoc, hshift,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  have hh := (hperm.map (fun e => d + 1 - (e + (10 * Fintype.card m - 1)))).sum_eq
  have hlist := congrArg (balancedDegreeList (6 * Fintype.card m)) hshape
  rw [hlist] at hh
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, List.map_map,
    Function.comp_def] using hh

end FD56
