/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddle

/-! Explicit GL degree lists for auxiliary degrees two and three. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_two_gl_minimal_degrees_le {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))))
      (List.replicate (u*(v-u)) 5 ++ List.replicate (2*u^2+v^2) 6 ++
        List.replicate (v*(2*u+v)) 7) := by
  let r := u+v
  have hr : 0 < r := by dsimp [r]; omega
  have hvlt : v < r := by dsimp [r]; omega
  have hdiff : 3*r+v-(2*r+v) = r := by omega
  have hcount : 2*r+v-r = r+v := by omega
  have hda : (2*r+v)/r = 2 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hma : (2*r+v)%r = v := by
    rw [Nat.mod_eq_sub_mul_div,hda]
    omega
  have halpha : balancedDegreeList (2*r+v) r =
      List.replicate v 3 ++ List.replicate u 2 := by
    have hh : r-v = u := by dsimp [r]; omega
    simp [balancedDegreeList,hda,hma,hh]
  have hbeta : balancedDegreeList (2*r+v+2*r) (r+v) =
      List.replicate (2*u+v) 3 ++ List.replicate (v-u) 2 := by
    by_cases he : u = v
    · subst u
      have hdb : (2*r+v+2*r)/(r+v) = 3 := by
        dsimp [r]
        apply Nat.div_eq_of_lt_le <;> omega
      have hmb : (2*r+v+2*r)%(r+v) = 0 := by
        rw [Nat.mod_eq_sub_mul_div,hdb]
        dsimp [r]
        omega
      simp [balancedDegreeList,hdb,hmb,r]
      omega
    · have hdb : (2*r+v+2*r)/(r+v) = 2 := by
        dsimp [r]
        apply Nat.div_eq_of_lt_le <;> omega
      have hmb : (2*r+v+2*r)%(r+v) = 2*u+v := by
        rw [Nat.mod_eq_sub_mul_div,hdb]
        dsimp [r]
        omega
      have hh : r+v-(2*u+v) = v-u := by dsimp [r]; omega
      simp [balancedDegreeList,hdb,hmb,hh]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (3*r+v)) (m := Fin (2*r+v))
    (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin,hdiff,hcount,halpha,hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution,List.map_flatMap,nat_sum_flatMap,
    List.map_append,List.map_replicate,List.map_map,List.sum_append,
    List.sum_replicate,smul_eq_mul,Function.comp_apply]
  norm_num
  have hs := Nat.sub_add_cancel huv
  have he : v*(v-u)+u*(2*u+v) = 2*u^2+v^2 := by
    nlinarith only [congrArg (fun z => v*z) hs]
  nlinarith only [congrArg (fun z => z*(d+1-6)) he]

theorem generic_mixed_two_gl_minimal_degrees_gt {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hvu : v < u) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))))
      (List.replicate (3*u*v) 6 ++ List.replicate (u*(u-v)+3*v^2) 7 ++
        List.replicate (v*(u-v)) 8) := by
  let r := u+v
  have hr : 0 < r := by dsimp [r]; omega
  have hvlt : v < r := by dsimp [r]; omega
  have hdiff : 3*r+v-(2*r+v) = r := by omega
  have hcount : 2*r+v-r = r+v := by omega
  have hda : (2*r+v)/r = 2 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hma : (2*r+v)%r = v := by
    rw [Nat.mod_eq_sub_mul_div,hda]
    omega
  have halpha : balancedDegreeList (2*r+v) r =
      List.replicate v 3 ++ List.replicate u 2 := by
    have hh : r-v = u := by dsimp [r]; omega
    simp [balancedDegreeList,hda,hma,hh]
  have hdb : (2*r+v+2*r)/(r+v) = 3 := by
    dsimp [r]
    apply Nat.div_eq_of_lt_le <;> omega
  have hmb : (2*r+v+2*r)%(r+v) = u-v := by
    rw [Nat.mod_eq_sub_mul_div,hdb]
    dsimp [r]
    omega
  have hbeta : balancedDegreeList (2*r+v+2*r) (r+v) =
      List.replicate (u-v) 4 ++ List.replicate (3*v) 3 := by
    have hh : r+v-(u-v) = 3*v := by dsimp [r]; omega
    simp [balancedDegreeList,hdb,hmb,hh]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (3*r+v)) (m := Fin (2*r+v))
    (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin,hdiff,hcount,halpha,hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution,List.map_flatMap,nat_sum_flatMap,
    List.map_append,List.map_replicate,List.map_map,List.sum_append,
    List.sum_replicate,smul_eq_mul,Function.comp_apply]
  norm_num
  ring

end FD56
