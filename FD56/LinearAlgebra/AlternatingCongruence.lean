/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Alternation, including characteristic two, is preserved by a matrix congruence. -/

namespace FD56
open Matrix
open scoped BigOperators

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]

theorem matrix_congruence_alternating (A : Matrix n n R) (T : Matrix n m R)
    (hA : ∀ v, v ⬝ᵥ (A *ᵥ v) = 0) (w : m → R) :
    w ⬝ᵥ ((T.transpose * A * T) *ᵥ w) = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  exact hA (T *ᵥ w)

theorem alternating_matrix_diag_zero [DecidableEq n] (A : Matrix n n R)
    (hA : ∀ v, v ⬝ᵥ (A *ᵥ v) = 0) (i : n) : A i i = 0 := by
  simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul] using hA (Pi.single i 1)

theorem alternating_matrix_transpose [DecidableEq n] (A : Matrix n n R)
    (hA : ∀ v, v ⬝ᵥ (A *ᵥ v) = 0) : A.transpose = -A := by
  have hpair (v w : n → R) : v ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ v) = 0 := by
    have h := hA (v+w)
    simpa only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hA,
      zero_add, add_zero, add_assoc, add_comm] using h
  funext i j
  have h := hpair (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul] at h
  change A j i = -A i j
  exact eq_neg_of_add_eq_zero_left ((add_comm (A j i) (A i j)).trans h)

theorem matrix_alternating_of_skew_diag (A : Matrix n n R)
    (hA : A.transpose = -A) (hd : ∀ i, A i i=0) (v : n → R) :
    v ⬝ᵥ (A *ᵥ v)=0 := by
  classical
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun ij : n × n => v ij.1 * (A ij.1 ij.2 * v ij.2))]
  refine Finset.sum_involution (s := Finset.univ)
    (f := fun ij : n × n => v ij.1 * (A ij.1 ij.2 * v ij.2))
    (fun ij _ => ij.swap) ?_ ?_ (fun ij _ => Finset.mem_univ _) ?_
  · rintro ⟨i,j⟩ _
    have h : A j i = -A i j := congrFun (congrFun hA i) j
    dsimp only [Prod.swap]
    rw [h]
    ring
  · rintro ⟨i,j⟩ _ hn he
    have h : j=i := congrArg Prod.fst he
    subst j
    exact hn (by simp [hd])
  · intro ij _
    exact Prod.swap_swap ij

theorem matrix_alternating_map {S : Type*} [CommRing S] [DecidableEq n]
    (φ : R →+* S) (A : Matrix n n R) (hA : ∀ v, v ⬝ᵥ (A *ᵥ v)=0) :
    ∀ v, v ⬝ᵥ (A.map φ *ᵥ v)=0 := by
  apply matrix_alternating_of_skew_diag
  · rw [← Matrix.transpose_map, alternating_matrix_transpose A hA]
    funext i j
    exact map_neg φ (A i j)
  · intro i
    simp [Matrix.map_apply, alternating_matrix_diag_zero A hA i]

end FD56
