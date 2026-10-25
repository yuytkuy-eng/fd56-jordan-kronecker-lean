/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.BaseChange
import Mathlib.Data.Fintype.Sum

/-! Reconstruction of selected rows of a kernel relation from complementary coordinates. -/

namespace FD56
open Matrix
open scoped BigOperators

theorem kernel_coordinate_reconstruction {R s t m : Type*} [CommRing R]
    [Fintype s] [Fintype t] [DecidableEq s]
    (A : Matrix (s ⊕ t) s R) (P : Matrix m (s ⊕ t) R) (U : Matrix s s R)
    (hPA : P * A = 0) (hU : A.submatrix Sum.inl id * U = 1) :
    P.submatrix id Sum.inl = -(P.submatrix id Sum.inr * A.submatrix Sum.inr id) * U := by
  have hsum : P.submatrix id Sum.inl * A.submatrix Sum.inl id +
      P.submatrix id Sum.inr * A.submatrix Sum.inr id = 0 := by
    ext i j
    have hh := congrArg (fun B => B i j) hPA
    simpa only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.submatrix_apply,
      id_eq, Matrix.add_apply, Matrix.zero_apply] using hh
  have hleft := eq_neg_of_add_eq_zero_left hsum
  calc
    P.submatrix id Sum.inl = P.submatrix id Sum.inl *
        (A.submatrix Sum.inl id * U) := by rw [hU, Matrix.mul_one]
    _ = (P.submatrix id Sum.inl * A.submatrix Sum.inl id) * U := by
      rw [Matrix.mul_assoc]
    _ = _ := by rw [hleft]

theorem kernel_coordinates_mem_subfield {F s t m : Type*} [Field F]
    [Fintype s] [Fintype t] [DecidableEq s]
    (K : Subfield F) (A : Matrix (s ⊕ t) s F) (P : Matrix m (s ⊕ t) F)
    (U : Matrix s s F) (hPA : P * A = 0) (hU : A.submatrix Sum.inl id * U = 1)
    (hA : ∀ i j, A i j ∈ K) (hP : ∀ i j, P i (Sum.inr j) ∈ K) :
    ∀ i j, P i j ∈ K := by
  have hu : ∀ i j, U i j ∈ K :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right (Equiv.refl s) K hU
      (fun i j => hA (Sum.inl i) j)
  have he := kernel_coordinate_reconstruction A P U hPA hU
  intro i j
  cases j with
  | inr j => exact hP i j
  | inl j =>
    have hij := congrArg (fun B => B i j) he
    change P i (Sum.inl j) = _ at hij
    rw [hij]
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.submatrix_apply, id_eq]
    apply K.sum_mem
    intro k _
    apply K.mul_mem _ (hu k j)
    apply K.neg_mem
    apply K.sum_mem
    intro l _
    exact K.mul_mem (hP i l) (hA (Sum.inr l) k)

end FD56
