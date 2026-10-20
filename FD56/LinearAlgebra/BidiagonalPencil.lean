/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The polynomial kernel of a rectangular bidiagonal Kronecker pencil.
Its coordinate recurrence also gives an explicit full-rank specialization. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def bidiagonalPencil (m : ℕ) : Matrix (Fin m) (Fin (m + 1)) K[X] :=
  fun i j => (if j = i.castSucc then Polynomial.X else 0) + (if j = i.succ then 1 else 0)

theorem bidiagonalPencil_degree (m : ℕ) : DegreeBound (bidiagonalPencil (K := K) m) 1 := by
  intro i j
  apply Polynomial.natDegree_add_le_of_degree_le
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem bidiagonalPencil_mulVec (m : ℕ) (v : Fin (m + 1) → K[X]) (i : Fin m) :
    (bidiagonalPencil m *ᵥ v) i = Polynomial.X * v i.castSucc + v i.succ := by
  simp [bidiagonalPencil, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib, ite_mul]

theorem bidiagonalPencil_kernel_coordinates (m : ℕ) (v : Fin (m + 1) → K[X])
    (hv : bidiagonalPencil m *ᵥ v = 0) :
    ∀ j, v j = (-Polynomial.X) ^ j.val * v 0 := by
  intro j
  refine Fin.induction ?_ (fun i ih => ?_) j
  · simp
  · have hh := congrFun hv i
    rw [bidiagonalPencil_mulVec] at hh
    change Polynomial.X * v i.castSucc + v i.succ = 0 at hh
    calc
      v i.succ = -Polynomial.X * v i.castSucc := by linear_combination hh
      _ = (-Polynomial.X) ^ i.succ.val * v 0 := by
        rw [ih]
        change -Polynomial.X * ((-Polynomial.X) ^ i.val * v 0) =
          (-Polynomial.X) ^ (i.val + 1) * v 0
        rw [pow_succ]
        ring

theorem bidiagonalPencil_kernel_iff (m : ℕ) (v : Fin (m + 1) → K[X]) :
    bidiagonalPencil m *ᵥ v = 0 ↔ ∀ j, v j = (-Polynomial.X) ^ j.val * v 0 := by
  constructor
  · exact bidiagonalPencil_kernel_coordinates m v
  · intro h
    funext i
    rw [bidiagonalPencil_mulVec, h i.castSucc, h i.succ]
    change Polynomial.X * ((-Polynomial.X) ^ i.val * v 0) +
      (-Polynomial.X) ^ (i.val + 1) * v 0 = 0
    rw [pow_succ]
    ring

theorem bidiagonalPencil_bounded_kernel_zero (d : ℕ) (v : Fin (d + 2) → K[X])
    (hv : bidiagonalPencil (d + 1) *ᵥ v = 0)
    (hdeg : ∀ j, (v j).natDegree ≤ d) : v = 0 := by
  have hc := bidiagonalPencil_kernel_coordinates (d + 1) v hv
  have hz : v 0 = 0 := by
    by_contra hn
    have hlast := hc (Fin.last (d + 1))
    have hb := hdeg (Fin.last (d + 1))
    rw [hlast] at hb
    change (((-Polynomial.X : K[X]) ^ (d + 1)) * v 0).natDegree ≤ d at hb
    have hp : (-Polynomial.X : K[X]) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by simp)
    rw [Polynomial.natDegree_mul hp hn] at hb
    simp only [Fin.val_last, Polynomial.natDegree_pow, Polynomial.natDegree_neg,
      Polynomial.natDegree_X, one_mul] at hb
    omega
  funext j
  rw [hc j, hz, mul_zero]
  rfl

theorem bidiagonalPencil_degree_iff (m d : ℕ) (v : Fin (m + 1) → K[X])
    (hv : bidiagonalPencil m *ᵥ v = 0) :
    (∀ j, (v j).natDegree ≤ d) ↔
      v 0 = 0 ∨ (m ≤ d ∧ (v 0).natDegree ≤ d - m) := by
  have hc := bidiagonalPencil_kernel_coordinates m v hv
  constructor
  · intro hb
    by_cases hz : v 0 = 0
    · exact Or.inl hz
    · have h := hb (Fin.last m)
      rw [hc (Fin.last m)] at h
      change (((-Polynomial.X : K[X]) ^ m) * v 0).natDegree ≤ d at h
      rw [Polynomial.natDegree_mul (pow_ne_zero _ (by simp)) hz] at h
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_neg, Polynomial.natDegree_X, one_mul] at h
      exact Or.inr ⟨by omega, by omega⟩
  · intro h j
    rw [hc j]
    rcases h with hz | ⟨hm, hb⟩
    · simp [hz]
    · have ht : (((-Polynomial.X : K[X]) ^ j.val) * v 0).natDegree ≤
          j.val + (v 0).natDegree := by
        simpa using (Polynomial.natDegree_mul_le
          (p := (-Polynomial.X : K[X]) ^ j.val) (q := v 0))
      have hj := j.isLt
      omega

theorem bidiagonalPencil_right_inverse (m : ℕ) :
    ∃ Q : Matrix (Fin (m + 1)) (Fin m) K[X], bidiagonalPencil (K := K) m * Q = 1 := by
  let B : Matrix (Fin m) (Fin m) K[X] := fun i j => bidiagonalPencil m i j.succ
  let E : Matrix (Fin (m + 1)) (Fin m) K[X] := fun i j => if i = j.succ then 1 else 0
  have hE : bidiagonalPencil m * E = B := by
    funext i j
    simp [Matrix.mul_apply, E, B]
  have htri : B.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    have h₁ : j.succ ≠ i.castSucc := by
      intro h
      have hh := congrArg Fin.val h
      change j.val + 1 = i.val at hh
      have hlt : i.val < j.val := hij
      omega
    have h₂ : j.succ ≠ i.succ := by
      intro h
      have hh := congrArg Fin.val h
      change j.val + 1 = i.val + 1 at hh
      have hlt : i.val < j.val := hij
      omega
    simp [B, bidiagonalPencil, h₁, h₂, ne_of_gt hij]
  have hd : B.det = 1 := by
    rw [Matrix.det_of_lowerTriangular B htri]
    apply Finset.prod_eq_one
    intro i _
    have h : i.succ ≠ i.castSucc := by
      intro he
      have hh := congrArg Fin.val he
      change i.val + 1 = i.val at hh
      omega
    simp [B, bidiagonalPencil, h]
  refine ⟨E * B⁻¹, ?_⟩
  rw [← Matrix.mul_assoc, hE]
  exact Matrix.mul_nonsing_inv B (hd ▸ isUnit_one)

theorem bidiagonalPencil_transpose_injective (m : ℕ) :
    Function.Injective (bidiagonalPencil (K := K) m).transpose.mulVec := by
  obtain ⟨Q, hQ⟩ := bidiagonalPencil_right_inverse (K := K) m
  have ht : Q.transpose * (bidiagonalPencil (K := K) m).transpose = 1 := by
    rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]
  intro v w h
  have hh := congrArg (fun z => Q.transpose *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ht, Matrix.one_mulVec] using hh

end FD56
