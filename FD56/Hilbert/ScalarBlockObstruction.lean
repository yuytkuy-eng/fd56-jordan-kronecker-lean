/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialLeading
import Mathlib.Data.Matrix.Block

/-! Repeating a polynomial matrix in diagonal blocks preserves its column
degree bounds, reduced leading matrix, and bounded scalar obstruction. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R S K a b : Type*}

/-- Equal diagonal blocks, with the block index first in each product type. -/
def repeatedBlockMatrix (ι : Type*) [DecidableEq ι] [Zero R]
    (G : Matrix a b R) : Matrix (ι × a) (ι × b) R :=
  (Matrix.blockDiagonal (fun _ : ι => G)).submatrix Prod.swap Prod.swap

theorem repeatedBlockMatrix_apply (ι : Type*) [DecidableEq ι] [Zero R]
    (G : Matrix a b R) (i : ι × a) (j : ι × b) :
    repeatedBlockMatrix ι G i j = if i.1 = j.1 then G i.2 j.2 else 0 := rfl

theorem repeatedBlockMatrix_map (ι : Type*) [DecidableEq ι] [Zero R] [Zero S]
    (G : Matrix a b R) (f : R → S) (hf : f 0 = 0) :
    (repeatedBlockMatrix ι G).map f = repeatedBlockMatrix ι (G.map f) := by
  funext x j
  by_cases h : x.1 = j.1 <;>
    simp [Matrix.map_apply, repeatedBlockMatrix_apply, h, hf]

theorem repeatedBlockMatrix_transpose (ι : Type*) [DecidableEq ι] [Zero R]
    (G : Matrix a b R) :
    (repeatedBlockMatrix ι G).transpose = repeatedBlockMatrix ι G.transpose := by
  funext x j
  simp [Matrix.transpose_apply, repeatedBlockMatrix_apply, eq_comm]

theorem repeatedBlockMatrix_mulVec (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Semiring R] [Fintype b] (G : Matrix a b R) (v : ι × b → R) (i : ι) (x : a) :
    (repeatedBlockMatrix ι G *ᵥ v) (i, x) = (G *ᵥ fun y => v (i, y)) x := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, repeatedBlockMatrix_apply]

theorem repeatedBlockMatrix_mulVec_injective (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Semiring R] [Fintype b] (G : Matrix a b R)
    (hG : Function.Injective G.mulVec) :
    Function.Injective (repeatedBlockMatrix ι G).mulVec := by
  intro v w h
  funext ⟨i, j⟩
  apply congrFun (hG ?_) j
  funext x
  simpa only [repeatedBlockMatrix_mulVec] using congrFun h (i, x)

theorem repeatedBlockMatrix_pointwise_injective (ι : Type*)
    [Fintype ι] [DecidableEq ι] [Field K] [Fintype b]
    (G : Matrix a b K[X])
    (hG : ∀ x : K, Function.Injective (G.map (Polynomial.evalRingHom x)).mulVec)
    (x : K) :
    Function.Injective
      ((repeatedBlockMatrix ι G).map (Polynomial.evalRingHom x)).mulVec := by
  rw [repeatedBlockMatrix_map ι G (Polynomial.evalRingHom x) (map_zero _)]
  exact repeatedBlockMatrix_mulVec_injective ι _ (hG x)

theorem mul_repeatedBlockMatrix_diagonal (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Semiring R] [Fintype a] (G : Matrix a b R)
    (E : Matrix (ι × b) (ι × a) R) (i : ι) :
    (E * repeatedBlockMatrix ι G).submatrix (fun x => (i, x)) (fun y => (i, y)) =
      E.submatrix (fun x => (i, x)) (fun y => (i, y)) * G := by
  funext x y
  simp [Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    repeatedBlockMatrix_apply]

theorem repeatedBlockMatrix_column_degree (ι : Type*) [DecidableEq ι] [Field K]
    (G : Matrix a b K[X]) (e : b → ℕ)
    (hG : ∀ x j, (G x j).natDegree ≤ e j) :
    ∀ x j, (repeatedBlockMatrix ι G x j).natDegree ≤ e j.2 := by
  intro x j
  by_cases h : x.1 = j.1
  · simpa only [repeatedBlockMatrix_apply, if_pos h] using hG x.2 j.2
  · simp [repeatedBlockMatrix_apply, h]

theorem repeatedBlockMatrix_degree (ι : Type*) [DecidableEq ι] [Field K]
    (G : Matrix a b K[X]) (d : ℕ) (hG : DegreeBound G d) :
    DegreeBound (repeatedBlockMatrix ι G) d :=
  repeatedBlockMatrix_column_degree ι G (fun _ => d) hG

theorem repeatedBlockMatrix_leading (ι : Type*) [DecidableEq ι] [Field K]
    (G : Matrix a b K[X]) (e : b → ℕ) :
    (fun x j => (repeatedBlockMatrix ι G x j).coeff (e j.2)) =
      repeatedBlockMatrix ι (fun x j => (G x j).coeff (e j)) := by
  funext x j
  by_cases h : x.1 = j.1 <;> simp [repeatedBlockMatrix_apply, h]

theorem repeatedBlockMatrix_leading_injective (ι : Type*)
    [Fintype ι] [DecidableEq ι] [Field K] [Fintype b]
    (G : Matrix a b K[X]) (e : b → ℕ)
    (hG : Function.Injective (Matrix.mulVec (fun x j => (G x j).coeff (e j)))) :
    Function.Injective (Matrix.mulVec
      (fun x j => (repeatedBlockMatrix ι G x j).coeff (e j.2))) := by
  rw [repeatedBlockMatrix_leading]
  exact repeatedBlockMatrix_mulVec_injective ι _ hG

/-- A scalar identity in repeated blocks restricts to the same scalar identity
in any one diagonal block. The multiplying matrix need not be block diagonal. -/
theorem repeatedBlockMatrix_scalar_obstruction (ι : Type*)
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Field K] [Fintype a] [DecidableEq b]
    (G : Matrix a b K[X]) (e : b → ℕ)
    (hG : ∀ (E : Matrix b a K[X]) (c : K[X]),
      (∀ i j, (E i j).natDegree ≤ e i) →
      E * G = (-c) • (1 : Matrix b b K[X]) → c = 0)
    (E : Matrix (ι × b) (ι × a) K[X]) (c : K[X])
    (hE : ∀ i j, (E i j).natDegree ≤ e i.2)
    (hEG : E * repeatedBlockMatrix ι G = (-c) • (1 : Matrix (ι × b) (ι × b) K[X])) :
    c = 0 := by
  let i : ι := Classical.choice inferInstance
  apply hG (E.submatrix (fun x => (i, x)) (fun y => (i, y))) c
  · intro x y
    exact hE (i, x) (i, y)
  · have h := congrArg
      (fun A : Matrix (ι × b) (ι × b) K[X] =>
        A.submatrix (fun x => (i, x)) (fun y => (i, y))) hEG
    dsimp only at h
    rw [mul_repeatedBlockMatrix_diagonal] at h
    funext x y
    by_cases hxy : x = y <;>
      simpa [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply, hxy] using
        congrFun (congrFun h x) y

end FD56
