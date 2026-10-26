/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerBlock

/-! Standard regular alternating blocks and a constant congruence for the
rank-two coupling that produces one four-dimensional Jordan block. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

def regularFourChange : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks ![![1,0],![0,0]] ![![0,0],![0,1]]
    ![![0,0],![0,-1]] ![![1,0],![0,0]]

theorem regularFourChange_inverse :
    regularFourChange (R := R) * (regularFourChange (R := R)).transpose = 1 ∧
      (regularFourChange (R := R)).transpose * regularFourChange (R := R) = 1 := by
  constructor <;> ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [regularFourChange, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ, Matrix.one_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]

def rankTwoRegularCoupling (t : R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks ![![0,1],![-1,0]] (t • (1 : Matrix (Fin 2) (Fin 2) R))
    (-(t • (1 : Matrix (Fin 2) (Fin 2) R))) 0

theorem rankTwoRegularCoupling_congruence (t : R) :
    (regularFourChange (R := R)).transpose * rankTwoRegularCoupling t *
      regularFourChange =
    Matrix.fromBlocks 0 ![![t,1],![0,t]]
      (-Matrix.transpose (![![t,1],![0,t]] : Matrix (Fin 2) (Fin 2) R)) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [regularFourChange, rankTwoRegularCoupling, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem regularFourChange_map {S : Type*} [CommRing S] (f : R →+* S) :
    (regularFourChange (R := R)).map f = regularFourChange := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [regularFourChange]

variable {K : Type*} [Field K]

def jordanUpperPencil (a : K) (e : ℕ) : Matrix (Fin e) (Fin e) K[X] :=
  fun i j => (if i = j then X - C a else 0) +
    if i.val + 1 = j.val then 1 else 0

def skewJordanBlockPencil (a : K) (e : ℕ) :
    Matrix (Fin e ⊕ Fin e) (Fin e ⊕ Fin e) K[X] :=
  Matrix.fromBlocks 0 (jordanUpperPencil a e) (-(jordanUpperPencil a e).transpose) 0

theorem rankTwoRegularCoupling_constant_congruence (a : K) :
    ∃ T S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      T * S = 1 ∧ S * T = 1 ∧
      (T.map C).transpose * rankTwoRegularCoupling (X - C a) * T.map C =
        skewJordanBlockPencil a 2 := by
  refine ⟨regularFourChange, (regularFourChange (R := K)).transpose,
    regularFourChange_inverse.1, regularFourChange_inverse.2, ?_⟩
  rw [regularFourChange_map, rankTwoRegularCoupling_congruence]
  have hJ : jordanUpperPencil a 2 = ![![X - C a,1],![0,X - C a]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jordanUpperPencil]
  simp only [skewJordanBlockPencil, hJ]

end FD56
