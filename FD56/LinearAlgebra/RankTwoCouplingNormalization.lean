/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-! Explicit normalization of a nonzero decomposable alternating coupling. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def rankTwoCross (w : n → K) : Matrix (Fin 2) n K := fun i j => if i=0 then w j else 0

def rankTwoTail (w : n → K) : Matrix (Fin 2) n K := fun i j => if i=1 then w j else 0

def rankTwoForm (c : K) (w : n → K) : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K :=
  Matrix.fromBlocks ![![0,c],![-c,0]] (rankTwoCross w) (-(rankTwoCross w).transpose) 0

def rankTwoCoordinateChange (c : K) (w : n → K) : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K :=
  Matrix.fromBlocks ![![1,0],![0,c⁻¹]] (rankTwoTail (fun j => -c⁻¹*w j)) 0 1

def rankTwoCoordinateInverse (c : K) (w : n → K) : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) K :=
  Matrix.fromBlocks ![![1,0],![0,c]] (rankTwoTail w) 0 1

theorem rankTwoCoordinate_inverse (c : K) (hc : c≠0) (w : n → K) :
    rankTwoCoordinateChange c w * rankTwoCoordinateInverse c w = 1 ∧
      rankTwoCoordinateInverse c w * rankTwoCoordinateChange c w = 1 := by
  let D : Matrix (Fin 2) (Fin 2) K := ![![1,0],![0,c⁻¹]]
  let E : Matrix (Fin 2) (Fin 2) K := ![![1,0],![0,c]]
  have hsmall : D*E = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D,E,Matrix.mul_apply,Fin.sum_univ_succ,hc,Matrix.one_apply]
  have hsmall' : E*D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D,E,Matrix.mul_apply,Fin.sum_univ_succ,hc,Matrix.one_apply]
  have htail : D * (rankTwoTail w : Matrix (Fin 2) n K) +
      rankTwoTail (fun j => -c⁻¹*w j) = 0 := by
    ext i j
    fin_cases i <;> simp [D,Matrix.mul_apply,Fin.sum_univ_succ,rankTwoTail]
  have htail' : E * (rankTwoTail (fun j => -c⁻¹*w j) : Matrix (Fin 2) n K) +
      rankTwoTail w = 0 := by
    ext i j
    fin_cases i <;> simp [E,Matrix.mul_apply,Fin.sum_univ_succ,rankTwoTail,hc,← mul_assoc]
  change Matrix.fromBlocks D _ 0 1 * Matrix.fromBlocks E _ 0 1 = 1 ∧
    Matrix.fromBlocks E _ 0 1 * Matrix.fromBlocks D _ 0 1 = 1
  constructor <;>
    simp only [rankTwoCoordinateChange,rankTwoCoordinateInverse,Matrix.fromBlocks_multiply,
      Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.mul_one,Matrix.one_mul,
      hsmall,hsmall',htail,htail',Matrix.fromBlocks_one]

theorem rankTwoCoordinate_congruence (c : K) (hc : c≠0) (w : n → K) :
    (rankTwoCoordinateChange c w).transpose * rankTwoForm c w * rankTwoCoordinateChange c w =
      Matrix.fromBlocks (![![0,1],![-1,0]] : Matrix (Fin 2) (Fin 2) K) 0 0 (0 : Matrix n n K) := by
  let D : Matrix (Fin 2) (Fin 2) K := ![![1,0],![0,c⁻¹]]
  let J : Matrix (Fin 2) (Fin 2) K := ![![0,c],![-c,0]]
  let V := rankTwoCross w
  let T := rankTwoTail (fun j => -c⁻¹*w j)
  have hJV : J*T+V=0 := by
    ext i j
    fin_cases i <;> simp [J,T,V,rankTwoTail,rankTwoCross,Matrix.mul_apply,
      Fin.sum_univ_succ,hc,← mul_assoc]
  have hsmall : D.transpose*J*D = ![![0,1],![-1,0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D,J,Matrix.mul_apply,Fin.sum_univ_succ,hc,← mul_assoc]
  have hleft : T.transpose*J*D - V.transpose*D = 0 := by
    ext i j
    fin_cases j <;>
      simp [D,J,T,V,rankTwoTail,rankTwoCross,Matrix.mul_apply,Fin.sum_univ_succ,hc,
        mul_comm,mul_left_comm,mul_assoc]
  have hVT : V.transpose*T = 0 := by
    ext i j
    simp [V,T,rankTwoTail,rankTwoCross,Matrix.mul_apply,Fin.sum_univ_succ]
  change (Matrix.fromBlocks D T 0 1).transpose * Matrix.fromBlocks J V (-V.transpose) 0 *
    Matrix.fromBlocks D T 0 1 = _
  rw [Matrix.mul_assoc, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, hJV, Matrix.neg_mul, hVT, neg_zero]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, add_zero, zero_add, ← Matrix.mul_assoc, hsmall,
    ← sub_eq_add_neg, hleft]

end FD56
