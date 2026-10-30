/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! The substitution f(epsilon,X) to f(epsilon,epsilon*X), with
epsilon as the outer variable, records total-degree initial coefficients. -/

noncomputable section
namespace FD56
open Polynomial

variable {K : Type*} [CommRing K]

def bivariateDiagonalRescaling : K[X][X] →+* K[X][X] :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom Polynomial.C) (Polynomial.C Polynomial.X*Polynomial.X)

theorem bivariateDiagonalRescaling_coeff (p : K[X][X]) (n j : ℕ) :
    ((bivariateDiagonalRescaling p).coeff n).coeff j=
      if j≤n then (p.coeff j).coeff (n-j) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,Polynomial.coeff_add,hp,hq]
    split_ifs <;> simp
  | monomial k a =>
    change ((Polynomial.eval₂ (Polynomial.mapRingHom Polynomial.C)
      (Polynomial.C Polynomial.X*Polynomial.X) (Polynomial.monomial k a)).coeff n).coeff j=_
    simp only [Polynomial.eval₂_monomial,mul_pow,←Polynomial.C_pow]
    rw [←mul_assoc,mul_right_comm]
    simp only [Polynomial.coeff_mul_C,Polynomial.coeff_mul_X_pow',Polynomial.coeff_map,
      Polynomial.coeff_monomial]
    by_cases hkn : k≤n
    · simp only [hkn,if_pos]
      by_cases hjk : j=k
      · subst j
        simp [hkn]
      · by_cases hkj : k≤j
        · have hj : j-k≠0 := by omega
          simp [hjk,Ne.symm hjk,Polynomial.coeff_C_mul,hkj,hj,Polynomial.coeff_C]
        · simp [hjk,Ne.symm hjk,Polynomial.coeff_C_mul,hkj]
    · by_cases hjk : j=k
      · subst j
        simp [hkn]
      · simp [hkn,hjk,Ne.symm hjk]

theorem bivariateDiagonalRescaling_coefficient_degree (p : K[X][X]) (n : ℕ) :
    ((bivariateDiagonalRescaling p).coeff n).natDegree≤n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [bivariateDiagonalRescaling_coeff,if_neg (by omega)]

theorem bivariateDiagonalRescaling_diagonal_coeff (p : K[X][X]) (j : ℕ) :
    ((bivariateDiagonalRescaling p).coeff j).coeff j=(p.coeff j).coeff 0 := by
  simp [bivariateDiagonalRescaling_coeff]

end FD56
