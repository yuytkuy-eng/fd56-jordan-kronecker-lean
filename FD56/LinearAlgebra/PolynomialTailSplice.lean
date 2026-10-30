/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BivariateDiagonalRescaling
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic

/-! An explicit polynomial tail splice. Before diagonal rescaling, the
outer variable is physical and the coefficient variable is the parameter.
After rescaling these roles are exchanged. -/

noncomputable section
namespace FD56
open Polynomial
open scoped BigOperators
set_option Elab.async false

variable {K : Type*} [CommRing K]

def polynomialTailSplice (u U : K[X]) (h : ℕ) : K[X][X] :=
  u.map C * X^h + ∑ j ∈ Finset.range h, monomial j (monomial (h-j) (U.coeff j))

def polynomialTailSpliceQuotient (u U : K[X]) (h : ℕ) : K[X][X] :=
  C (X^h) * bivariateDiagonalRescaling (u.map C) +
    C (∑ j ∈ Finset.range h, monomial j (U.coeff j))

theorem polynomialTailSplice_degree (u U : K[X]) (h a : ℕ) (hu : u.natDegree≤a) :
    (polynomialTailSplice u U h).natDegree≤a+h := by
  unfold polynomialTailSplice
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_mul_le).trans
      (Nat.add_le_add (Polynomial.natDegree_map_le.trans hu)
        (Polynomial.natDegree_X_pow_le (R:=K[X]) h))
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hj; omega)

theorem polynomialTailSplice_parameter_zero (u U : K[X]) (h : ℕ) :
    (polynomialTailSplice u U h).map (Polynomial.evalRingHom (0:K))=X^h*u := by
  have hmap : (u.map C).map (Polynomial.evalRingHom (0:K))=u := by
    ext j
    simp
  have htail : (∑ j ∈ Finset.range h,
      monomial j (monomial (h-j) (U.coeff j)) : K[X][X]).map
        (Polynomial.evalRingHom (0:K))=0 := by
    rw [Polynomial.map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hh : h-j≠0 := by have := Finset.mem_range.mp hj; omega
    simp [hh]
  simp only [polynomialTailSplice,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,hmap,htail,add_zero]
  exact mul_comm _ _

private theorem diagonal_tail_monomial (c : K) (h j : ℕ) (hj : j≤h) :
    bivariateDiagonalRescaling (monomial j (monomial (h-j) c))=
      (X : K[X][X])^h*C (monomial j c) := by
  ext n l
  rw [bivariateDiagonalRescaling_coeff]
  by_cases hn : n=h
  · subst n
    by_cases hl : l=j
    · subst l
      simp [Polynomial.coeff_monomial,hj,Polynomial.coeff_X_pow_mul]
    · simp [Polynomial.coeff_monomial,hl,Ne.symm hl,Polynomial.coeff_X_pow_mul]
  · by_cases hln : l≤n
    · by_cases hl : l=j
      · subst l
        have hd : h-j≠n-j := by omega
        simp [Polynomial.coeff_monomial,hd,Ne.symm hd,hln,hn,Ne.symm hn,
          Polynomial.coeff_X_pow_mul]
      · simp [Polynomial.coeff_monomial,hl,Ne.symm hl,hln,hn,Ne.symm hn,
          Polynomial.coeff_X_pow_mul]
    · simp [hln,hn,Ne.symm hn,Polynomial.coeff_X_pow_mul]

theorem polynomialTailSplice_diagonal_factor (u U : K[X]) (h : ℕ) :
    bivariateDiagonalRescaling (polynomialTailSplice u U h)=
      X^h*polynomialTailSpliceQuotient u U h := by
  have hx : bivariateDiagonalRescaling (X : K[X][X])=C X*X := by
    simp [bivariateDiagonalRescaling]
  simp only [polynomialTailSplice,map_add,map_mul,map_pow,map_sum,hx]
  have ht : (∑ j ∈ Finset.range h,
      bivariateDiagonalRescaling (monomial j (monomial (h-j) (U.coeff j))))=
      X^h*C (∑ j ∈ Finset.range h,monomial j (U.coeff j)) := by
    rw [map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact diagonal_tail_monomial _ h j (Nat.le_of_lt (Finset.mem_range.mp hj))
  rw [ht]
  simp only [polynomialTailSpliceQuotient,mul_pow,←map_pow]
  ring

theorem polynomialTailSpliceQuotient_constant (u U : K[X]) (h : ℕ)
    (hU : U.natDegree≤h) (hmatch : U.coeff h=u.coeff 0) :
    (polynomialTailSpliceQuotient u U h).coeff 0=U := by
  have hconstant : (bivariateDiagonalRescaling (u.map C)).coeff 0=C (u.coeff 0) := by
    ext j
    rw [bivariateDiagonalRescaling_coeff]
    by_cases hj : j=0
    · subst j; simp
    · simp [Polynomial.coeff_C,hj,Ne.symm hj]
  have hsum : U=(∑ j ∈ Finset.range h,monomial j (U.coeff j))+monomial h (U.coeff h) := by
    have he := Polynomial.as_sum_range' U (h+1) (by omega)
    rw [Finset.sum_range_succ] at he
    exact he
  rw [polynomialTailSpliceQuotient,Polynomial.coeff_add,Polynomial.coeff_C_mul,
    hconstant,Polynomial.coeff_C_zero,←hmatch]
  have hm : X^h*C (U.coeff h)=monomial h (U.coeff h) := by
    rw [mul_comm,Polynomial.C_mul_X_pow_eq_monomial]
  rw [hm,add_comm]
  exact hsum.symm

end FD56
