/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.Algebra.Polynomial.Expand

/-! Substitution of a positive power multiplies the first possible kernel
degree. The proof extracts coefficient classes modulo that power. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

private def residueExtract {K : Type*} [Field K] (h r : ℕ) (p : K[X]) : K[X] :=
  (Polynomial.contract h (p*X^(h-r))).divX

private theorem residueExtract_coeff {K : Type*} [Field K]
    (h r : ℕ) (hh : 0<h) (hr : r<h) (p : K[X]) (n : ℕ) :
    (residueExtract h r p).coeff n=p.coeff (n*h+r) := by
  rw [residueExtract,Polynomial.coeff_divX,Polynomial.coeff_contract hh.ne']
  have he : (n+1)*h=(n*h+r)+(h-r) := by nlinarith [Nat.sub_add_cancel hr.le]
  rw [he,Polynomial.coeff_mul_X_pow]

private def residueExtractHom {K : Type*} [Field K] (h r : ℕ)
    (hh : 0<h) (hr : r<h) : K[X] →+ K[X] where
  toFun := residueExtract h r
  map_zero' := by ext n; simp only [residueExtract_coeff h r hh hr,Polynomial.coeff_zero]
  map_add' p q := by ext n; simp only [residueExtract_coeff h r hh hr,Polynomial.coeff_add]

private theorem divX_mul_of_constant_zero {K : Type*} [Field K]
    (p q : K[X]) (hp : p.coeff 0=0) : (p*q).divX=p.divX*q := by
  apply mul_right_cancel₀ (Polynomial.X_ne_zero : (X : K[X])≠0)
  have h₁ : (p*q).divX*X=p*q := by
    simpa only [Polynomial.mul_coeff_zero,hp,zero_mul,Polynomial.C_0,add_zero]
      using Polynomial.divX_mul_X_add (p*q)
  have h₂ : p.divX*X=p := by
    simpa only [hp,Polynomial.C_0,add_zero] using Polynomial.divX_mul_X_add p
  rw [h₁]
  calc
    p*q=(p.divX*X)*q := by rw [h₂]
    _=(p.divX*q)*X := by ring

private theorem residueExtract_expand_mul {K : Type*} [Field K]
    (h r : ℕ) (hh : 0<h) (hr : r<h) (p q : K[X]) :
    residueExtract h r (Polynomial.expand K h p*q)=p*residueExtract h r q := by
  have hc : (Polynomial.contract h (q*X^(h-r))).coeff 0=0 := by
    rw [Polynomial.coeff_contract hh.ne']
    simp only [zero_mul,Polynomial.coeff_mul_X_pow',show ¬h-r≤0 by omega,if_false]
  unfold residueExtract
  rw [show Polynomial.expand K h p*q*X^(h-r)=(q*X^(h-r))*Polynomial.expand K h p by ring,
    Polynomial.contract_mul_expand hh.ne',divX_mul_of_constant_zero _ _ hc,mul_comm]

theorem expanded_matrix_bounded_kernel_zero
    {K a b : Type*} [Field K] [Fintype b]
    (P : Matrix a b K[X]) (d h : ℕ) (hh : 0<h)
    (hzero : ∀ z : b → K[X], P*ᵥz=0 → (∀ j,(z j).natDegree≤d) → z=0)
    (z : b → K[X]) (hz : (P.map (Polynomial.expand K h))*ᵥz=0)
    (hdeg : ∀ j,(z j).natDegree≤h*(d+1)-1) : z=0 := by
  classical
  have hres (r : ℕ) (hr : r<h) : (fun j => residueExtract h r (z j))=0 := by
    apply hzero
    · funext i
      have he := congrArg (residueExtractHom h r hh hr) (congrFun hz i)
      simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,map_sum,Pi.zero_apply,map_zero] at he
      change (∑ j,residueExtract h r (Polynomial.expand K h (P i j)*z j))=0 at he
      simp only [residueExtract_expand_mul h r hh hr] at he
      exact he
    · intro j
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [residueExtract_coeff h r hh hr]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hd := hdeg j
      have hmul : h*(d+1)≤n*h := by nlinarith
      have hpos : 0<h*(d+1) := Nat.mul_pos hh (by omega)
      omega
  funext j
  apply Polynomial.ext
  intro n
  have he := congrArg (fun p : K[X] => p.coeff (n/h))
    (congrFun (hres (n%h) (Nat.mod_lt n hh)) j)
  change (residueExtract h (n%h) (z j)).coeff (n/h)=0 at he
  rw [residueExtract_coeff h (n%h) hh (Nat.mod_lt n hh)] at he
  have hn : n/h*h+n%h=n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n h
  simpa only [hn,Pi.zero_apply,Polynomial.coeff_zero] using he

end FD56
