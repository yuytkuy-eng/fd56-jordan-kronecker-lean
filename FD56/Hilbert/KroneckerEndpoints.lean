/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGLKronecker
import FD56.LinearAlgebra.PolynomialCongruenceSpecialization
import FD56.Stabilizer.KirillovParameterMap

/-! A positive Kronecker degree forces the two endpoint matrices to be independent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem kronecker_decomposition_endpoints_independent
    (H : Matrix n n K[X]) (xs : List ℕ)
    (h : HasKroneckerDecomposition H xs) (hpos : 0<xs.sum) :
    LinearIndependent K ![(fun i j => (H i j).coeff 0),
      (fun i j => (H i j).coeff 1)] := by
  classical
  obtain ⟨r,d,hp,T,S,hTS,hST,hform⟩ := h
  have hd : ∃ j, 0<d j := by
    by_contra! hn
    have hzero : (List.ofFn d).sum=0 := by
      rw [List.sum_ofFn]
      apply Finset.sum_eq_zero
      intro j _
      exact Nat.eq_zero_of_le_zero (hn j)
    have he := hp.sum_eq
    omega
  obtain ⟨j,hj⟩ := hd
  let i : Fin (d j) := ⟨0,hj⟩
  let B := Matrix.blockDiagonal' (fun k : Fin r => kroneckerBlockPencil (K:=K) (d k))
  have hc (k : ℕ) :
      T.transpose*(show Matrix n n K from fun a b => (H a b).coeff k)*T=
        (fun a b => (B a b).coeff k) := by
    calc
      _ = (fun a b => (((T.map C).transpose*H*T.map C) a b).coeff k) :=
        (polynomial_constant_congruence_coefficients H T k).symm
      _ = _ := by rw [hform]
  have hneq : i.castSucc≠i.succ := by
    intro he
    have := congrArg Fin.val he
    simp at this
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    have he := hc 1
    change (fun a b => (H a b).coeff 1)=0 at hz
    rw [hz] at he
    change T.transpose*0*T=(fun a b => (B a b).coeff 1) at he
    rw [Matrix.mul_zero,Matrix.zero_mul] at he
    have hh := congrFun (congrFun he ⟨j,Sum.inl i⟩) ⟨j,Sum.inr i.castSucc⟩
    simpa [B,kroneckerBlockPencil,bidiagonalPencil,hneq] using hh
  · intro c he
    change c•(fun a b => (H a b).coeff 1)=(fun a b => (H a b).coeff 0) at he
    have ht := congrArg (fun A : Matrix n n K => T.transpose*A*T) he
    dsimp only at ht
    rw [Matrix.mul_smul,Matrix.smul_mul,hc 1,hc 0] at ht
    have hh := congrFun (congrFun ht ⟨j,Sum.inl i⟩) ⟨j,Sum.inr i.succ⟩
    norm_num [B,kroneckerBlockPencil,bidiagonalPencil,Ne.symm hneq,Polynomial.coeff_one] at hh

theorem affine_pair_endpoints_independent_of_positive_kronecker
    {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (xs : List ℕ)
    (h : HasKroneckerDecomposition (glKirillovMatrix M P) xs) (hpos : 0<xs.sum) :
    LinearIndependent K ![((fun i j => (M i j).coeff 0),(fun i j => (P i j).coeff 0)),
      ((fun i j => (M i j).coeff 1),(fun i j => (P i j).coeff 1))] :=
  affine_pair_endpoints_independent_of_kirillov M P
    (kronecker_decomposition_endpoints_independent _ xs h hpos)

end FD56
