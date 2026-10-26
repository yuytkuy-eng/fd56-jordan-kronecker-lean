/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DistinctPoleHyperplane
import Mathlib.LinearAlgebra.Lagrange

/-! The trace-hyperplane diagonal pencil and its polynomial kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def poleTraceChart (i₀ : n) : Matrix n {j : n // j≠i₀} K :=
  fun i j => (if i=j.val then 1 else 0)-(if i=i₀ then 1 else 0)

def poleTracePencil (lam : n → K) (i₀ : n) : Matrix {j : n // j≠i₀} n K[X] :=
  ((poleTraceChart (K := K) i₀).map C).transpose * regularPoleDiagonal lam

def poleCofactor (lam : n → K) (i : n) : K[X] :=
  ∏ j ∈ Finset.univ.erase i, (X-C (lam j))

theorem poleTraceChart_sum (i₀ : n) (j : {j : n // j≠i₀}) :
    ∑ i, poleTraceChart (K := K) i₀ i j=0 := by
  simp [poleTraceChart,Finset.sum_sub_distrib]

theorem poleTracePencil_entry (lam : n → K) (i₀ : n) (j : {j : n // j≠i₀}) (i : n) :
    poleTracePencil lam i₀ j i =
      (if i=j.val then X-C (lam i) else 0)-(if i=i₀ then X-C (lam i) else 0) := by
  simp only [poleTracePencil,regularPoleDiagonal,Matrix.mul_diagonal,Matrix.transpose_apply,
    Matrix.map_apply,poleTraceChart,map_sub,sub_mul]
  by_cases hij : i=j.val <;> by_cases hi : i=i₀ <;> simp [hij,hi]

theorem poleTracePencil_mulVec (lam : n → K) (i₀ : n) (y : n → K[X])
    (j : {j : n // j≠i₀}) :
    (poleTracePencil lam i₀ *ᵥ y) j =
      (X-C (lam j.val))*y j.val-(X-C (lam i₀))*y i₀ := by
  simp only [Matrix.mulVec,dotProduct,poleTracePencil_entry,sub_mul,Finset.sum_sub_distrib,
    ite_mul,zero_mul]
  simp

theorem poleTracePencil_transpose_mulVec (lam : n → K) (i₀ : n)
    (x : {j : n // j≠i₀} → K[X]) (j : {j : n // j≠i₀}) :
    ((poleTracePencil lam i₀).transpose *ᵥ x) j.val = (X-C (lam j.val))*x j := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,poleTracePencil_entry,j.property,
    if_false,sub_zero]
  have he (i : {j : n // j≠i₀}) : j.val=i.val ↔ j=i := Subtype.val_inj
  simp only [he,ite_mul,zero_mul]
  simp

theorem poleCofactor_identity (lam : n → K) (i : n) :
    (X-C (lam i))*poleCofactor lam i = ∏ j, (X-C (lam j)) := by
  exact Finset.mul_prod_erase Finset.univ (fun j : n => X-C (lam j)) (Finset.mem_univ i)

theorem poleCofactor_degree (lam : n → K) (i : n) :
    (poleCofactor lam i).natDegree=Fintype.card n-1 := by
  simp [poleCofactor,Polynomial.natDegree_prod_of_monic,
    fun j (_ : j ∈ Finset.univ.erase i) => Polynomial.monic_X_sub_C (lam j)]

theorem poleCofactor_ne_zero (lam : n → K) (i : n) : poleCofactor lam i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Polynomial.X_sub_C_ne_zero _

theorem poleTracePencil_cofactor_kernel (lam : n → K) (i₀ : n) :
    poleTracePencil lam i₀ *ᵥ poleCofactor lam = 0 := by
  funext j
  rw [poleTracePencil_mulVec,poleCofactor_identity,poleCofactor_identity,sub_self]
  rfl

theorem poleTracePencil_low_degree_zero (lam : n → K) (hlam : Function.Injective lam)
    (i₀ : n) (y : n → K[X]) (d : ℕ) (hd : d<Fintype.card n-1)
    (hy : ∀ i, (y i).natDegree ≤ d) (hker : poleTracePencil lam i₀ *ᵥ y=0) : y=0 := by
  have hrel (i : n) : (X-C (lam i))*y i=(X-C (lam i₀))*y i₀ := by
    by_cases hi : i=i₀
    · subst i; rfl
    · have h := congrFun hker ⟨i,hi⟩
      rw [poleTracePencil_mulVec] at h
      exact sub_eq_zero.mp h
  funext i
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.univ.erase i) hlam.injOn
  · have hi : (y i).natDegree < (Finset.univ.erase i).card := by simpa using (hy i).trans_lt hd
    exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hi)
  · intro j hj
    have hij : i≠j := Ne.symm (Finset.mem_erase.mp hj).1
    have h := congrArg (Polynomial.eval (lam j)) ((hrel i).trans (hrel j).symm)
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
      sub_self,zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hlam.ne (Ne.symm hij)))

end FD56
