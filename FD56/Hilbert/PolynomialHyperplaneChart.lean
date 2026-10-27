/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Coefficients
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Constant hyperplane charts preserve polynomial kernel vectors and their degree bounds. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n r : Type*} [Field K] [Fintype n] [Fintype r]

omit [Fintype r] in
theorem constant_mulVec_coefficient (A : Matrix r n K) (v : n → K[X]) (d : ℕ) (i : r) :
    ((A.map C *ᵥ v) i).coeff d=(A *ᵥ (fun j => (v j).coeff d)) i := by
  simp only [Matrix.mulVec,dotProduct,Polynomial.finset_sum_coeff,
    Matrix.map_apply,Polynomial.coeff_C_mul]

theorem polynomial_hyperplane_chart_recovery (E : Matrix n r K) (F : Matrix r n K)
    (c : n → K) (hEF : ∀ v, c ⬝ᵥ v=0 → E *ᵥ (F *ᵥ v)=v)
    (v : n → K[X]) (hv : (fun i => C (c i)) ⬝ᵥ v=0) :
    E.map C *ᵥ (F.map C *ᵥ v)=v := by
  funext i
  apply Polynomial.ext
  intro d
  have hc : c ⬝ᵥ (fun j => (v j).coeff d)=0 := by
    have h := congrArg (fun p : K[X] => p.coeff d) hv
    simpa only [dotProduct,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul,
      Polynomial.coeff_zero] using h
  have h := congrFun (hEF _ hc) i
  simpa only [constant_mulVec_coefficient] using h

theorem polynomial_hyperplane_chart_kernel (H : Matrix n n K[X])
    (E : Matrix n r K) (F : Matrix r n K) (c : n → K)
    (hE : E.transpose *ᵥ c=0)
    (hEF : ∀ v, c ⬝ᵥ v=0 → E *ᵥ (F *ᵥ v)=v)
    (v : n → K[X]) (p : K[X])
    (hv : (fun i => C (c i)) ⬝ᵥ v=0)
    (hH : H *ᵥ v=fun i => p*C (c i)) :
    ((E.map C).transpose*H*E.map C) *ᵥ (F.map C *ᵥ v)=0 := by
  rw [← Matrix.mulVec_mulVec,polynomial_hyperplane_chart_recovery E F c hEF v hv,
    ← Matrix.mulVec_mulVec,hH]
  funext i
  have hc := congrFun hE i
  change ∑ j, C (E j i)*(p*C (c j))=0
  calc
    _ = p*C (∑ j, E j i*c j) := by
      simp only [map_sum,map_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by change p*C ((E.transpose *ᵥ c) i)=0; simp only [hc,Pi.zero_apply,map_zero,mul_zero]

theorem constant_mulVec_degree (A : Matrix r n K) (v : n → K[X]) (d : ℕ)
    (hv : ∀ i, (v i).natDegree≤d) (i : r) :
    ((A.map C *ᵥ v) i).natDegree≤d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [constant_mulVec_coefficient]
  have hz : (fun j => (v j).coeff k)=0 := by
    funext j
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hv j).trans_lt hk)
  rw [hz,Matrix.mulVec_zero]
  rfl

end FD56
