/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedScalarWitness

/-! Four scalar parameters for one column of each adjacent degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

def mixedTwoSingleScalarWitness : Matrix (MixedScalarRows 2 (Fin 1) (Fin 1))
    (Fin 1 ⊕ Fin 1) K[X]
  | Sum.inl x, Sum.inl _ => X^(4*x.1.val)
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr x, Sum.inl _ => if x.1=2 then X^2 else 0
  | Sum.inr x, Sum.inr _ => X^(if x.1=2 then 5 else 2*x.1.val)

theorem mixedTwoSingleScalarWitness_degree (x : MixedScalarRows 2 (Fin 1) (Fin 1))
    (j : Fin 1 ⊕ Fin 1) :
    (mixedTwoSingleScalarWitness (K := K) x j).natDegree ≤ 4+mixedColumnShift j := by
  cases x with
  | inl x =>
    cases j <;> simp only [mixedTwoSingleScalarWitness,mixedColumnShift]
    · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
    · simp
  | inr x =>
    cases j
    · simp only [mixedTwoSingleScalarWitness,mixedColumnShift]
      split_ifs <;> simp
    · simp only [mixedTwoSingleScalarWitness,mixedColumnShift]
      split_ifs
      · simp
      · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)

theorem mixedTwoSingleScalarWitness_eval_zero_injective :
    Function.Injective ((mixedTwoSingleScalarWitness (K := K)).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v huv
  have hn : (0 : Fin 3) ≠ 2 := by decide
  funext j
  cases j with
  | inl j =>
    fin_cases j
    simpa [mixedTwoSingleScalarWitness,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Fin.sum_univ_succ] using congrFun huv (Sum.inl ((0 : Fin 2),(0 : Fin 1)))
  | inr j =>
    fin_cases j
    simpa [mixedTwoSingleScalarWitness,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Fin.sum_univ_succ,hn] using congrFun huv (Sum.inr ((0 : Fin 3),(0 : Fin 1)))

theorem mixedTwoSingleScalarWitness_injective :
    Function.Injective (mixedTwoSingleScalarWitness (K := K)).mulVec := by
  apply polynomial_matrix_injective_of_zero
  exact mixedTwoSingleScalarWitness_eval_zero_injective

private theorem mixedTwoSingleScalarWitness_mul_left
    (E : Matrix (Fin 1) (MixedScalarRows 2 (Fin 1) (Fin 1)) K[X]) :
    (E*mixedTwoSingleScalarWitness (K := K)) 0 (Sum.inl 0) =
      E 0 (Sum.inl (0,0)) + E 0 (Sum.inl (1,0))*X^4 + E 0 (Sum.inr (2,0))*X^2 := by
  have hn02 : (0 : Fin 3) ≠ 2 := by decide
  have hn12 : (1 : Fin 3) ≠ 2 := by decide
  simp [mixedTwoSingleScalarWitness,Matrix.mul_apply,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,hn02,hn12,add_assoc]

private theorem mixedTwoSingleScalarWitness_mul_right
    (E : Matrix (Fin 1) (MixedScalarRows 2 (Fin 1) (Fin 1)) K[X]) :
    (E*mixedTwoSingleScalarWitness (K := K)) 0 (Sum.inr 0) =
      E 0 (Sum.inr (0,0)) + E 0 (Sum.inr (1,0))*X^2 + E 0 (Sum.inr (2,0))*X^5 := by
  have hn02 : (0 : Fin 3) ≠ 2 := by decide
  have hn12 : (1 : Fin 3) ≠ 2 := by decide
  simp [mixedTwoSingleScalarWitness,Matrix.mul_apply,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fin.sum_univ_succ,hn02,hn12,add_assoc]

theorem mixedTwoSingleScalarWitness_scalar_obstruction
    (E : Matrix (Fin 1) (MixedScalarRows 2 (Fin 1) (Fin 1)) K[X]) (c : K[X])
    (hE : DegreeBound E 1)
    (hrel : E*mixedTwoSingleScalarWitness = (-c) •
      (fun i j => if Sum.inr i=j then 1 else 0 : Matrix (Fin 1) (Fin 1 ⊕ Fin 1) K[X]))
    (htail : ∀ k : Fin 4, c.coeff k.val=0) : E=0 ∧ c=0 := by
  have hcE (x : MixedScalarRows 2 (Fin 1) (Fin 1)) (k : ℕ) (hk : 1<k) :
      (E 0 x).coeff k=0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE 0 x) hk)
  have hleft : E 0 (Sum.inl (0,0)) + E 0 (Sum.inl (1,0))*X^4 + E 0 (Sum.inr (2,0))*X^2=0 := by
    have h := congrArg (fun A : Matrix (Fin 1) (Fin 1 ⊕ Fin 1) K[X] => A 0 (Sum.inl 0)) hrel
    have hh : (E*mixedTwoSingleScalarWitness (K := K)) 0 (Sum.inl 0)=0 := by simpa using h
    rw [mixedTwoSingleScalarWitness_mul_left E] at hh
    exact hh
  have hright : E 0 (Sum.inr (0,0)) + E 0 (Sum.inr (1,0))*X^2 + E 0 (Sum.inr (2,0))*X^5 = -c := by
    have h := congrArg (fun A : Matrix (Fin 1) (Fin 1 ⊕ Fin 1) K[X] => A 0 (Sum.inr 0)) hrel
    have hh : (E*mixedTwoSingleScalarWitness (K := K)) 0 (Sum.inr 0)=-c := by simpa using h
    rw [mixedTwoSingleScalarWitness_mul_right E] at hh
    exact hh
  have h20 : (E 0 (Sum.inr (2,0))).coeff 0=0 := by
    simpa [coeff_add,coeff_mul_X_pow',hcE] using congrArg (fun p : K[X] => p.coeff 2) hleft
  have h21 : (E 0 (Sum.inr (2,0))).coeff 1=0 := by
    simpa [coeff_add,coeff_mul_X_pow',hcE] using congrArg (fun p : K[X] => p.coeff 3) hleft
  have h2 : E 0 (Sum.inr (2,0))=0 := by
    rw [eq_X_add_C_of_natDegree_le_one (hE 0 _),h20,h21]
    simp
  have hc : c=0 := by
    ext k
    by_cases hk : k<4
    · exact htail ⟨k,hk⟩
    · have h := congrArg (fun p : K[X] => p.coeff k) hright
      have hk0 : 1<k := by omega
      have hk2 : 1<k-2 := by omega
      simpa [coeff_add,coeff_mul_X_pow',h2,hcE _ _ hk0,hcE _ _ hk2] using h.symm
  have hr (l : Fin 2) (q : Fin 2) :
      (E 0 (Sum.inr (l.castSucc,0))).coeff q.val=0 := by
    have h := congrArg (fun p : K[X] => p.coeff (2*l.val+q.val)) hright
    fin_cases l <;> fin_cases q <;> simpa [coeff_add,coeff_mul_X_pow',hc,h2,hcE] using h
  have hl (l : Fin 2) (q : Fin 2) : (E 0 (Sum.inl (l,0))).coeff q.val=0 := by
    have h := congrArg (fun p : K[X] => p.coeff (4*l.val+q.val)) hleft
    fin_cases l <;> fin_cases q <;> simpa [coeff_add,coeff_mul_X_pow',h2,hcE] using h
  refine ⟨?_,hc⟩
  funext i x
  fin_cases i
  cases x with
  | inl x =>
    rcases x with ⟨l,j⟩
    fin_cases j
    change E 0 (Sum.inl (l,0))=0
    rw [eq_X_add_C_of_natDegree_le_one (hE 0 _)]
    have h0 := hl l 0
    have h1 := hl l 1
    simp only [Fin.val_zero] at h0
    simp only [Fin.val_one] at h1
    simp [h0,h1]
  | inr x =>
    rcases x with ⟨l,j⟩
    fin_cases j
    fin_cases l
    · change E 0 (Sum.inr (0,0))=0
      rw [eq_X_add_C_of_natDegree_le_one (hE 0 _)]
      have h0 : (E 0 (Sum.inr (0,0))).coeff 0=0 := hr 0 0
      have h1 : (E 0 (Sum.inr (0,0))).coeff 1=0 := hr 0 1
      rw [h1,h0]
      simp
    · change E 0 (Sum.inr (1,0))=0
      rw [eq_X_add_C_of_natDegree_le_one (hE 0 _)]
      have h0 : (E 0 (Sum.inr (1,0))).coeff 0=0 := hr 1 0
      have h1 : (E 0 (Sum.inr (1,0))).coeff 1=0 := hr 1 1
      simp [h0,h1]
    · exact h2

end FD56
