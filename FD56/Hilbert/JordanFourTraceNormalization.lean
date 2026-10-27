/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NilpotentRankTwoJordan

/-! Normalize a nonzero functional supported on the two nonkernel coordinates
of a four-dimensional Jordan block, while preserving both alternating forms. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def jordanFourSL2Change (p q r s : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks ![![p,0],![0,p]] ![![0,q],![q,0]]
    ![![0,r],![r,0]] ![![s,0],![0,s]]

theorem jordanFourSL2Change_inverse (p q r s : K) (h : p*s-q*r=1) :
    jordanFourSL2Change p q r s * jordanFourSL2Change s (-q) (-r) p=1 ∧
      jordanFourSL2Change s (-q) (-r) p * jordanFourSL2Change p q r s=1 := by
  constructor <;> ext i j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [jordanFourSL2Change,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_succ,Matrix.one_apply] <;> first | ring1 | linear_combination h

theorem jordanFourSL2Change_congruence (a p q r s : K) (h : p*s-q*r=1) :
    ((jordanFourSL2Change p q r s).map C).transpose * skewJordanBlockPencil a 2 *
      (jordanFourSL2Change p q r s).map C=skewJordanBlockPencil a 2 := by
  have hc : C p*C s-C q*C r=(1 : K[X]) := by
    rw [← map_mul,← map_mul,← map_sub,h,map_one]
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [jordanFourSL2Change,skewJordanBlockPencil,jordanUpperPencil,
      Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ] <;>
    first | ring1 | linear_combination hc | linear_combination -hc |
      linear_combination (X-C a)*hc | linear_combination -(X-C a)*hc

theorem jordanFourSL2Change_trace (a b p r : K) (h : a*p+b*r=1)
    (v : Fin 2 ⊕ Fin 2 → K) :
    a*(jordanFourSL2Change p (-b) r a *ᵥ v) (.inl 0)+
      b*(jordanFourSL2Change p (-b) r a *ᵥ v) (.inr 1)=v (.inl 0) := by
  simp [jordanFourSL2Change,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    Fin.sum_univ_succ]
  linear_combination v (.inl 0)*h

theorem jordan_four_trace_normalization (a b lam : K) (h : a≠0 ∨ b≠0) :
    ∃ T S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*skewJordanBlockPencil lam 2*T.map C=skewJordanBlockPencil lam 2 ∧
      ∀ v, a*(T*ᵥv) (.inl 0)+b*(T*ᵥv) (.inr 1)=v (.inl 0) := by
  obtain ⟨p,r,hpr⟩ : ∃ p r : K, a*p+b*r=1 := by
    rcases h with ha | hb
    · exact ⟨a⁻¹,0,by simp [ha]⟩
    · exact ⟨0,b⁻¹,by simp [hb]⟩
  have hd : p*a-(-b)*r=1 := by linear_combination hpr
  exact ⟨jordanFourSL2Change p (-b) r a,jordanFourSL2Change a b (-r) p,
    by simpa using (jordanFourSL2Change_inverse p (-b) r a hd).1,
    by simpa using (jordanFourSL2Change_inverse p (-b) r a hd).2,
    jordanFourSL2Change_congruence lam p (-b) r a hd,
    jordanFourSL2Change_trace a b p r hpr⟩

end FD56
