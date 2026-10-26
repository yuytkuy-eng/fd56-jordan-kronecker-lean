/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile

/-! Two independent scalar lifts rule out low-degree solutions without a coprimality assumption. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem scalar_cross_eliminates {R V : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup V] [Module R V] [NoZeroSMulDivisors R V]
    (p₀ p₁ f : R) (v₀ v₁ z : V)
    (h₀ : p₀ • z = f • v₀) (h₁ : p₁ • z = f • v₁)
    (hw : p₁ • v₀ - p₀ • v₁ ≠ 0) : z = 0 := by
  have hfW : f • (p₁ • v₀-p₀ • v₁)=0 := by
    calc
      _ = p₁ • (f • v₀)-p₀ • (f • v₁) := by simp [smul_sub,smul_smul,mul_comm]
      _ = p₁ • (p₀ • z)-p₀ • (p₁ • z) := by rw [← h₀,← h₁]
      _ = 0 := by simp [smul_smul,mul_comm]
  have hf : f=0 := (smul_eq_zero.mp hfW).resolve_right hw
  rw [hf,zero_smul] at h₀ h₁
  by_cases hp₀ : p₀=0
  · have hp₁ : p₁≠0 := by intro hp₁; apply hw; simp [hp₀,hp₁]
    exact (smul_eq_zero.mp h₁).resolve_left hp₁
  · exact (smul_eq_zero.mp h₀).resolve_left hp₀

variable {K a b : Type*} [Field K] [Fintype b]

theorem polynomial_kernel_vector_zero_of_hilbert_zero
    (A : Matrix a b K[X]) (d : ℕ)
    (hz : Module.finrank K (polynomialKernelAtDegree A d)=0)
    (v : b → K[X]) (hv : A *ᵥ v=0) (hd : ∀ j, (v j).natDegree ≤ d) : v=0 := by
  let w : polynomialKernelAtDegree A d := ⟨fun j => boundedPolyOf (v j) (hd j),hv⟩
  have hw : w=0 := (finrank_zero_iff_forall_zero.mp hz) w
  funext j
  exact congrArg (fun z : polynomialKernelAtDegree A d => (z.val j).val) hw

theorem polynomial_scalar_lifts_low_degree_zero
    (A : Matrix a b K[X]) (w : a → K[X]) (d : ℕ)
    (Z₀ Z₁ : b → K[X]) (p₀ p₁ : K[X])
    (h₀ : A *ᵥ Z₀ = p₀ • w) (h₁ : A *ᵥ Z₁ = p₁ • w)
    (hZ₀ : ∀ j, (Z₀ j).natDegree ≤ d+1) (hZ₁ : ∀ j, (Z₁ j).natDegree ≤ d+1)
    (hp₀ : p₀.natDegree ≤ d+2) (hp₁ : p₁.natDegree ≤ d+2)
    (hcross : p₁ • Z₀-p₀ • Z₁ ≠ 0)
    (hker : Module.finrank K (polynomialKernelAtDegree A (2*d+2))=0)
    (z : b → K[X]) (f : K[X]) (hz : A *ᵥ z=f • w)
    (hdz : ∀ j, (z j).natDegree ≤ d) (hdf : f.natDegree ≤ d+1) : z=0 := by
  have hc (Z : b → K[X]) (p : K[X])
      (hZ : ∀ j, (Z j).natDegree ≤ d+1) (hp : p.natDegree ≤ d+2)
      (hAZ : A *ᵥ Z=p • w) : p • z=f • Z := by
    apply sub_eq_zero.mp
    apply polynomial_kernel_vector_zero_of_hilbert_zero A (2*d+2) hker
    · simp [Matrix.mulVec_sub,Matrix.mulVec_smul,hz,hAZ,smul_smul,mul_comm]
    · intro j
      change (p*z j-f*Z j).natDegree ≤ 2*d+2
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact Polynomial.natDegree_mul_le.trans (by have := hdz j; omega)
      · exact Polynomial.natDegree_mul_le.trans (by have := hZ j; omega)
  exact scalar_cross_eliminates p₀ p₁ f Z₀ Z₁ z
    (hc Z₀ p₀ hZ₀ hp₀ h₀) (hc Z₁ p₁ hZ₁ hp₁ h₁) hcross

end FD56
