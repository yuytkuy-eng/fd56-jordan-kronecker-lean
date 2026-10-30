/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedWitness
import FD56.Hilbert.SixOutputTenSeedWitness

/-! Two explicit normalized seeds supply the finite Hilbert tests for the
six-output weights not divisible by six. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

private theorem kernel_finrank_zero (P : Matrix (Fin 15) (Fin 15) K[X]) (d : ℕ)
    (hz : ∀ v : Fin 15 → K[X], P*ᵥv=0 → (∀ j, (v j).natDegree≤d) → v=0) :
    Module.finrank K (polynomialKernelAtDegree P d)=0 := by
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z h
  have he := hz (fun i => (z i).val) h (fun i => boundedPoly_degree d (z i))
  funext i
  exact Subtype.ext (congrFun he i)

variable [CharZero K]

theorem exists_six_output_balanced_seed (s : ℕ)
    (hs : s ∈ ([8,10] : List ℕ)) :
    ∃ (a b : ℕ) (u v : Fin 6 → K[X]),
      (b=a ∨ b=a+1) ∧ a+b=s ∧
      (∀ i, (u i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i) ∧
      (∀ i, (v i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i) ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u v)) (3*s/9-1))=0 ∧
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u v)) (3*s/9))≤9-(3*s)%9 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl
  · refine ⟨4,4,sixOutputEightSeedU,sixOutputEightSeedV,Or.inl rfl,rfl,
      sixOutputEightSeedU_constant,sixOutputEightSeedV_constant,
      sixOutputEightSeedU_degree,sixOutputEightSeedV_degree,?_,
      sixOutputEightSeed_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ sixOutputEightSeed_bounded_kernel_zero_charZero
  · refine ⟨5,5,sixOutputTenSeedU,sixOutputTenSeedV,Or.inl rfl,rfl,
      sixOutputTenSeedU_constant,sixOutputTenSeedV_constant,
      sixOutputTenSeedU_degree,sixOutputTenSeedV_degree,?_,
      sixOutputTenSeed_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ sixOutputTenSeed_bounded_kernel_zero_charZero

end FD56
