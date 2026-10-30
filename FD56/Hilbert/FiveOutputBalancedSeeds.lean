/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSixteenTangentWitness
import FD56.Hilbert.BalancedSeventeenTangentWitness
import FD56.Hilbert.BalancedEighteenTangentWitness
import FD56.Hilbert.BalancedTwentyOneTangentWitness
import FD56.Hilbert.BalancedTwentyThreeTangentWitness
import FD56.Hilbert.BalancedTwentyFourTangentWitness
import FD56.Hilbert.BalancedTwentyFiveTangentWitness

/-! Explicit normalized seeds for the seven nondivisible residue weights.
Both required Hilbert bounds follow from integral, kernel-checked minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

private theorem kernel_finrank_zero (P : Matrix (Fin 5) (Fin 10) K[X]) (d : ℕ)
    (hz : ∀ v : Fin 10 → K[X], P*ᵥv=0 → (∀ j, (v j).natDegree≤d) → v=0) :
    Module.finrank K (polynomialKernelAtDegree P d)=0 := by
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z h
  have he := hz (fun i => (z i).val) h (fun i => boundedPoly_degree d (z i))
  funext i
  exact Subtype.ext (congrFun he i)

variable [CharZero K]

theorem exists_five_output_balanced_seed (s : ℕ)
    (hs : s ∈ ([16,17,18,21,23,24,25] : List ℕ)) :
    ∃ (a b : ℕ) (u v : Fin 5 → K[X]),
      (b=a ∨ b=a+1) ∧ a+b=s ∧
      (∀ i, (u i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i) ∧
      (∀ i, (v i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i) ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      Module.finrank K (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u v)) (2*s/7-1))=0 ∧
      Module.finrank K (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u v)) (2*s/7))≤7-(2*s)%7 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨8,8,balancedSixteenTangentU,balancedSixteenTangentV,Or.inl rfl,rfl,
      balancedSixteenTangentU_constant,balancedSixteenTangentV_constant,
      balancedSixteenTangentU_degree,balancedSixteenTangentV_degree,?_,balancedSixteenTangent_kernel_finrank_four_le_three⟩
    exact kernel_finrank_zero _ _ balancedSixteenTangent_bounded_kernel_zero_charZero
  · refine ⟨8,9,balancedSeventeenTangentU,balancedSeventeenTangentV,Or.inr rfl,rfl,
      balancedSeventeenTangentU_constant,balancedSeventeenTangentV_constant,
      balancedSeventeenTangentU_degree,balancedSeventeenTangentV_degree,?_,balancedSeventeenTangent_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ balancedSeventeenTangent_bounded_kernel_zero_charZero
  · refine ⟨9,9,balancedEighteenTangentU,balancedEighteenTangentV,Or.inl rfl,rfl,
      balancedEighteenTangentU_constant,balancedEighteenTangentV_constant,
      balancedEighteenTangentU_degree,balancedEighteenTangentV_degree,?_,balancedEighteenTangent_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ balancedEighteenTangent_bounded_kernel_zero_charZero
  · refine ⟨10,11,balancedTwentyOneTangentU,balancedTwentyOneTangentV,Or.inr rfl,rfl,
      balancedTwentyOneTangentU_constant,balancedTwentyOneTangentV_constant,
      balancedTwentyOneTangentU_degree,balancedTwentyOneTangentV_degree,?_,balancedTwentyOneTangent_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ balancedTwentyOneTangent_bounded_kernel_zero_charZero
  · refine ⟨11,12,balancedTwentyThreeTangentU,balancedTwentyThreeTangentV,Or.inr rfl,rfl,
      balancedTwentyThreeTangentU_constant,balancedTwentyThreeTangentV_constant,
      balancedTwentyThreeTangentU_degree,balancedTwentyThreeTangentV_degree,?_,balancedTwentyThreeTangent_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ balancedTwentyThreeTangent_bounded_kernel_zero_charZero
  · refine ⟨12,12,balancedTwentyFourTangentU,balancedTwentyFourTangentV,Or.inl rfl,rfl,
      balancedTwentyFourTangentU_constant,balancedTwentyFourTangentV_constant,
      balancedTwentyFourTangentU_degree,balancedTwentyFourTangentV_degree,?_,balancedTwentyFourTangent_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ balancedTwentyFourTangent_bounded_kernel_zero_charZero
  · refine ⟨12,13,balancedTwentyFiveTangentU,balancedTwentyFiveTangentV,Or.inr rfl,rfl,
      balancedTwentyFiveTangentU_constant,balancedTwentyFiveTangentV_constant,
      balancedTwentyFiveTangentU_degree,balancedTwentyFiveTangentV_degree,?_,balancedTwentyFiveTangent_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ balancedTwentyFiveTangent_bounded_kernel_zero_charZero

end FD56
