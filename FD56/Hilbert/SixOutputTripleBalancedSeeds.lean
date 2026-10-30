/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedWitness
import FD56.Hilbert.SixOutputThreeColumnFourSeedWitness
import FD56.Hilbert.SixOutputTripleSpliceNormalization

/-! The two normalized finite seeds supply the Hilbert tests in the
nondivisible column-degree classes of the six-output middle remainder. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

private theorem kernel_finrank_zero (P : Matrix (Fin 20) (Fin 20) K[X]) (d : ℕ)
    (hz : ∀ z : Fin 20 → K[X], P*ᵥz=0 → (∀ j, (z j).natDegree≤d) → z=0) :
    Module.finrank K (polynomialKernelAtDegree P d)=0 := by
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z h
  have he := hz (fun i => (z i).val) h (fun i => boundedPoly_degree d (z i))
  funext i
  exact Subtype.ext (congrFun he i)

variable [CharZero K]

theorem exists_six_output_triple_balanced_seed (a : ℕ) (ha : a∈([1,4] : List ℕ)) :
    ∃ G : Matrix (Fin 6) (Fin 3) K[X],
      (∀ i j, (G i j).coeff 0=sixOutputTripleBaseFrame K i j) ∧
      (∀ i j, (G i j).natDegree≤a) ∧
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) (12*a/10-1))=0 ∧
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) (12*a/10))≤10-(12*a)%10 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  · refine ⟨sixOutputThreeColumnOneSeedFrame,
      sixOutputThreeColumnOneSeedFrame_constant,sixOutputThreeColumnOneSeedFrame_degree,?_,
      sixOutputThreeColumnOneSeed_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ sixOutputThreeColumnOneSeed_bounded_kernel_zero_charZero
  · refine ⟨sixOutputThreeColumnFourSeedFrame,
      sixOutputThreeColumnFourSeedFrame_constant,sixOutputThreeColumnFourSeedFrame_degree,?_,
      sixOutputThreeColumnFourSeed_kernel_finrank_critical_le⟩
    exact kernel_finrank_zero _ _ sixOutputThreeColumnFourSeed_bounded_kernel_zero_charZero

end FD56
