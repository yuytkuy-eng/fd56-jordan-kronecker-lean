/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLClosure

/-! Recovery of three consecutive degrees from one scalar-correction value. -/

noncomputable section
namespace FD56

theorem hasMinimalKernelDegrees_three_of_scalar_correction
    {K x y u v : Type*} [Field K] [Fintype y] [Fintype v]
    [DecidableEq y] [DecidableEq v]
    (F : Matrix x y (Polynomial K)) (G : Matrix u v (Polynomial K))
    (D A B C : ℕ) (hcond : D+2 ≤ B+2*C+1)
    (hG : HasMinimalKernelDegrees G
      (List.replicate A D ++ List.replicate B (D+1) ++ List.replicate C (D+2)))
    (hlow : ∀ d, d < D → Module.finrank K (polynomialKernelAtDegree F d) = 0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree F D) = A+(D+2-C))
    (hhigh : ∀ d, D < d → Module.finrank K (polynomialKernelAtDegree F d) =
      Module.finrank K (polynomialKernelAtDegree G d)+(d+2)) :
    let t := D+2-C
    HasMinimalKernelDegrees F
      (List.replicate (A+t) D ++ List.replicate (B+D+3-2*t) (D+1) ++
        List.replicate (C-(D+2)) (D+2)) := by
  let t := D+2-C
  obtain ⟨hm0,hm1⟩ := scalar_correction_multiplicity_identity B C (D+2) hcond
  change HasMinimalKernelDegrees F
    (List.replicate (A+t) D ++ List.replicate (B+D+3-2*t) (D+1) ++
      List.replicate (C-(D+2)) (D+2))
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  simp only [List.map_append,List.map_replicate,List.sum_append,
    List.sum_replicate,smul_eq_mul]
  by_cases hd : d < D
  · rw [hlow d hd]
    have h0 : d+1-D = 0 := by omega
    have h1 : d+1-(D+1) = 0 := by omega
    have h2 : d+1-(D+2) = 0 := by omega
    simp [h0,h1,h2]
  · by_cases he : d = D
    · subst d
      rw [hcritical]
      have h0 : D+1-D = 1 := by omega
      have h1 : D+1-(D+1) = 0 := by omega
      have h2 : D+1-(D+2) = 0 := by omega
      simp only [h0,h1,h2,mul_one,mul_zero,add_zero]
      rfl
    · rw [hhigh d (by omega),(hasMinimalKernelDegrees_iff_hilbert _ _).mp hG d]
      simp only [List.map_append,List.map_replicate,List.sum_append,
        List.sum_replicate,smul_eq_mul]
      have h0 : d+1-D = d-(D+1)+2 := by omega
      have h1 : d+1-(D+1) = d-(D+1)+1 := by omega
      have h2 : d+1-(D+2) = d-(D+1) := by omega
      have hD : d+2 = d-(D+1)+(D+3) := by omega
      rw [h0,h1,h2,hD]
      have hp : B+(D+2)+1 = B+D+3 := by omega
      rw [hp] at hm0 hm1
      change 2*t+(B+D+3-2*t) = B+D+3 at hm0
      change t+(B+D+3-2*t)+(C-(D+2)) = B+C+1 at hm1
      nlinarith only [hm0,congrArg (fun z => z*(d-(D+1))) hm1]

end FD56
