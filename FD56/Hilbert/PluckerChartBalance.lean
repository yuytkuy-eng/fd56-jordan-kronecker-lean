/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PluckerChartSpecialization
import FD56.Hilbert.MonomialPluckerChart

/-! The explicit balanced quadric certificate transfers to every coprime
full-degree chart whose coordinates are algebraically independent. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

theorem pluckerChart_balanced_minimal_degrees
    (W : ℕ) (hW : 5≤W) (F : Fin 6 → L[X])
    (hF : ∀ i,(F i).natDegree≤W) (hF0 : F 0≠0) (hFd : (F 0).natDegree=W)
    (hFc : IsCoprime (F 0) (F 1)) (hFq : F 0*F 5-F 1*F 4+F 2*F 3=0)
    (hind : AlgebraicIndependent K (pluckerChartCoordinates W F)) :
    HasMinimalKernelDegrees (fun _ : Unit => F) (balancedDegreeList W 5) := by
  let G := monomialPluckerChart (K:=K) (pluckerGapA W) (pluckerGapB W) (pluckerGapC W)
  obtain ⟨hG,hGd,hGc,hGq,hGmin⟩ := balancedMonomialPluckerChart_certificate (K:=K) W hW
  have hG0 : G 0≠0 := by
    intro hz
    change (G 0).natDegree=W at hGd
    rw [hz,Polynomial.natDegree_zero] at hGd
    omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [balancedDegreeList_hilbert _ _ _ (by decide)]
  apply Nat.le_antisymm
  · have h := pluckerChart_kernel_le_witness W F G hF hG hF0 hFd hFc hG0 hGd hGc hFq hGq hind d
    have hGhilbert := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hGmin d
    rw [balancedDegreeList_hilbert _ _ _ (by decide)] at hGhilbert
    exact h.trans_eq hGhilbert
  · have h := prescribed_matrix_kernel_lower (fun _ : Unit => F) (fun _ => W)
      (fun _ j => hF j) (by simp) d
    simpa using h

theorem pluckerChart_balanced_minimal_degrees_of_derivation_rank
    (W : ℕ) (hW : 5≤W) (F : Fin 6 → L[X])
    (hF : ∀ i,(F i).natDegree≤W) (hF0 : F 0≠0) (hFd : (F 0).natDegree=W)
    (hFc : IsCoprime (F 0) (F 1)) (hFq : F 0*F 5-F 1*F 4+F 2*F 3=0)
    (hrank : 4*(W+1)+1≤Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K) F))) :
    HasMinimalKernelDegrees (fun _ : Unit => F) (balancedDegreeList W 5) :=
  pluckerChart_balanced_minimal_degrees W hW F hF hF0 hFd hFc hFq
    (pluckerChart_coordinates_algebraicIndependent W F hF hF0 hFd hFc hFq hrank)

end FD56
