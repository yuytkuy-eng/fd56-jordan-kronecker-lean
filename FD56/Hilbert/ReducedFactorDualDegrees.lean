/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ReducedFactorDegrees
import FD56.LinearAlgebra.PolynomialKernelFrameGeneration
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.Hilbert.MinimalDegreeMixedFrame

/-! A reduced factorization and an exact kernel-generation statement identify
complementary minimal degrees once their total degree is sharp. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

private theorem kernel_generators_injective_of_basis
    {K a s j : Type*} [Field K] [Fintype s] [DecidableEq s]
    [Fintype j] [DecidableEq j] (A : Matrix a s K[X])
    (B : Basis j K[X] (LinearMap.ker (Matrix.toLin' A))) (Z : Matrix s j K[X])
    (hgen : LinearMap.range (Matrix.toLin' Z)=LinearMap.ker (Matrix.toLin' A)) :
    Function.Injective Z.mulVec := by
  have hBinj : Function.Injective (polynomialKernelBasisMatrix A B).mulVec := by
    intro u v huv
    apply B.equivFun.symm.injective
    apply Subtype.ext
    simpa only [polynomialKernelBasisMatrix_mulVec] using huv
  have hAZ : A*Z=0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,map_zero]
    exact LinearMap.range_le_ker_iff.mp (le_of_eq hgen)
  obtain ⟨T,hVT⟩ := polynomialKernelFrame_factor A B Z hAZ
  have hsurj : Function.Surjective T.mulVec := by
    intro c
    have hmem : polynomialKernelBasisMatrix A B *ᵥ c ∈
        LinearMap.ker (Matrix.toLin' A) := by
      change A *ᵥ (polynomialKernelBasisMatrix A B *ᵥ c)=0
      rw [Matrix.mulVec_mulVec,polynomialKernelBasisMatrix_mul,Matrix.zero_mulVec]
    rw [← hgen] at hmem
    obtain ⟨v,hv⟩ := hmem
    refine ⟨v,?_⟩
    apply hBinj
    simpa only [Matrix.mulVec_mulVec,hVT] using hv
  obtain ⟨R,hTR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  have hRT : R*T=1 := Matrix.mul_eq_one_comm.mp hTR
  have hTinj : Function.Injective T.mulVec := by
    intro u v huv
    have h := congrArg R.mulVec huv
    simpa only [Matrix.mulVec_mulVec,hRT,Matrix.one_mulVec] using h
  intro u v huv
  apply hTinj
  apply hBinj
  simpa only [Matrix.mulVec_mulVec,hVT] using huv

theorem reduced_factor_dual_minimal_degrees
    {K a n s : Type*} [Field K] [Fintype s] [DecidableEq s]
    {r : ℕ} (V : Matrix n (Fin r) K[X]) (C : Matrix (Fin r) s K[X])
    (e : Fin r → ℕ) (D : ℕ)
    (hV : ∀ i j, (V i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff (e j))))
    (hVC : DegreeBound (V*C) D)
    (A : Matrix a s K[X])
    (hgen : LinearMap.range (Matrix.toLin' C.transpose)=LinearMap.ker (Matrix.toLin' A))
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs)
    (hlen : xs.length=r) (hbudget : xs.sum+(∑ i, e i)=r*D) :
    HasMinimalKernelDegrees A (List.ofFn (fun i => D-e i)) := by
  have hC : Function.Injective C.transpose.mulVec := by
    obtain ⟨k,B,_,_,_,hperm⟩ := hmin
    have hk : k=r := by simpa only [List.length_ofFn,hlen] using hperm.length_eq
    subst k
    exact kernel_generators_injective_of_basis A B C.transpose hgen
  obtain ⟨he,hdegree⟩ := reduced_factor_degree_bounds V C e D hV hlead hC hVC
  have hsum : xs.sum=∑ i, (D-e i) := by
    rw [Finset.sum_tsub_distrib _ (fun i _ => he i)]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  obtain ⟨B,hB⟩ := polynomial_kernel_frame_basis A C.transpose hC hgen
  have hAZ : A*C.transpose=0 := by
    rw [← hB]
    exact polynomialKernelBasisMatrix_mul A B
  exact minimal_degrees_of_full_mixed_frame_at_point A xs hmin r (fun i => D-e i)
    C.transpose hlen hsum hAZ (fun i j => hdegree j i) 0
    (polynomial_kernel_frame_pointwise_injective A C.transpose hC hgen 0)

end FD56
