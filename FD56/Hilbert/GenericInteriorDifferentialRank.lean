/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorScalarFrame
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.Stabilizer.GenericMinorDifferentialImage

/-! The selected interior observability minors have the full derivative-image
dimension forced by the actual generic SL kernel and its degree budget. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

private theorem polynomial_derivation_image_finite
    {K L j : Type*} [Field K] [Field L] [Algebra K L] [Fintype j]
    (p : j → L[X]) : Module.Finite L (LinearMap.range (polynomialDerivationImageMap (K:=K) p)) := by
  let E : (∀ i, BoundedPoly L (p i).natDegree) →ₗ[L] (j → L[X]) :=
    { toFun := fun z i => (z i).val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : LinearMap.range (polynomialDerivationImageMap (K:=K) p) ≤ LinearMap.range E := by
    rintro y ⟨D,rfl⟩
    refine ⟨fun i => boundedPolyOf (polynomialCoefficientDerivation D (p i))
      (polynomialCoefficientDerivation_natDegree_le D (p i)),rfl⟩
  exact Submodule.finiteDimensional_of_le hle

variable (r s : ℕ) [NeZero r] [NeZero s]
variable {K : Type*} [Field K]

def genericInteriorMinorVector (q : ℕ) : Option (Fin r × Fin s) →
    (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))[X] :=
  fun z => (observabilitySelectedMatrix
    (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
    (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s)))
    (interiorLevel r s q) (interiorSelectorRow r s q z)).det

theorem generic_interior_minor_derivation_rank_double_lower (q : ℕ) (hq : 0<q) :
    (r+s)^2*q*(q+1)+2*(r+s)*(q+1)*r+2*(r*s+1) ≤
      2*Module.finrank (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))
        (LinearMap.range (polynomialDerivationImageMap (K:=K)
          (genericInteriorMinorVector (K:=K) r s q))) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)))
  let M := genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s))
  let P := genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s))
  let i₀ : Fin ((r+s)*q+r) := ⟨0,by have := NeZero.pos r; omega⟩
  let A := slEquationMatrix M P i₀
  let A₀ := fun i j => (A i j).coeff 0
  let A₁ := fun i j => (A i j).coeff 1
  let Z := interiorScalarLiftMatrix r s q M P
  let p := genericInteriorMinorVector (K:=K) r s q
  have hr : 0<r := NeZero.pos r
  have hs : 0<s := NeZero.pos s
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin ((r+s)*q+r)) (m:=Fin (r+s)) q hq i₀
    (by simp only [Fintype.card_fin]; nlinarith)
    (by simp only [Fintype.card_fin]; nlinarith)
  simp only [Fintype.card_fin] at hlen hsum
  have hxlen : xs.length=r*s+1 := by
    rw [show (r+s)*q+r-q*(r+s)=r by rw [Nat.mul_comm q (r+s)]; omega,
      show (q+1)*(r+s)-((r+s)*q+r)=s by
        rw [show (q+1)*(r+s)=((r+s)*q+r)+s by ring]
        omega] at hlen
    exact hlen
  have hA : affineMatrixPencil A₀ A₁=A :=
    affineMatrixPencil_coefficients A (slEquationMatrix_degree M P i₀
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _))
  change HasMinimalKernelDegrees A xs at hmin
  rw [← hA] at hmin
  obtain ⟨k,basis,d,hdegree,hlead,hperm⟩ := hmin
  have hk : k=r*s+1 := by
    have hh := hperm.length_eq
    simp only [List.length_ofFn] at hh
    omega
  have hAZ : affineMatrixPencil A₀ A₁*Z=0 := by
    rw [hA]
    exact interiorScalarLiftMatrix_kernel r s q M P i₀
  let φ := algebraMap L[X] (FractionRing L[X])
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hZ : Function.Injective (Z.map φ).mulVec :=
    generic_interior_scalar_lifts_field_injective (K:=K) r s q φ hφ
  have hcard : Fintype.card (Option (Fin r × Fin s))=Fintype.card (Fin k) := by simp [hk]
  have hframe := affineKernelFrame_finrank_range A₀ A₁ basis d hdegree hlead
    Z hAZ φ hφ hcard hZ
  have hds : (∑ j, d j)=xs.sum := by
    simpa only [List.sum_ofFn] using hperm.sum_eq
  have hds2 : (∑ j, (d j+2))=xs.sum+2*(r*s+1) := by
    rw [Finset.sum_add_distrib,hds]
    simp [hk,mul_comm]
  rw [hds2] at hframe
  have hle : LinearMap.range (affineDualPairMap Z) ≤
      LinearMap.range (polynomialDerivationImageMap (K:=K) p) :=
    generic_minor_affine_pairing_range_le (K:=K)
      (fun _ : Option (Fin r × Fin s) => interiorLevel r s q) (interiorSelectorRow r s q)
  letI : Module.Finite L (LinearMap.range (polynomialDerivationImageMap (K:=K) p)) :=
    polynomial_derivation_image_finite p
  have hdim := Submodule.finrank_mono hle
  rw [hframe] at hdim
  change _ ≤ 2*Module.finrank L (LinearMap.range (polynomialDerivationImageMap (K:=K) p))
  rw [hxlen] at hsum
  nlinarith

theorem generic_interior_minor_derivation_rank_lower_of_weight (q : ℕ) (hq : 0<q)
    (S : ℕ) (hS : 2*S=(r+s)*q*(q+1)+2*(q+1)*r) :
    (r+s)*S+r*s+1 ≤
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))
        (LinearMap.range (polynomialDerivationImageMap (K:=K)
          (genericInteriorMinorVector (K:=K) r s q))) := by
  have h := generic_interior_minor_derivation_rank_double_lower (K:=K) r s q hq
  nlinarith

theorem generic_interior_minor_derivation_rank_lower (q : ℕ) (hq : 0<q) :
    (r+s)*((r+s)*q*(q+1)/2+(q+1)*r)+r*s+1 ≤
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))
        (LinearMap.range (polynomialDerivationImageMap (K:=K)
          (genericInteriorMinorVector (K:=K) r s q))) := by
  have h := generic_interior_minor_derivation_rank_double_lower (K:=K) r s q hq
  have hdvd : 2 ∣ (r+s)*q*(q+1) := by
    rw [Nat.mul_assoc]
    exact dvd_mul_of_dvd_right (Nat.even_mul_succ_self q).two_dvd (r+s)
  have hmod := Nat.mod_eq_zero_of_dvd hdvd
  have hdiv := Nat.mod_add_div ((r+s)*q*(q+1)) 2
  nlinarith

end FD56
