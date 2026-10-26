/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile
import FD56.LinearAlgebra.ClearDenominators
import FD56.LinearAlgebra.RankSpecialization

/-! The number of polynomial minimal kernel degrees equals rational nullity. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K F a b k : Type*} [Field K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]
  [Fintype a] [Fintype b] [Fintype k]
  [DecidableEq a] [DecidableEq b] [DecidableEq k]

omit [Fintype a] [DecidableEq a] in
theorem polynomialKernelBasisMatrix_fraction_range (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    LinearMap.range (Matrix.toLin' ((polynomialKernelBasisMatrix A B).map (algebraMap K[X] F))) =
      LinearMap.ker (Matrix.toLin' (A.map (algebraMap K[X] F))) := by
  let φ := algebraMap K[X] F
  let Z := polynomialKernelBasisMatrix A B
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.toLin'_mul,← Matrix.map_mul,polynomialKernelBasisMatrix_mul]
    simp
  · intro v hv
    obtain ⟨d,w,hd,hw,he⟩ := kernel_clear_denominators (F := F) A v hv
    let w' : LinearMap.ker (Matrix.toLin' A) := ⟨w,hw⟩
    let c := B.equivFun w'
    have hc : Z *ᵥ c = w := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (B.equivFun.symm_apply_apply w')
    have hmap : Z.map φ *ᵥ (fun j => φ (c j)) = φ d • v := by
      funext i
      have hh := RingHom.map_mulVec φ Z c i
      change φ ((Z *ᵥ c) i) = (Z.map φ *ᵥ (fun j => φ (c j))) i at hh
      rw [hc] at hh
      exact hh.symm.trans (he i)
    refine ⟨(φ d)⁻¹ • (fun j => φ (c j)),?_⟩
    change Z.map φ *ᵥ ((φ d)⁻¹ • (fun j => φ (c j))) = v
    rw [Matrix.mulVec_smul,hmap,smul_smul,inv_mul_cancel₀,one_smul]
    simpa only [map_zero] using (IsFractionRing.injective K[X] F).ne hd

omit [Fintype a] [DecidableEq a] in
theorem polynomial_kernel_basis_fraction_finrank (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map (algebraMap K[X] F)))) = Fintype.card k := by
  have hinj : Function.Injective
      ((polynomialKernelBasisMatrix A B).map (algebraMap K[X] F)).mulVec :=
    matrix_injective_of_specialization Polynomial.C (Polynomial.evalRingHom 0)
      (fun c => by simp) (algebraMap K[X] F) (IsFractionRing.injective K[X] F) _
      (polynomialKernelBasisMatrix_pointwise_injective A B 0)
  have hdim := (Matrix.toLin' ((polynomialKernelBasisMatrix A B).map
    (algebraMap K[X] F))).finrank_range_add_finrank_ker
  have hker : LinearMap.ker (Matrix.toLin' ((polynomialKernelBasisMatrix A B).map (algebraMap K[X] F))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  rw [hker,finrank_bot,add_zero,polynomialKernelBasisMatrix_fraction_range,
    Module.finrank_fintype_fun_eq_card] at hdim
  exact hdim

omit [Fintype a] [DecidableEq a] in
theorem HasMinimalKernelDegrees.length_eq_fraction_nullity
    (A : Matrix a b K[X]) (xs : List ℕ) (h : HasMinimalKernelDegrees A xs) :
    xs.length = Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map (algebraMap K[X] F)))) := by
  obtain ⟨r,B,e,_,_,he⟩ := h
  rw [polynomial_kernel_basis_fraction_finrank A B,Fintype.card_fin]
  have hh := he.length_eq
  simpa only [List.length_ofFn] using hh.symm

end FD56
