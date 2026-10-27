/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveTwoSLNullity
import FD56.Hilbert.DivisibleGL

/-! Full GL injectivity and singleton SL nullity for one-output generic pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K F : Type*} [Field K] [Field F]

theorem generic_affine_gl_nullity_from_observability {n m : Type}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (q ρ : ℕ) (hsize : Fintype.card n = (q+1)*Fintype.card m + ρ)
    (hρ : 0 < ρ) (hρm : ρ ≤ Fintype.card m)
    (ψ : (AffineCoefficientField K (MatrixParameters n m))[X] →+* F)
    (hψ : Function.Injective ψ) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' ((glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)).map ψ))) =
        ρ*(Fintype.card m-ρ) := by
  let M := (genericAffineSquare K n m).map ψ
  let P := (genericAffineRows K n m).map ψ
  have hw : (q+1)*Fintype.card m < Fintype.card n := by omega
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K := K) (q+1) hw
  have hR' : observabilityMatrix M P (q+1) * R.map ψ = 1 := by
    have hh := congrArg (fun A => A.map ψ) hR
    simpa only [Matrix.map_mul,observabilityMatrix_map,Matrix.map_one,map_zero,map_one] using hh
  have hsurj : Function.Surjective (observabilityMatrix M P (q+1)).mulVec := by
    intro y
    exact ⟨R.map ψ *ᵥ y,by rw [Matrix.mulVec_mulVec,hR',Matrix.one_mulVec]⟩
  have hfirst : Module.finrank F (unobservableSpace M P (q+1)) = ρ := by
    have hh := (Matrix.toLin' (observabilityMatrix M P (q+1))).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,
      Module.finrank_fintype_fun_eq_card,observabilityMatrix_ker,
      Module.finrank_fintype_fun_eq_card] at hh
    simp only [Fintype.card_prod,Fintype.card_fin] at hh
    omega
  have hinj : Function.Injective (observabilityMatrix M P (q+2)).mulVec := by
    have hh := universal_terminal_observability_injective (K := K) (n := n) (m := m)
      (q+1) hw.le (by nlinarith) (ψ.comp (affineParameterMap K _))
      (hψ.comp (affineParameterMap_injective K _))
    simpa only [M,P,genericAffineSquare,genericAffineRows,Matrix.map_map,Nat.add_assoc] using hh
  have hnext : Module.finrank F (unobservableSpace M P (q+2)) = 0 := by
    rw [← observabilityMatrix_ker,LinearMap.ker_eq_bot.mpr hinj,finrank_bot]
  rw [glEquationMatrix_map,glEquationMatrix_field_finrank]
  exact gl_finrank_of_observability q ρ M P hsize hfirst hnext

theorem generic_one_output_gl_injective (N : ℕ) (hN : 2 ≤ N) :
    Function.Injective (glEquationMatrix (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1))).mulVec := by
  let F := GenericPencilField K (Fin N) (Fin 1)
  let φ := algebraMap (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1)))[X] F
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  apply matrix_mulVec_injective_of_map φ hφ
  change Function.Injective (Matrix.toLin' ((glEquationMatrix
    (genericAffineSquare K (Fin N) (Fin 1)) (genericAffineRows K (Fin N) (Fin 1))).map φ))
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := generic_affine_gl_nullity_from_observability (K := K) (N-2) 1
    (n := Fin N) (m := Fin 1) (by simp only [Fintype.card_fin]; omega)
    (by decide) (by simp) φ hφ
  simpa using h

theorem generic_one_output_sl_nullity (N : ℕ) (hN : 2 ≤ N) (i₀ : Fin N) :
    Module.finrank (GenericPencilField K (Fin N) (Fin 1))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix
        (genericAffineSquare K (Fin N) (Fin 1)) (genericAffineRows K (Fin N) (Fin 1)) i₀).map
          (algebraMap _ (GenericPencilField K (Fin N) (Fin 1)))))) = 1 := by
  letI : Nonempty (Fin N) := ⟨i₀⟩
  have h := generic_affine_sl_nullity_from_observability (K := K) (N-2) 1
    (n := Fin N) (m := Fin 1) (by simp only [Fintype.card_fin]; omega)
    (by decide) (by simp) i₀
    (algebraMap _ (GenericPencilField K (Fin N) (Fin 1)))
    (IsFractionRing.injective _ _)
  simpa using h

end FD56
