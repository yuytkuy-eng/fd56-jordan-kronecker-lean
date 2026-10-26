/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericWideObservabilityRightInverse
import FD56.Hilbert.GenericTerminalObservability
import FD56.Hilbert.MinimalDegreeNullity
import FD56.Stabilizer.SLKirillovPencil

/-! Rational nullity and minimal-degree counts for the first higher-depth SL case. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K F : Type*} [Field K] [Field F]

theorem generic_affine_sl_nullity_from_observability {n m : Type}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (q ρ : ℕ) (hsize : Fintype.card n = (q+1)*Fintype.card m + ρ)
    (hρ : 0 < ρ) (hρm : ρ ≤ Fintype.card m) (i₀ : n)
    (ψ : (AffineCoefficientField K (MatrixParameters n m))[X] →+* F)
    (hψ : Function.Injective ψ) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' ((slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀).map ψ))) =
        ρ*(Fintype.card m-ρ)+1 := by
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
  rw [slEquationMatrix_specialized_finrank]
  exact sl_finrank_of_observability q ρ M P hsize hfirst hnext

theorem generic_five_two_sl_nullity (i₀ : Fin 5) :
    Module.finrank (GenericPencilField K (Fin 5) (Fin 2))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix (genericAffineSquare K (Fin 5) (Fin 2))
        (genericAffineRows K (Fin 5) (Fin 2)) i₀).map
        (algebraMap _ (GenericPencilField K (Fin 5) (Fin 2)))))) = 2 := by
  exact generic_affine_sl_nullity_from_observability 1 1 (by decide) (by decide) (by decide)
    i₀ _ (IsFractionRing.injective _ _)

theorem generic_five_two_sl_minimal_degrees_length (i₀ : Fin 5) (xs : List ℕ)
    (h : HasMinimalKernelDegrees (slKirillovMatrix (genericAffineSquare K (Fin 5) (Fin 2))
      (genericAffineRows K (Fin 5) (Fin 2)) i₀) xs) : xs.length = 2 := by
  have he := (slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mp h
  exact (he.length_eq_fraction_nullity (F := GenericPencilField K (Fin 5) (Fin 2))).trans
    (generic_five_two_sl_nullity i₀)

theorem generic_five_two_sl_kirillov_nullity (i₀ : Fin 5) :
    Module.finrank (GenericPencilField K (Fin 5) (Fin 2))
      (LinearMap.ker (Matrix.toLin' ((slKirillovMatrix (genericAffineSquare K (Fin 5) (Fin 2))
        (genericAffineRows K (Fin 5) (Fin 2)) i₀).map
        (algebraMap _ (GenericPencilField K (Fin 5) (Fin 2)))))) = 2 := by
  let A := slKirillovMatrix (genericAffineSquare K (Fin 5) (Fin 2))
    (genericAffineRows K (Fin 5) (Fin 2)) i₀
  obtain ⟨r,B,e,hZ,hlead,_,_⟩ := polynomial_kernel_has_minimal_basis A
  have hmin : HasMinimalKernelDegrees A (List.ofFn e) := ⟨r,B,e,hZ,hlead,List.Perm.refl _⟩
  have hlen := generic_five_two_sl_minimal_degrees_length i₀ (List.ofFn e) hmin
  rw [polynomial_kernel_basis_fraction_finrank A B,Fintype.card_fin]
  simpa only [List.length_ofFn] using hlen

end FD56
