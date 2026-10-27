/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SimpleDeterminantRoot
import FD56.Stabilizer.GenericDivisibleObservability
import FD56.Stabilizer.GenericWideObservabilityRightInverse
import FD56.Stabilizer.GenericObservabilityLeftInverse

/-! The three observability nullities at a generic square-observability root. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L n m : Type*} [Field K] [Field L]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem generic_wide_observability_evaluated_nullity (q : ℕ)
    (hn : q*Fintype.card m < Fintype.card n)
    (φ : AffineCoefficientField K (MatrixParameters n m) →+* L) (x : L) :
    Module.finrank L (unobservableSpace
      ((genericAffineSquare K n m).map (Polynomial.eval₂RingHom φ x))
      ((genericAffineRows K n m).map (Polynomial.eval₂RingHom φ x)) q) =
      Fintype.card n-q*Fintype.card m := by
  let ev := Polynomial.eval₂RingHom φ x
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K := K) q hn
  have hR' := congrArg (fun A => A.map ev) hR
  dsimp only at hR'
  rw [Matrix.map_mul,observabilityMatrix_map,Matrix.map_one _ (map_zero ev) (map_one ev)] at hR'
  have hsurj : Function.Surjective (observabilityMatrix
      ((genericAffineSquare K n m).map ev) ((genericAffineRows K n m).map ev) q).mulVec := by
    intro v
    refine ⟨R.map ev *ᵥ v, ?_⟩
    rw [Matrix.mulVec_mulVec,hR',Matrix.one_mulVec]
  have h := surjective_matrix_kernel_finrank _ hsurj
  rw [observabilityMatrix_ker] at h
  simpa only [Fintype.card_prod,Fintype.card_fin] using h

theorem generic_tall_observability_evaluated_nullity (q : ℕ)
    (hm : 2≤Fintype.card m) (hn : Fintype.card n < q*Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters n m) →+* L) (x : L) :
    Module.finrank L (unobservableSpace
      ((genericAffineSquare K n m).map (Polynomial.eval₂RingHom φ x))
      ((genericAffineRows K n m).map (Polynomial.eval₂RingHom φ x)) q) = 0 := by
  let ev := Polynomial.eval₂RingHom φ x
  obtain ⟨V,hV⟩ := generic_affine_observability_left_inverse (K := K) q hm hn
  have hV' := congrArg (fun A => A.map ev) hV
  dsimp only at hV'
  rw [Matrix.map_mul,observabilityMatrix_map,Matrix.map_one _ (map_zero ev) (map_one ev)] at hV'
  have hinj : Function.Injective (observabilityMatrix
      ((genericAffineSquare K n m).map ev) ((genericAffineRows K n m).map ev) q).mulVec := by
    intro v w h
    have hh := congrArg (fun z => V.map ev *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec,hV',Matrix.one_mulVec] using hh
  rw [← observabilityMatrix_ker,LinearMap.ker_eq_bot.mpr hinj,finrank_bot]

theorem generic_divisible_observability_root_nullity (q : ℕ)
    (φ : AffineCoefficientField K (MatrixParameters (Fin q × m) m) →+* L) (x : L)
    (hx : (observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q).det.eval₂ φ x=0) :
    Module.finrank L (unobservableSpace
      ((genericAffineSquare K (Fin q × m) m).map (Polynomial.eval₂RingHom φ x))
      ((genericAffineRows K (Fin q × m) m).map (Polynomial.eval₂RingHom φ x)) q)=1 := by
  have h := polynomial_matrix_separable_root_kernel_finrank _ φ x
    (generic_divisible_observability_separable K m q).2 hx
  rw [observabilityMatrix_map,observabilityMatrix_ker] at h
  exact h

theorem generic_divisible_observability_root_profile (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) (x : L)
    (hx : (observabilityMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) (q+1)).det.eval₂ φ x=0) :
    let M := (genericAffineSquare K (Fin (q+1) × m) m).map (Polynomial.eval₂RingHom φ x)
    let P := (genericAffineRows K (Fin (q+1) × m) m).map (Polynomial.eval₂RingHom φ x)
    Module.finrank L (unobservableSpace M P q)=Fintype.card m ∧
      Module.finrank L (unobservableSpace M P (q+1))=1 ∧
      Module.finrank L (unobservableSpace M P (q+2))=0 := by
  have hwide : q*Fintype.card m < Fintype.card (Fin (q+1) × m) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    nlinarith
  have htall : Fintype.card (Fin (q+1) × m) < (q+2)*Fintype.card m := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    nlinarith
  refine ⟨?_,generic_divisible_observability_root_nullity (q+1) φ x hx,
    generic_tall_observability_evaluated_nullity (q+2) hm htall φ x⟩
  have h := generic_wide_observability_evaluated_nullity q hwide φ x
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.add_mul,one_mul,
    Nat.add_sub_cancel_left] using h

end FD56
