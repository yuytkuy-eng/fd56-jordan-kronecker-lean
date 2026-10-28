/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineKernelDualRank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A polynomial kernel frame that is independent over an extension field has
the same affine dual rank as a reduced kernel basis of the same cardinality. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K F a n j l : Type*} [Field K] [Field F]
  [Fintype n] [DecidableEq n] [Fintype j] [Fintype l]

omit [Fintype l] in
theorem polynomialKernelFrame_factor (A : Matrix a n K[X])
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' A)))
    (Z : Matrix n l K[X]) (hAZ : A * Z = 0) :
    ∃ T : Matrix j l K[X], polynomialKernelBasisMatrix A basis * T = Z := by
  let y (k : l) : LinearMap.ker (Matrix.toLin' A) :=
    ⟨fun i => Z i k, by
      change A *ᵥ (fun i => Z i k) = 0
      funext i
      exact congrFun (congrFun hAZ i) k⟩
  refine ⟨fun i k => basis.equivFun (y k) i, ?_⟩
  funext i k
  change (polynomialKernelBasisMatrix A basis *ᵥ (basis.equivFun (y k))) i = Z i k
  rw [polynomialKernelBasisMatrix_mulVec]
  exact congrArg (fun z : LinearMap.ker (Matrix.toLin' A) => z.val i)
    (basis.equivFun.symm_apply_apply (y k))

private theorem transpose_injective_of_field_frame
    (T : Matrix j l K[X]) (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (hcard : Fintype.card l = Fintype.card j)
    (hT : Function.Injective (T.map φ).mulVec) :
    Function.Injective T.transpose.mulVec := by
  classical
  have hsurj : Function.Surjective (T.map φ).mulVec := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Matrix.toLin' (T.map φ)) ?_).mp hT
    simpa only [Module.finrank_pi, Module.finrank_self, mul_one] using hcard
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj
  have hleft : R.transpose * (T.map φ).transpose = 1 := by
    rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  have hti : Function.Injective (T.map φ).transpose.mulVec := by
    intro u v huv
    have h := congrArg R.transpose.mulVec huv
    simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using h
  intro u v huv
  have hmap : (T.map φ).transpose *ᵥ (φ ∘ u) =
      (T.map φ).transpose *ᵥ (φ ∘ v) := by
    funext k
    simpa only [RingHom.map_mulVec] using
      congrArg φ (congrFun huv k)
  have h := hti hmap
  funext k
  exact hφ (congrFun h k)

theorem affineKernelFrame_finrank_range [DecidableEq j]
    (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i k,
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i k).natDegree ≤ d k)
    (hlead : Function.Injective (Matrix.mulVec (fun i k =>
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i k).coeff (d k))))
    (Z : Matrix n l K[X]) (hAZ : affineMatrixPencil A B * Z = 0)
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (hcard : Fintype.card l = Fintype.card j)
    (hZ : Function.Injective (Z.map φ).mulVec) :
    Module.finrank K (LinearMap.range (affineDualPairMap Z)) = ∑ k, (d k + 2) := by
  obtain ⟨T, hVT⟩ := polynomialKernelFrame_factor (affineMatrixPencil A B) basis Z hAZ
  have hT : Function.Injective (T.map φ).mulVec := by
    intro u v huv
    apply hZ
    rw [← hVT, Matrix.map_mul]
    simpa only [Matrix.mulVec_mulVec] using
      congrArg ((polynomialKernelBasisMatrix (affineMatrixPencil A B) basis).map φ).mulVec huv
  have htranspose := transpose_injective_of_field_frame T φ hφ hcard hT
  have hdual : affineDualPairMap Z =
      ((Matrix.toLin' T.transpose).restrictScalars K).comp
        (affineDualPairMap (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis)) := by
    apply LinearMap.ext
    intro x
    change Z.transpose *ᵥ _ = T.transpose *ᵥ
      ((polynomialKernelBasisMatrix (affineMatrixPencil A B) basis).transpose *ᵥ _)
    rw [← hVT, Matrix.transpose_mul, Matrix.mulVec_mulVec]
  rw [hdual]
  exact affineKernelDual_comp_finrank_range A B basis d hdegree hlead T htranspose

end FD56
