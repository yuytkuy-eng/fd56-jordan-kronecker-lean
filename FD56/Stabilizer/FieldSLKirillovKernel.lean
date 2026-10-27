/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SLKirillovPencil
import FD56.Stabilizer.FieldRadical

/-! The actual traceless Kirillov matrix has the full field-valued SL radical. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slKirillovMatrix_field_pairing (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (z w : SLChartInput n m i₀ → K) :
    w ⬝ᵥ (slKirillovMatrix M P i₀ *ᵥ z)=
      fieldKirillovForm M P (matrixPairEquiv K K n m (slChartEmbed K K i₀ z))
        (matrixPairEquiv K K n m (slChartEmbed K K i₀ w)) := by
  rw [slKirillovMatrix_pairing,glKirillovMatrix_pairing_equations,fieldKirillovForm_equations]
  rfl

theorem slKirillovMatrix_field_kernel_iff (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (z : SLChartInput n m i₀ → K) :
    slKirillovMatrix M P i₀ *ᵥ z=0 ↔
      matrixPairEquiv K K n m (slChartEmbed K K i₀ z) ∈ fieldSLRadical M P := by
  constructor
  · intro hz
    refine ⟨slChartEmbed_trace K K i₀ z,?_⟩
    intro w hw
    let v := (matrixPairEquiv K K n m).symm w
    have ht : slInputTrace K K v=0 := hw
    have he := slChartEmbed_retract K K i₀ v ht
    have h := slKirillovMatrix_field_pairing M P i₀ z (slChartRetract K K i₀ v)
    rw [hz,dotProduct_zero,he,LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · intro hz
    funext i
    have h := hz.2 (matrixPairEquiv K K n m (slChartEmbed K K i₀ (Pi.single i 1)))
      (slChartEmbed_trace K K i₀ _)
    have hp := slKirillovMatrix_field_pairing M P i₀ z (Pi.single i 1)
    simpa only [single_dotProduct,one_mul] using hp.trans h

def fieldSLKirillovKernelEquiv (M : Matrix n n K) (P : Matrix m n K) (i₀ : n) :
    LinearMap.ker (Matrix.toLin' (slKirillovMatrix M P i₀)) ≃ₗ[K] fieldSLRadical M P where
  toFun z := ⟨matrixPairEquiv K K n m (slChartEmbed K K i₀ z.val),
    (slKirillovMatrix_field_kernel_iff M P i₀ z.val).mp z.property⟩
  invFun w := ⟨slChartRetract K K i₀ ((matrixPairEquiv K K n m).symm w.val),by
    apply (slKirillovMatrix_field_kernel_iff M P i₀ _).mpr
    rw [slChartEmbed_retract K K i₀ _ w.property.1,LinearEquiv.apply_symm_apply]
    exact w.property⟩
  left_inv z := by
    apply Subtype.ext
    dsimp only
    rw [LinearEquiv.symm_apply_apply,slChartRetract_embed]
  right_inv w := by
    apply Subtype.ext
    dsimp only
    rw [slChartEmbed_retract K K i₀ _ w.property.1,LinearEquiv.apply_symm_apply]
  map_add' z w := by
    apply Subtype.ext
    change matrixPairEquiv K K n m (slChartEmbed K K i₀ (z.val+w.val))=_
    rw [map_add,map_add]
    rfl
  map_smul' c z := by
    apply Subtype.ext
    change matrixPairEquiv K K n m (slChartEmbed K K i₀ (c•z.val))=_
    rw [map_smul,map_smul]
    rfl

theorem slKirillovMatrix_field_finrank (M : Matrix n n K) (P : Matrix m n K) (i₀ : n) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (slKirillovMatrix M P i₀)))=
      Module.finrank K (fieldSLRadical M P) :=
  (fieldSLKirillovKernelEquiv M P i₀).finrank_eq

end FD56
