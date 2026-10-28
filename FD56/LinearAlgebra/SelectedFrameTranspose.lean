/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RankSpecialization

/-! A square selected column frame over an extension field ensures polynomial
row independence, without requiring the whole matrix to be square. -/

noncomputable section
namespace FD56
open Matrix

theorem matrix_transpose_injective_of_selected_field_columns
    {R F r s t : Type*} [CommRing R] [Field F] [Fintype r] [Fintype s] [Fintype t]
    (C : Matrix r s R) (φ : R →+* F) (hφ : Function.Injective φ)
    (select : t → s) (hcard : Fintype.card t=Fintype.card r)
    (hselected : Function.Injective ((C.submatrix id select).map φ).mulVec) :
    Function.Injective C.transpose.mulVec := by
  classical
  let T := (C.submatrix id select).map φ
  have hsurj : Function.Surjective T.mulVec := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f:=Matrix.toLin' T) ?_).mp hselected
    simpa only [Module.finrank_pi,Module.finrank_self,mul_one] using hcard
  have htrans : Function.Injective T.transpose.mulVec :=
    matrix_transpose_injective_of_surjective T hsurj
  intro u v huv
  have hselected' : (C.submatrix id select).transpose*ᵥu=
      (C.submatrix id select).transpose*ᵥv := funext (fun j => congrFun huv (select j))
  have hmapped : T.transpose*ᵥ(φ ∘ u)=T.transpose*ᵥ(φ ∘ v) := by
    funext j
    simpa only [RingHom.map_mulVec] using congrArg φ (congrFun hselected' j)
  have h := htrans hmapped
  funext i
  exact hφ (congrFun h i)

theorem factor_transpose_injective_of_selected_field_frame
    {R F n r s t : Type*} [CommRing R] [Field F] [Fintype r] [Fintype s] [Fintype t]
    (V : Matrix n r R) (C : Matrix r s R) (φ : R →+* F) (hφ : Function.Injective φ)
    (select : t → s) (hcard : Fintype.card t=Fintype.card r)
    (hselected : Function.Injective (((V*C).submatrix id select).map φ).mulVec) :
    Function.Injective C.transpose.mulVec := by
  apply matrix_transpose_injective_of_selected_field_columns C φ hφ select hcard
  intro u v huv
  apply hselected
  have he : ((V*C).submatrix id select).map φ =
      V.map φ*(C.submatrix id select).map φ := by
    rw [← Matrix.map_mul]
    congr 1
  rw [he,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,huv]

end FD56
