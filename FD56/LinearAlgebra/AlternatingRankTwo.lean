/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingCongruence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! A nonzero pivot determines every entry of an alternating matrix of rank at most two. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem alternating_rank_two_pivot_coordinates (A : Matrix n n K)
    (hA : ∀ v : n → K, v ⬝ᵥ (A *ᵥ v) = 0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A)) ≤ 2)
    (i j : n) (hij : A i j ≠ 0) :
    Function.Injective (fun v : LinearMap.range (Matrix.toLin' A) => (v.val i, v.val j)) := by
  let f : LinearMap.range (Matrix.toLin' A) →ₗ[K] K × K :=
    { toFun := fun v => (v.val i, v.val j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hd := alternating_matrix_diag_zero A hA
  have ht := alternating_matrix_transpose A hA
  have hji : A j i = - A i j := congrArg (fun B => B i j) ht
  have hs : Function.Surjective f := by
    rintro ⟨x,y⟩
    let v : n → K := (-y / A i j) • (Pi.single i 1 : n → K) +
      (x / A i j) • (Pi.single j 1 : n → K)
    refine ⟨⟨A *ᵥ v, ⟨v,rfl⟩⟩,?_⟩
    change ((A *ᵥ v) i,(A *ᵥ v) j)=(x,y)
    apply Prod.ext <;>
      simp only [v,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_single_one,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.transpose_apply,hd,hji,mul_zero,zero_add,add_zero]
    · field_simp
    · field_simp
  have hh := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_prod,
    Module.finrank_self] at hh
  have hk : Module.finrank K (LinearMap.ker f) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

theorem alternating_rank_two_pivot_formula (A : Matrix n n K)
    (hA : ∀ v : n → K, v ⬝ᵥ (A *ᵥ v) = 0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A)) ≤ 2)
    (i j : n) (hij : A i j ≠ 0) (k l : n) :
    A k l = (A k i * A l j - A k j * A l i) / A i j := by
  let u : LinearMap.range (Matrix.toLin' A) :=
    ⟨A *ᵥ Pi.single l 1, ⟨Pi.single l 1,rfl⟩⟩
  let v : n → K := (-(A j l) / A i j) • (Pi.single i 1 : n → K) +
    (A i l / A i j) • (Pi.single j 1 : n → K)
  let w : LinearMap.range (Matrix.toLin' A) := ⟨A *ᵥ v, ⟨v,rfl⟩⟩
  have hd := alternating_matrix_diag_zero A hA
  have ht := alternating_matrix_transpose A hA
  have hji : A j i = - A i j := congrArg (fun B => B i j) ht
  have he : (u.val i,u.val j) = (w.val i,w.val j) := by
    apply Prod.ext <;>
      simp only [u,w,v,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_single_one,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.transpose_apply,hd,hji,mul_zero,zero_add,add_zero]
    · field_simp
    · field_simp
  have heq := congrArg (fun z : LinearMap.range (Matrix.toLin' A) => z.val k)
    (alternating_rank_two_pivot_coordinates A hA hr i j hij he)
  simp only [u,w,v,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_single_one,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.transpose_apply] at heq
  rw [heq]
  have hjl : A j l = - A l j := congrArg (fun B => B l j) ht
  have hil : A i l = - A l i := congrArg (fun B => B l i) ht
  rw [hjl,hil]
  ring

theorem alternating_rank_two_decomposable (A : Matrix n n K)
    (hA : ∀ v : n → K, v ⬝ᵥ (A *ᵥ v) = 0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A)) ≤ 2)
    (i j : n) (hij : A i j ≠ 0) :
    ∃ u v : n → K, A = Matrix.vecMulVec u v - Matrix.vecMulVec v u := by
  refine ⟨(fun k => A k i),(fun k => A k j / A i j),?_⟩
  ext k l
  rw [alternating_rank_two_pivot_formula A hA hr i j hij k l]
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply]
  ring

end FD56
