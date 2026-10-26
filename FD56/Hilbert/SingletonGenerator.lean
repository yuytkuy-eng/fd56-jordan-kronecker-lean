/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile

/-! A unique polynomial generator with a nonzero top coefficient gives one minimal degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

theorem hasMinimalKernelDegrees_singleton_of_generator
    (A : Matrix a b K[X]) (c : b → K[X]) (hker : A *ᵥ c = 0)
    (hgen : ∀ y : b → K[X], A *ᵥ y = 0 ↔ ∃! h : K[X], y = h • c)
    (D : ℕ) (hc : ∀ j, (c j).natDegree ≤ D) (htop : ∃ j, (c j).coeff D ≠ 0) :
    HasMinimalKernelDegrees A [D] := by
  classical
  let L : K[X] →ₗ[K[X]] LinearMap.ker (Matrix.toLin' A) :=
    (LinearMap.toSpanSingleton K[X] (b → K[X]) c).codRestrict _ (by
      intro h
      change A *ᵥ (h • c) = 0
      rw [Matrix.mulVec_smul,hker,smul_zero])
  have hL : Function.Bijective L := by
    constructor
    · intro u v huv
      obtain ⟨h,hh,hu⟩ := (hgen (u • c)).mp (by rw [Matrix.mulVec_smul,hker,smul_zero])
      have heu : u = h := hu u rfl
      have hev : v = h := hu v (congrArg Subtype.val huv)
      exact heu.trans hev.symm
    · intro y
      obtain ⟨h,hh,_⟩ := (hgen y.val).mp y.property
      exact ⟨h,Subtype.ext hh.symm⟩
  let B := (Basis.singleton (Fin 1) K[X]).map (LinearEquiv.ofBijective L hL)
  have hB : ∀ i j, polynomialKernelBasisMatrix A B i j = c i := by
    intro i j
    simp [B,polynomialKernelBasisMatrix,Basis.map_apply,L,LinearMap.toSpanSingleton_apply]
  refine ⟨1,B,(fun _ => D),?_,?_,?_⟩
  · intro i j
    rw [hB]
    exact hc i
  · intro u v huv
    obtain ⟨j,hj⟩ := htop
    have hh := congrFun huv j
    simp only [Matrix.mulVec,dotProduct,hB,Fin.sum_univ_one] at hh
    have he : u 0 = v 0 := mul_left_cancel₀ hj hh
    funext i
    exact Subsingleton.elim i 0 ▸ he
  · simp

end FD56
