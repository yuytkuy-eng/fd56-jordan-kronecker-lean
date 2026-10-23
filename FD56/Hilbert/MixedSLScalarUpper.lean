/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleSLHilbert

/-! Scalar coefficient selectors bound the mixed-degree SL correction. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def boundedPolySubmoduleSelector {d : ℕ} (V : Submodule K (BoundedPoly K d))
    (t : ℕ) (f : Fin t → ℕ) : V →ₗ[K] (Fin t → K) where
  toFun z j := z.val.val.coeff (f j)
  map_add' z w := by ext j; exact Polynomial.coeff_add _ _ _
  map_smul' k z := by ext j; exact Polynomial.coeff_smul _ _ _

theorem boundedPolySubmodule_finrank_le_selector {d : ℕ}
    (V : Submodule K (BoundedPoly K d)) (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ c : V, (∀ j, c.val.val.coeff (f j) = 0) → c.val.val = 0) :
    Module.finrank K V ≤ t := by
  have hinj : Function.Injective (boundedPolySubmoduleSelector V t f) := by
    intro x y hxy
    suffices h : x - y = 0 by exact sub_eq_zero.mp h
    apply Subtype.ext
    apply Subtype.ext
    apply hzero (x-y)
    have hz : boundedPolySubmoduleSelector V t f (x-y) = 0 := by
      exact ((boundedPolySubmoduleSelector V t f).map_sub x y).trans
        (by rw [hxy,sub_self])
    exact congrFun hz
  have hh := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using hh

theorem boundedSLScalar_range_le_of_selector
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d t : ℕ)
    (f : Fin t → ℕ)
    (hscalar : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]),
      DegreeBound X d → DegreeBound U d → SLRadical M P X U →
      M * X - X * M = U * P + c • 1 →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    Module.finrank K (LinearMap.range (boundedSLScalar M P hM hP i₀ d)) ≤ t := by
  apply boundedPolySubmodule_finrank_le_selector _ t f
  intro c hc
  obtain ⟨z,hz⟩ := c.property
  have hr := boundedSLScalar_residual M P hM hP i₀ d z
  rw [hz] at hr
  apply hscalar (entries z.val.1) (entries z.val.2) c.val.val
    (entries_degree z.val.1) (entries_degree z.val.2) z.property _ hc
  change M * entries z.val.1 - entries z.val.1 * M - entries z.val.2 * P = _ at hr
  exact (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)

theorem middle_slHilbert_le_gl_add_selector
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : r → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
    (hBL : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
    (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (i₀ : n) (d t : ℕ) (f : Fin t → ℕ)
    (hscalar : ∀ (E : Matrix r m K[X]) (c : K[X]),
      (∀ i j, E i j = 0 ∨ (a i + 1 ≤ d ∧ (E i j).natDegree ≤ d - (a i + 1))) →
      E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    slHilbert M P d ≤
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) + t := by
  rw [middle_slHilbert_eq_gl_add_scalar_range M P B R hPR hG hM hP i₀ d]
  apply Nat.add_le_add_left
  apply boundedSLScalar_range_le_of_selector M P hM hP i₀ d t f
  intro X U c hX _ hs hc htail
  letI : Nonempty n := ⟨i₀⟩
  have hPX := ((slRadical_iff_equations M P X U).mp hs).2.1
  obtain ⟨E,hE,_⟩ := middle_sl_forward M P B R hPR hG X U c hPX hc
  apply hscalar E c _ hE.1 htail
  apply (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E a d
    hB hBL hP hPL).mp
  change DegreeBound (middleSLX P B E) d
  rw [← hE.2.1]
  exact hX

/-- Only the high-degree rows are needed to bound the scalar image. -/
theorem mixed_middle_slHilbert_upper_of_high_rows
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (a u v : ℕ)
    (B : Basis (Fin u ⊕ Fin v) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤
      Sum.elim (fun _ => a) (fun _ => a+1) i)
    (hBL : Function.Injective (Matrix.mulVec (fun x i =>
      (polynomialKernelBasisMatrix P B x i).coeff (Sum.elim (fun _ => a) (fun _ => a+1) i))))
    (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (i₀ : n) (d k t : ℕ) (hk : d-(a+2) ≤ k) (f : Fin t → ℕ)
    (hscalar : ∀ (E : Matrix (Fin v) m K[X]) (c : K[X]), DegreeBound E k →
      E * (P * M * polynomialKernelBasisMatrix P B) =
        (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
          Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    slHilbert M P d ≤
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) + t := by
  apply middle_slHilbert_le_gl_add_selector M P B R hPR hG
    (Sum.elim (fun _ => a) (fun _ => a+1)) hM hP hB hBL hPL i₀ d t f
  intro E c hE hrel htail
  let Eh : Matrix (Fin v) m K[X] := E.submatrix Sum.inr id
  have hEh : DegreeBound Eh k := by
    intro i j
    rcases hE (Sum.inr i) j with h | ⟨_,h⟩
    · change (E (Sum.inr i) j).natDegree ≤ k
      rw [h]
      simp
    · apply h.trans
      simpa only [Sum.elim_inr,Nat.add_assoc,Nat.reduceAdd] using hk
  apply hscalar Eh c hEh _ htail
  funext i j
  have h := congrArg (fun A : Matrix (Fin u ⊕ Fin v) (Fin u ⊕ Fin v) K[X] =>
    A (Sum.inr i) j) hrel
  simpa [Eh, Matrix.mul_apply, Matrix.one_apply] using h

theorem mixed_middle_slHilbert_critical_upper
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (a u v : ℕ)
    (B : Basis (Fin u ⊕ Fin v) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤
      Sum.elim (fun _ => a) (fun _ => a+1) i)
    (hBL : Function.Injective (Matrix.mulVec (fun x i =>
      (polynomialKernelBasisMatrix P B x i).coeff (Sum.elim (fun _ => a) (fun _ => a+1) i))))
    (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (i₀ : n) (t : ℕ) (f : Fin t → ℕ)
    (hscalar : ∀ (E : Matrix (Fin v) m K[X]) (c : K[X]), DegreeBound E 0 →
      E * (P * M * polynomialKernelBasisMatrix P B) =
        (-c) • (fun i j => if Sum.inr i = j then 1 else 0 :
          Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    slHilbert M P (a+2) ≤
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) (a+2)) + t := by
  apply middle_slHilbert_le_gl_add_selector M P B R hPR hG
    (Sum.elim (fun _ => a) (fun _ => a+1)) hM hP hB hBL hPL i₀ (a+2) t f
  intro E c hE hrel htail
  let Eh : Matrix (Fin v) m K[X] := E.submatrix Sum.inr id
  have hEh : DegreeBound Eh 0 := by
    intro i j
    rcases hE (Sum.inr i) j with h | ⟨_,h⟩
    · change (E (Sum.inr i) j).natDegree ≤ 0
      rw [h]
      simp
    · simpa only [Sum.elim_inr, Nat.add_assoc, Nat.reduceAdd, Nat.sub_self] using h
  apply hscalar Eh c hEh _ htail
  funext i j
  have h := congrArg (fun A : Matrix (Fin u ⊕ Fin v) (Fin u ⊕ Fin v) K[X] =>
    A (Sum.inr i) j) hrel
  simpa [Eh, Matrix.mul_apply, Matrix.one_apply] using h

end FD56
