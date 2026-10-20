/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineProduct
import FD56.Hilbert.GLMatrix
import FD56.Hilbert.HilbertObstruction

/-! Actual bounded SL radicals when the two coefficient column spaces are
independent. The scalar correction contributes d + 2 dimensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem surjective_comap_finrank {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (S : Submodule K W) :
    Module.finrank K (S.comap f) = Module.finrank K (LinearMap.ker f) + Module.finrank K S := by
  let g := S.mkQ.comp f
  have hg : Function.Surjective g := S.mkQ_surjective.comp hf
  have hk : LinearMap.ker g = S.comap f := by ext x; simp [g]
  have h₁ := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hk] at h₁
  have h₂ := S.finrank_quotient_add_finrank
  have h₃ := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at h₃
  omega

def boundedScalarMap (d : ℕ) : BoundedPoly K d →ₗ[K] BoundedMatrix K n n d where
  toFun c i j := if i = j then c else 0
  map_add' c c' := by funext i j; by_cases h : i = j <;> simp [h]
  map_smul' a c := by funext i j; by_cases h : i = j <;> simp [h]

def boundedScalarSpace (d : ℕ) : Submodule K (BoundedMatrix K n n d) :=
  LinearMap.range (boundedScalarMap (K := K) (n := n) d)

omit [Fintype n] in
theorem boundedScalarSpace_finrank (i₀ : n) (d : ℕ) :
    Module.finrank K (boundedScalarSpace (K := K) (n := n) d) = d + 1 := by
  have hi : Function.Injective (boundedScalarMap (K := K) (n := n) d) := by
    intro c c' h
    simpa [boundedScalarMap] using congrArg (fun A : BoundedMatrix K n n d => A i₀ i₀) h
  exact (LinearMap.finrank_range_of_inj hi).trans (boundedPoly_finrank d)

omit [Fintype n] in
theorem mem_boundedScalarSpace_iff (i₀ : n) (d : ℕ) (A : BoundedMatrix K n n d) :
    A ∈ boundedScalarSpace d ↔ ∃ c : K[X], entries A = c • (1 : Matrix n n K[X]) := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c.val, ?_⟩
    funext i j
    by_cases h : i = j <;> simp [entries, boundedScalarMap, Matrix.one_apply, h]
  · rintro ⟨c, hc⟩
    have hb : c.natDegree ≤ d := by
      have hh := congrArg (fun B : Matrix n n K[X] => B i₀ i₀) hc
      have hh' : (A i₀ i₀).val = c := by simpa [entries] using hh
      rw [← hh']
      exact boundedPoly_degree d (A i₀ i₀)
    refine ⟨boundedPolyOf c hb, ?_⟩
    funext i j
    apply Subtype.ext
    have hh := congrArg (fun B : Matrix n n K[X] => B i j) hc
    by_cases h : i = j <;>
      simpa [boundedScalarMap, boundedPolyOf, entries, Matrix.one_apply, h] using hh.symm

theorem tall_slRadical_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (R : Matrix n m K[X]) (hR : R * P = 1) (i₀ : n)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    SLRadical M P X U ↔ X = 0 ∧ ∃ c : K[X], U * P = c • (1 : Matrix n n K[X]) := by
  letI : Nonempty n := ⟨i₀⟩
  rw [slRadical_iff_equations]
  constructor
  · rintro ⟨_, hPX, c, hc⟩
    have hX : X = 0 := by
      have hh := congrArg (fun A : Matrix m n K[X] => R * A) hPX
      simpa [← Matrix.mul_assoc, hR] using hh
    refine ⟨hX, -c, ?_⟩
    rw [hX, Matrix.mul_zero, Matrix.zero_mul, sub_self] at hc
    exact (eq_neg_of_add_eq_zero_left hc.symm).trans (neg_smul c (1 : Matrix n n K[X])).symm
  · rintro ⟨rfl, c, hc⟩
    refine ⟨by simp, by simp, -c, ?_⟩
    simp [hc]

def tallSLKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : DegreeBound P 1) (R : Matrix n m K[X]) (hR : R * P = 1)
    (i₀ : n) (d : ℕ) :
    boundedSLKernel M P d ≃ₗ[K]
      (boundedScalarSpace (K := K) (n := n) (d + 1)).comap (boundedRightProduct P hP d) where
  toFun z := ⟨z.val.2, (mem_boundedScalarSpace_iff i₀ (d + 1) _).mpr
    ((tall_slRadical_iff M P R hR i₀ _ _).mp z.property).2⟩
  invFun U := ⟨(0, U.val), (tall_slRadical_iff M P R hR i₀ _ _).mpr
    ⟨rfl, (mem_boundedScalarSpace_iff i₀ (d + 1) _).mp U.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective d
      exact ((tall_slRadical_iff M P R hR i₀ _ _).mp z.property).1.symm
    · rfl
  right_inv U := rfl
  map_add' z w := rfl
  map_smul' a z := rfl

theorem tall_slHilbert (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : DegreeBound P 1) (i₀ : n)
    (hJ : Function.Injective (affineCoefficientColumns P).mulVec) (d : ℕ) :
    slHilbert M P d =
      (Fintype.card n * Fintype.card m * (d + 1) -
        Fintype.card n * Fintype.card n * (d + 2)) + (d + 2) := by
  obtain ⟨R₀, R₁, hR₀, hR₁⟩ := affine_dual_matrices P hP hJ
  unfold slHilbert
  rw [(tallSLKernelEquiv M P hP (R₀.map Polynomial.C) hR₀ i₀ d).finrank_eq,
    surjective_comap_finrank _ (boundedRightProduct_surjective P hP R₀ R₁ hR₀ hR₁ d),
    boundedRightProduct_kernel_finrank P hP R₀ R₁ hR₀ hR₁,
    boundedScalarSpace_finrank i₀]

theorem tall_gl_kernel_equations (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (R : Matrix n m K[X]) (hR : R * P = 1) (v : SLInput n m → K[X]) :
    glEquationMatrix M P *ᵥ v = 0 ↔
      (fun i j => v (.inl (i, j))) = 0 ∧
        (show Matrix n m K[X] from fun i j => v (.inr (i, j))) * P = 0 := by
  rw [glEquationMatrix_kernel_iff]
  constructor
  · rintro ⟨hP, hM⟩
    have hX : (matrixPairEquiv K[X] K[X] n m v).1 = 0 := by
      have hh := congrArg (fun A : Matrix m n K[X] => R * A) hP
      simpa [← Matrix.mul_assoc, hR] using hh
    refine ⟨hX, ?_⟩
    simpa [stabilizerResidual, hX] using hM
  · rintro ⟨hX, hU⟩
    change (matrixPairEquiv K[X] K[X] n m v).1 = 0 at hX
    change (matrixPairEquiv K[X] K[X] n m v).2 * P = 0 at hU
    simp [stabilizerResidual, hX, hU]

def tallGLKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : DegreeBound P 1) (R : Matrix n m K[X]) (hR : R * P = 1) (d : ℕ) :
    polynomialKernelAtDegree (glEquationMatrix M P) d ≃ₗ[K]
      LinearMap.ker (boundedRightProduct (l := n) P hP d) where
  toFun v := ⟨fun i j => v.val (.inr (i, j)), by
    have hh := ((tall_gl_kernel_equations M P R hR _).mp v.property).2
    apply entries_injective (d + 1)
    exact hh⟩
  invFun U := ⟨Sum.elim (fun _ => 0) (fun ij => U.val ij.1 ij.2), by
    apply (tall_gl_kernel_equations M P R hR _).mpr
    constructor
    · rfl
    · exact congrArg entries U.property⟩
  left_inv v := by
    apply Subtype.ext
    funext ij
    rcases ij with ij | ij
    · apply Subtype.ext
      have hh := ((tall_gl_kernel_equations M P R hR _).mp v.property).1
      exact (congrArg (fun A : Matrix n n K[X] => A ij.1 ij.2) hh).symm
    · rfl
  right_inv U := rfl
  map_add' v w := rfl
  map_smul' a v := rfl

theorem tall_gl_kernel_hilbert (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hP : DegreeBound P 1)
    (hJ : Function.Injective (affineCoefficientColumns P).mulVec) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      Fintype.card n * Fintype.card m * (d + 1) -
        Fintype.card n * Fintype.card n * (d + 2) := by
  obtain ⟨R₀, R₁, hR₀, hR₁⟩ := affine_dual_matrices P hP hJ
  rw [(tallGLKernelEquiv M P hP (R₀.map Polynomial.C) hR₀ d).finrank_eq]
  exact boundedRightProduct_kernel_finrank P hP R₀ R₁ hR₀ hR₁ d

end FD56
