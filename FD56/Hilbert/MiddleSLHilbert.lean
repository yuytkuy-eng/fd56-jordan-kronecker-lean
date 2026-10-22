/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.MiddleSLReduction
import FD56.Stabilizer.MiddleSLDegrees

/-! The bounded scalar correction gives an exact dimension formula between
the full SL radical and the GL kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
theorem bounded_stabilizer_residual_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (z : BoundedMatrix K n n d × BoundedMatrix K n m d) :
    DegreeBound (stabilizerResidual M P (entries z.1, entries z.2)) (d + 1) := by
  apply degreeBound_sub
  · apply degreeBound_sub
    · simpa only [Nat.add_comm] using degreeBound_mul hM (entries_degree z.1)
    · exact degreeBound_mul (entries_degree z.1) hM
  · exact degreeBound_mul (entries_degree z.2) hP

def boundedSLScalar (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ) :
    boundedSLKernel M P d →ₗ[K] BoundedPoly K (d + 1) where
  toFun z := boundedPolyOf
    (stabilizerResidual M P (entries z.val.1, entries z.val.2) i₀ i₀)
    (bounded_stabilizer_residual_degree M P hM hP d z.val i₀ i₀)
  map_add' z w := by
    apply Subtype.ext
    change (stabilizerResidual M P
      ((entries z.val.1, entries z.val.2) + (entries w.val.1, entries w.val.2))) i₀ i₀ = _
    rw [map_add]
    rfl
  map_smul' a z := by
    apply Subtype.ext
    change (stabilizerResidual M P (a • (entries z.val.1, entries z.val.2))) i₀ i₀ = _
    exact congrArg (fun A : Matrix n n K[X] => A i₀ i₀)
      (((stabilizerResidual M P).restrictScalars K).map_smul a _)

theorem boundedSLScalar_residual (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (z : boundedSLKernel M P d) :
    stabilizerResidual M P (entries z.val.1, entries z.val.2) =
      (boundedSLScalar M P hM hP i₀ d z).val • (1 : Matrix n n K[X]) := by
  letI : Nonempty n := ⟨i₀⟩
  obtain ⟨_, _, c, hc⟩ := (slRadical_iff_equations M P _ _).mp z.property
  have hr : stabilizerResidual M P (entries z.val.1, entries z.val.2) = c • 1 := by
    change M * entries z.val.1 - entries z.val.1 * M - entries z.val.2 * P = _
    rw [hc, add_sub_cancel_left]
  change stabilizerResidual M P (entries z.val.1, entries z.val.2) =
    (stabilizerResidual M P (entries z.val.1, entries z.val.2) i₀ i₀) • 1
  rw [hr]
  simp

theorem boundedSLScalar_zero_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (z : boundedSLKernel M P d) :
    boundedSLScalar M P hM hP i₀ d z = 0 ↔
      stabilizerResidual M P (entries z.val.1, entries z.val.2) = 0 := by
  constructor
  · intro hz
    rw [boundedSLScalar_residual M P hM hP i₀ d z, hz]
    simp
  · intro hz
    apply Subtype.ext
    change stabilizerResidual M P (entries z.val.1, entries z.val.2) i₀ i₀ = 0
    rw [hz]
    rfl

def boundedSLScalarKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P * X = 0 → M * X - X * M = U * P → Matrix.trace X = 0) :
    LinearMap.ker (boundedSLScalar M P hM hP i₀ d) ≃ₗ[K]
      polynomialKernelAtDegree (glEquationMatrix M P) d where
  toFun z := ⟨(matrixPairEquiv K (BoundedPoly K d) n m).symm z.val.val, by
    apply (glEquationMatrix_kernel_iff M P _).mpr
    letI : Nonempty n := ⟨i₀⟩
    exact ⟨((slRadical_iff_equations M P _ _).mp z.val.property).2.1,
      (boundedSLScalar_zero_iff M P hM hP i₀ d z.val).mp z.property⟩⟩
  invFun v := by
    let z := matrixPairEquiv K (BoundedPoly K d) n m v.val
    have hv := (glEquationMatrix_kernel_iff M P (fun i => (v.val i).val)).mp v.property
    change P * entries z.1 = 0 ∧ stabilizerResidual M P (entries z.1, entries z.2) = 0 at hv
    have hcomm : M * entries z.1 - entries z.1 * M = entries z.2 * P :=
      sub_eq_zero.mp hv.2
    letI : Nonempty n := ⟨i₀⟩
    have hs : SLRadical M P (entries z.1) (entries z.2) :=
      (slRadical_iff_equations M P _ _).mpr
        ⟨htrace _ _ hv.1 hcomm, hv.1, 0, by simpa using hcomm⟩
    exact ⟨⟨z, hs⟩, (boundedSLScalar_zero_iff M P hM hP i₀ d ⟨z, hs⟩).mpr hv.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (matrixPairEquiv K (BoundedPoly K d) n m).right_inv z.val.val
  right_inv v := by
    apply Subtype.ext
    exact (matrixPairEquiv K (BoundedPoly K d) n m).left_inv v.val
  map_add' z w := by
    apply Subtype.ext
    exact (matrixPairEquiv K (BoundedPoly K d) n m).symm.map_add z.val.val w.val.val
  map_smul' a z := by
    apply Subtype.ext
    exact (matrixPairEquiv K (BoundedPoly K d) n m).symm.map_smul a z.val.val

theorem slHilbert_eq_gl_add_scalar_range
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P * X = 0 → M * X - X * M = U * P → Matrix.trace X = 0) :
    slHilbert M P d = Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) +
      Module.finrank K (LinearMap.range (boundedSLScalar M P hM hP i₀ d)) := by
  letI : Module.Finite K (boundedSLKernel M P d) :=
    Module.Finite.of_injective (boundedSLKernel M P d).subtype Subtype.val_injective
  have rank_nullity (f : boundedSLKernel M P d →ₗ[K] BoundedPoly K (d + 1)) :
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
        Module.finrank K (boundedSLKernel M P d) :=
    @LinearMap.finrank_range_add_finrank_ker K (boundedSLKernel M P d) inferInstance
      inferInstance inferInstance (BoundedPoly K (d + 1)) inferInstance inferInstance inferInstance f
  have hh := rank_nullity (boundedSLScalar M P hM hP i₀ d)
  rw [(boundedSLScalarKernelEquiv M P hM hP i₀ d htrace).finrank_eq] at hh
  exact hh.symm.trans (Nat.add_comm _ _)

omit [DecidableEq m] in
theorem boundedSLScalar_surjective_of_lifts
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (hlift : ∀ c : K[X], c.natDegree ≤ d + 1 →
      ∃ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
        DegreeBound X d ∧ DegreeBound U d ∧ SLRadical M P X U ∧
          M * X - X * M = U * P + c • 1) :
    Function.Surjective (boundedSLScalar M P hM hP i₀ d) := by
  intro c
  obtain ⟨X, U, hX, hU, hs, hc⟩ := hlift c.val (boundedPoly_degree _ c)
  refine ⟨⟨(boundedMatrixOf X hX, boundedMatrixOf U hU), hs⟩, ?_⟩
  apply Subtype.ext
  change (M * X - X * M - U * P) i₀ i₀ = c.val
  rw [hc, add_sub_cancel_left]
  simp

theorem slHilbert_eq_gl_add_of_scalar_lifts
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P * X = 0 → M * X - X * M = U * P → Matrix.trace X = 0)
    (hlift : ∀ c : K[X], c.natDegree ≤ d + 1 →
      ∃ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
        DegreeBound X d ∧ DegreeBound U d ∧ SLRadical M P X U ∧
          M * X - X * M = U * P + c • 1) :
    slHilbert M P d =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) + (d + 2) := by
  rw [slHilbert_eq_gl_add_scalar_range M P hM hP i₀ d htrace,
    LinearMap.range_eq_top.mpr (boundedSLScalar_surjective_of_lifts M P hM hP i₀ d hlift),
    finrank_top, boundedPoly_finrank]

theorem slHilbert_eq_gl_of_scalar_obstruction
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P * X = 0 → M * X - X * M = U * P → Matrix.trace X = 0)
    (hscalar : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]),
      DegreeBound X d → DegreeBound U d → SLRadical M P X U →
        M * X - X * M = U * P + c • 1 → c = 0) :
    slHilbert M P d =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) := by
  have hz : boundedSLScalar M P hM hP i₀ d = 0 := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    have hr := boundedSLScalar_residual M P hM hP i₀ d z
    apply hscalar (entries z.val.1) (entries z.val.2) _
      (entries_degree z.val.1) (entries_degree z.val.2) z.property
    change M * entries z.val.1 - entries z.val.1 * M - entries z.val.2 * P = _ at hr
    exact (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)
  rw [slHilbert_eq_gl_add_scalar_range M P hM hP i₀ d htrace, hz]
  simp

variable {r : Type*} [Fintype r] [DecidableEq r]

theorem middle_gl_trace_zero
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P) : Matrix.trace X = 0 := by
  obtain ⟨E, hE, _⟩ := middle_sl_forward M P B R hPR hG X U 0 hPX (by simpa using hcomm)
  rw [hE.2.1]
  exact (middle_sl_reconstruct M P B R hPR E 0 hE.1).1

theorem middle_slHilbert_eq_gl_add_scalar_range
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ) :
    slHilbert M P d = Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) +
      Module.finrank K (LinearMap.range (boundedSLScalar M P hM hP i₀ d)) :=
  slHilbert_eq_gl_add_scalar_range M P hM hP i₀ d (middle_gl_trace_zero M P B R hPR hG)

theorem middle_slHilbert_of_scalar_lifts
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (hlift : ∀ c : K[X], c.natDegree ≤ d + 1 →
      ∃ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
        DegreeBound X d ∧ DegreeBound U d ∧ SLRadical M P X U ∧
          M * X - X * M = U * P + c • 1) :
    slHilbert M P d =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) + (d + 2) :=
  slHilbert_eq_gl_add_of_scalar_lifts M P hM hP i₀ d
    (middle_gl_trace_zero M P B R hPR hG) hlift

theorem middle_slHilbert_of_scalar_obstruction
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : r → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
    (hBlead : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (i₀ : n) (d : ℕ)
    (hscalar : ∀ (E : Matrix r m K[X]) (c : K[X]),
      (∀ i j, E i j = 0 ∨ (a i + 1 ≤ d ∧ (E i j).natDegree ≤ d - (a i + 1))) →
        E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 → c = 0) :
    slHilbert M P d =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) := by
  letI : Nonempty n := ⟨i₀⟩
  apply slHilbert_eq_gl_of_scalar_obstruction M P hM hP i₀ d
    (middle_gl_trace_zero M P B R hPR hG)
  intro X U c hX _ hs hc
  have hPX := ((slRadical_iff_equations M P X U).mp hs).2.1
  obtain ⟨E, hE, _⟩ := middle_sl_forward M P B R hPR hG X U c hPX hc
  apply hscalar E c _ hE.1
  apply (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E a d
    hB hBlead hP hPlead).mp
  change DegreeBound (middleSLX P B E) d
  rw [← hE.2.1]
  exact hX

end FD56
