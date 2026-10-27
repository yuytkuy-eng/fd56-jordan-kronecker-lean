/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleGLRoot
import FD56.Stabilizer.GenericDivisibleGLDeterminant
import FD56.Stabilizer.ObservableRadical
import FD56.Stabilizer.SLTraceChart

/-! The trace functional annihilates every evaluated kernel in the divisible GL family. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem observable_gl_kirillov_kernel_trace_zero
    {K n m : Type*} [Field K] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K) (P : Matrix m n K) (q : ℕ)
    (hq : Module.finrank K (unobservableSpace M P q)=0)
    (z : SLInput n m → K) (hz : glKirillovMatrix M P *ᵥ z=0) :
    slInputTrace K K z=0 := by
  have he := (glKirillovMatrix_kernel_iff M P z).mp hz
  let w : glStabilizerSpace M P :=
    ⟨matrixPairEquiv K K n m z,(glEquationMatrix_field_kernel_iff M P z).mp he⟩
  exact observable_stabilizer_trace_zero M P q hq w

variable {K L : Type*} {m : Type} [Field K] [Field L] [Fintype m] [DecidableEq m]

theorem generic_divisible_gl_kernel_trace_zero (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L)
    (x : L) (z : SLInput (Fin (q+1) × m) m → L)
    (hz : ((glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map
        (Polynomial.eval₂RingHom φ x)) *ᵥ z=0) :
    slInputTrace L L z=0 := by
  let ev := Polynomial.eval₂RingHom φ x
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  by_cases hx : (observabilityMatrix M P (q+1)).det.eval₂ φ x=0
  · obtain ⟨_,_,hnext⟩ := generic_divisible_observability_root_profile q hm φ x hx
    apply observable_gl_kirillov_kernel_trace_zero (M.map ev) (P.map ev) (q+2) hnext z
    simpa only [glKirillovMatrix_map] using hz
  · have hd : ((glKirillovMatrix M P).map ev).det≠0 := by
      have he := ev.map_det (glKirillovMatrix M P)
      change ev (glKirillovMatrix M P).det=((glKirillovMatrix M P).map ev).det at he
      rw [← he, generic_divisible_gl_kirillov_determinant,map_pow]
      exact pow_ne_zero _ hx
    have hzero : z=0 := Matrix.eq_zero_of_mulVec_eq_zero hd hz
    rw [hzero,map_zero]

end FD56
