/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericNondivisibleGLStructure
import FD56.Hilbert.GenericSLFromKroneckerGL

/-! Every strictly nondivisible generic SL pencil is pure Kronecker.
The exact block count and total minimal degree do not specify each block size. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_nondivisible_sl_kronecker_structure
    (q : ℕ) (hq : 0<q) (i₀ : n)
    (hlo : q*Fintype.card m<Fintype.card n)
    (hhi : Fintype.card n<(q+1)*Fintype.card m) :
    ∃ xs : List ℕ,
      xs.length=(Fintype.card n-q*Fintype.card m)*((q+1)*Fintype.card m-Fintype.card n)+1 ∧
      2*xs.sum+xs.length+1=Fintype.card n*(Fintype.card n+Fintype.card m) ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs := by
  obtain ⟨gs,hgl,hgs,hminGL,hGL⟩ := generic_nondivisible_gl_kronecker_structure (K:=K) q hq hlo hhi
  have hm : 0<Fintype.card m := by
    by_contra h
    have hz : Fintype.card m=0 := by omega
    simp only [hz,Nat.mul_zero] at hhi
    omega
  obtain ⟨xs,hsl,hss,hminSL,hSL⟩ :=
    generic_sl_exists_kronecker_of_gl_kronecker hm i₀ gs hGL hminGL
  exact ⟨xs,by omega,by omega,hminSL,hSL⟩

end FD56
