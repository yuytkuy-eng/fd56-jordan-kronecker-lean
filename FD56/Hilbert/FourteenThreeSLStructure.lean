/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSLFromKroneckerGL
import FD56.Hilbert.FourteenThreeKronecker

/-! Pure SL Kronecker structure for the repeated (14,3) family. The block
count and total degree are exact; individual minimal degrees remain unspecified. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K t : Type*} [Field K] [CharZero K]
  [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_fourteen_three_repeated_sl_kronecker_structure (i₀ : Fin 14 × t) :
    ∃ xs : List ℕ, xs.length=2*Fintype.card t^2+1 ∧ xs.sum+1=118*Fintype.card t^2 ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 14 × t) (Fin 3 × t)) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K (Fin 14 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 14 × t) (Fin 3 × t)) i₀) xs := by
  obtain ⟨xs,hl,hs,hxs,hcanon⟩ := generic_sl_exists_kronecker_of_gl_kronecker (K:=K)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; exact Nat.mul_pos (by decide) Fintype.card_pos)
    i₀ _ (generic_fourteen_three_repeated_gl_kronecker (K:=K) (t:=t))
      (generic_fourteen_three_repeated_gl_minimal_degrees (K:=K) (t:=t))
  refine ⟨xs,by simpa using hl,?_,hxs,hcanon⟩
  simpa only [List.sum_replicate,smul_eq_mul,
    show 2*Fintype.card t^2*59=118*Fintype.card t^2 by ring] using hs

end FD56
