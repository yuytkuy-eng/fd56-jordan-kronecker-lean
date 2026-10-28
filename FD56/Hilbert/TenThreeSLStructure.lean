/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSLFromKroneckerGL
import FD56.Hilbert.DepthThreeTenThreeFamily

/-! Pure SL Kronecker structure for the repeated (10,3) family. The block
count and total degree are exact; individual minimal degrees remain unspecified. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K t : Type*} [Field K] [CharZero K]
  [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_ten_three_repeated_sl_kronecker_structure (i₀ : Fin 10 × t) :
    ∃ xs : List ℕ, xs.length=2*Fintype.card t^2+1 ∧ xs.sum+1=64*Fintype.card t^2 ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 10 × t) (Fin 3 × t)) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 10 × t) (Fin 3 × t)) i₀) xs := by
  have hmin := generic_ten_three_repeated_gl_minimal_degrees (K:=K) (t:=t)
  have hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 10 × t) (Fin 3 × t)))
      (List.replicate (2*Fintype.card t^2) 32) := by
    apply glKirillovMatrix_kronecker _ _ _
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hmin
    simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
      List.map_replicate,List.sum_replicate,smul_eq_mul]
    ring
  obtain ⟨xs,hl,hs,hxs,hcanon⟩ := generic_sl_exists_kronecker_of_gl_kronecker
    (by simp only [Fintype.card_prod,Fintype.card_fin]; exact Nat.mul_pos (by decide) Fintype.card_pos)
    i₀ _ hGL hmin
  refine ⟨xs,by simpa using hl,?_,hxs,hcanon⟩
  simpa only [List.sum_replicate,smul_eq_mul,
    show 2*Fintype.card t^2*32=64*Fintype.card t^2 by ring] using hs

end FD56
