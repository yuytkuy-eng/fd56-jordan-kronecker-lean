/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.StructuredLeading

/-! The structured construction gives the Hilbert function of the actual GL
equations once the auxiliary bases satisfy the stated rank and degree tests. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem structured_gl_kernel_hilbert {K F n m r s : Type*}
    [Field K] [IsAlgClosed K] [Field F]
    [Fintype n] [Fintype m] [Fintype r] [Fintype s]
    [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]
    (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P) (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hO : Function.Injective (Matrix.mulVec
      (show Matrix n (Fin (q + 1) × m) K from fun y im =>
        (matrixCoeff P 1 * matrixCoeff M 1 ^ im.1.val) im.2 y)))
    (hpoint : ∀ x : K, Function.Injective
      ((structuredXColumns M V H q).map (Polynomial.evalRingHom x)).mulVec)
    (hlead : Function.Injective (Matrix.mulVec (fun xy kj =>
      (structuredXColumns M V H q xy kj).coeff (a kj.1 + b kj.2 + q + 1))))
    (hdim : Module.finrank F (glStabilizerSpace (M.map φ) (P.map φ)) =
      Fintype.card r * Fintype.card s) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ kj : r × s, (d + 1 - (a kj.1 + b kj.2 + q + 1)) := by
  have hrel := structuredCoefficientRows_relation M P H D T q hzero hstep hend
  have hD := structured_coefficients_degree M P D T q b hM hP hT hrel hO
  have hH := structured_rows_degree M P H D T q b hM hP hstep hend hD hT
  apply polynomial_kernel_hilbert_function φ hφ (glEquationMatrix M P)
    (structuredColumns M V H D T q) (fun kj => a kj.1 + b kj.2 + q + 1) d
  · exact structuredColumns_gl_equations M P V H D T q hzero hstep hend hobs
  · exact structuredColumns_degree M V H D T q a b hM hV hH hD hT
  · intro x
    exact structuredColumns_point_of_X (Polynomial.evalRingHom x) M V H D T q (hpoint x)
  · rw [glEquationMatrix_map, glEquationMatrix_field_finrank, hdim, Fintype.card_prod]
  · exact structuredColumns_leading_of_X M V H D T q _ hlead

end FD56
