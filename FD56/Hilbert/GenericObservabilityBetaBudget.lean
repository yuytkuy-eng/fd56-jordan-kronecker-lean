/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Hilbert.GenericTerminalDegreeBudget
import FD56.Hilbert.GenericObservabilityBetaTransfer

/-! The second auxiliary degree budget in terms of the state and output dimensions.
The chosen polynomial kernel basis need not be reduced. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m]

theorem generic_observability_actual_beta_finrank (q : ℕ)
    (hwide : q*Fintype.card m<Fintype.card n)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q)))) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m)
        (genericAffineRows K n m) d) =
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose d) := by
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hwide
  exact observability_beta_kernel_finrank q _ _ B R hR
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_observability_row_leading_injective q hwide.le) d

theorem generic_observability_beta_degree_budget (q : ℕ) (hm : 2≤Fintype.card m)
    (hlo : q*Fintype.card m<Fintype.card n) (hhi : Fintype.card n<(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q))))
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees
      (genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose xs) :
    xs.length+(Fintype.card n-q*Fintype.card m)=Fintype.card m ∧
      2*xs.sum=Fintype.card m*q*(q+1)+2*(q+1)*(Fintype.card n-q*Fintype.card m) := by
  let O := observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q
  obtain ⟨s,Bv,a,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hAlpha : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨s,Bv,a,hV,hVL,List.Perm.refl _⟩
  obtain ⟨hl,hs⟩ := generic_observability_kernel_degree_budget (K:=K) q hlo _ hAlpha
  simp only [List.length_ofFn,List.sum_ofFn] at hl hs
  have hBeta : HasMinimalKernelDegrees
      (genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix O Bv).transpose xs := by
    apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
    intro d
    rw [← generic_observability_actual_beta_finrank q hlo Bv d,
      generic_observability_actual_beta_finrank q hlo B d]
    exact (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d
  obtain ⟨hbl,hbs⟩ := generic_terminal_kernel_degree_budget q hm hlo hhi Bv a hV hVL xs hBeta
  simp only [Fintype.card_fin] at hbl hbs
  have hr : Fintype.card n-q*Fintype.card m=s := by omega
  refine ⟨by omega,?_⟩
  rw [hr,hbs]
  nlinarith

end FD56
