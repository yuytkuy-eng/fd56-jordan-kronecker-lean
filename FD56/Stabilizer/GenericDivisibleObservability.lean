/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.BlockScalarObservability

/-! The generic square observability determinant has full degree and simple roots. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem generic_divisible_observability_separable (K m : Type*)
    [Field K] [Fintype m] [DecidableEq m] (q : ℕ) :
    let A := observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q
    A.det.natDegree = (∑ i : Fin q × m, (i.1.val + 1)) ∧ A.det.Separable := by
  let L := FractionRing (MvPolynomial (Fin q × m) K)
  let ι : MvPolynomial (Fin q × m) K →+* L := algebraMap _ _
  let a : Fin q × m → L := fun i => ι (MvPolynomial.X i)
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have ha (b : m) : Function.Injective (fun i => a (i,b)) := by
    intro i j h
    exact congrArg Prod.fst (MvPolynomial.X_injective (hι h))
  exact generic_selected_observability_separable_of_witness
    (ι.comp MvPolynomial.C) (blockScalarState a) (blockScalarOutput a)
    (blockScalarState_degree a) (blockScalarOutput_degree a)
    (fun i => i.1.val) Prod.snd
    (blockScalarObservability_natDegree a ha) (blockScalarObservability_separable ι hι)

theorem generic_divisible_observability_nonzero (K m : Type*)
    [Field K] [Fintype m] [DecidableEq m] (q : ℕ) :
    (observabilityMatrix (genericAffineSquare K (Fin q × m) m)
      (genericAffineRows K (Fin q × m) m) q).det ≠ 0 :=
  (generic_divisible_observability_separable K m q).2.ne_zero

end FD56
