/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.WeightedSurjectivity
import FD56.Stabilizer.MiddleSLReduction
import FD56.Stabilizer.MiddleSLDegrees

/-! Row coefficient surjectivity realizes every scalar correction with
the required bounds on the full SL radical. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem middle_sl_scalar_lift
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (a : r → ℕ) (d : ℕ) (ha : ∀ i, a i + 1 ≤ d)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
    (hVlead : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (hs : ∀ i, Function.Surjective (weightedCoefficientMatrix
      (P * M * polynomialKernelBasisMatrix P B).transpose
      (fun _ => d - (a i + 1)) (fun j => d - (a i + 1) + a j + 2)).mulVec)
    (c : K[X]) (hc : c.natDegree ≤ d + 1) :
    ∃ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      DegreeBound X d ∧ DegreeBound U d ∧ Matrix.trace X = 0 ∧
      P * X = 0 ∧ M * X - X * M = U * P + c • 1 := by
  let V := polynomialKernelBasisMatrix P B
  let G := P * M * V
  have hG : ∀ x j, (G x j).natDegree ≤ a j + 2 := by
    intro x j
    change ((P * M * V) x j).natDegree ≤ a j + 2
    have hh := (matrixCoeff_mul_column (P * M) V 2 a (degreeBound_mul hP hM) hV x j).1
    omega
  have hlift (i : r) : ∃ e : m → K[X],
      (∀ j, (e j).natDegree ≤ d - (a i + 1)) ∧
      G.transpose *ᵥ e = fun j => if i = j then -c else 0 := by
    apply weighted_coefficient_surjective_lift G.transpose
      (fun _ => d - (a i + 1)) (fun j => d - (a i + 1) + a j + 2)
    · intro j x
      have := hG x j
      change (G x j).natDegree + _ ≤ _
      omega
    · exact hs i
    · intro j
      by_cases hij : i = j
      · subst j
        simp only [ite_true, Polynomial.natDegree_neg]
        have := ha i
        omega
      · simp [hij]
  choose E hE hEG using hlift
  have hrel : (show Matrix r m K[X] from E) * G = (-c) • (1 : Matrix r r K[X]) := by
    funext i j
    have hh := congrFun (hEG i) j
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      mul_comm, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] using hh
  let X := middleSLX P B E
  let U := middleSLTranslation M P B R E c
  have hX : DegreeBound X d := by
    apply (middle_product_degree_iff V P E a d hV hVlead hP hPlead).mpr
    intro i j
    exact Or.inr ⟨ha i, hE i j⟩
  have he := middle_sl_reconstruct M P B R hPR E c hrel
  have hU : DegreeBound U d := middle_translation_degree M P X U c d
    hM hP hPlead hX hc he.2.2
  exact ⟨X, U, hX, hU, he⟩

end FD56
