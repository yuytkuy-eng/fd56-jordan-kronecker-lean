/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLLeading
import FD56.Hilbert.GenericObservabilityLeading
import FD56.Hilbert.ObservabilityTerminalInverse
import FD56.Stabilizer.GenericObservabilityLeftInverse
import FD56.Stabilizer.GenericWideObservabilityRightInverse

/-! The terminal kernel restriction has its expected column degrees,
independent leading columns, and a polynomial left inverse. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m r : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem observability_terminal_degree_and_leading
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (a : r → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ i j, (V i j).natDegree≤a j) (hzero : observabilityMatrix M P q*V=0)
    (hVL : Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff (a j))))
    (hO : Function.Injective (observabilityMatrix (matrixCoeff M 1) (matrixCoeff P 1) (q+1)).mulVec) :
    (∀ i j, ((P*M^q*V) i j).natDegree≤a j+q+1) ∧
      Function.Injective (Matrix.mulVec (fun i j => ((P*M^q*V) i j).coeff (a j+q+1))) := by
  have hp : DegreeBound (M^q) q := by simpa using degreeBound_pow M 1 hM q
  have hPM : DegreeBound (P*M^q) (q+1) := by
    simpa only [Nat.add_comm] using degreeBound_mul hP hp
  have hc : matrixCoeff (P*M^q) (q+1)=matrixCoeff P 1*(matrixCoeff M 1)^q := by
    rw [Nat.add_comm q 1,matrixCoeff_mul P (M^q) 1 q hP hp]
    have hpow := matrixCoeff_pow M 1 hM q
    simpa only [Nat.mul_one] using congrArg (fun Z => matrixCoeff P 1*Z) hpow
  have hz (i : ℕ) (hi : i<q) : P*M^i*V=0 := by
    funext x j
    exact congrFun (congrFun hzero (⟨i,hi⟩,x)) j
  have han := observability_kernel_leading_annihilation M P V q a hM hP hV hz
  have hf := observability_terminal_restriction_injective (matrixCoeff M 1) (matrixCoeff P 1)
    (show Matrix n r K from fun i j => (V i j).coeff (a j)) q hVL han hO
  refine ⟨?_,?_⟩
  · intro i j
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (matrixCoeff_mul_column (P*M^q) V (q+1) a hPM hV i j).1
  · have he : (fun i j => ((P*M^q*V) i j).coeff (a j+q+1))=
        matrixCoeff P 1*(matrixCoeff M 1)^q*
          (show Matrix n r K from fun i j => (V i j).coeff (a j)) := by
      funext i j
      simpa only [hc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (matrixCoeff_mul_column (P*M^q) V (q+1) a hPM hV i j).2
    rw [he]
    exact hf

theorem generic_terminal_kernel_left_inverse
    (q : ℕ) (hm : 2≤Fintype.card m)
    (hlo : q*Fintype.card m<Fintype.card n)
    (hhi : Fintype.card n<(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q)))) :
    ∃ L : Matrix r m (AffineCoefficientField K (MatrixParameters n m))[X],
      L*(genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B)=1 := by
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨U,hU⟩ := generic_affine_observability_left_inverse (K:=K) (q+1) hm hhi
  exact observability_terminal_kernel_left_inverse q _ _ B R hR U hU

theorem generic_terminal_kernel_degree_and_leading
    (q : ℕ) (hhi : Fintype.card n≤(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q))))
    (a : r → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤a j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (a j)))) :
    (∀ i j, ((genericAffineRows K n m*(genericAffineSquare K n m)^q*
      polynomialKernelBasisMatrix _ B) i j).natDegree≤a j+q+1) ∧
    Function.Injective (Matrix.mulVec (fun i j =>
      ((genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix _ B) i j).coeff (a j+q+1))) :=
  observability_terminal_degree_and_leading q _ _ _ a
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    hV (polynomialKernelBasisMatrix_mul _ B) hVL
    (generic_tall_observability_leading_pair_injective (q+1) hhi)

end FD56
