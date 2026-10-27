/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericObservabilitySeparable

/-! Independent scalar-output blocks give a separable square observability witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def blockScalarPoleEmbedding {q : ℕ} {m : Type*} (b : m) : Fin q ↪ Fin q × m :=
  ⟨fun i => (i,b), fun _ _ h => congrArg Prod.fst h⟩

def blockScalarPoleSupport {q : ℕ} {m : Type*} (s : m × scalarObservabilityPoleIndex q) :
    Finset (Fin q × m) :=
  (scalarObservabilityPoleSupport s.2).map (blockScalarPoleEmbedding s.1)

theorem scalarObservabilityPoleSupport_nonempty {q : ℕ} (s : scalarObservabilityPoleIndex q) :
    (scalarObservabilityPoleSupport s).Nonempty := by
  rcases s with i | ⟨i,j⟩ <;> simp [scalarObservabilityPoleSupport]

theorem blockScalarPoleSupport_injective (q : ℕ) (m : Type*) :
    Function.Injective (@blockScalarPoleSupport q m) := by
  classical
  rintro ⟨a,s⟩ ⟨b,t⟩ h
  obtain ⟨i,hi⟩ := scalarObservabilityPoleSupport_nonempty s
  have hm : (i,a) ∈ blockScalarPoleSupport (a,s) := by
    exact Finset.mem_map.mpr ⟨i,hi,rfl⟩
  rw [h] at hm
  obtain ⟨j,hj,he⟩ := Finset.mem_map.mp hm
  have hab : b = a := congrArg Prod.snd he
  subst b
  have hst : scalarObservabilityPoleSupport s = scalarObservabilityPoleSupport t :=
    Finset.map_injective (blockScalarPoleEmbedding a) h
  have hs := scalarObservabilityPoleSupport_injective q hst
  subst t
  rfl

theorem independent_block_scalar_poles_injective {K F m : Type*}
    [Field K] [Field F] (q : ℕ)
    (ι : MvPolynomial (Fin q × m) K →+* F) (hι : Function.Injective ι) :
    Function.Injective (fun s : m × scalarObservabilityPoleIndex q =>
      scalarObservabilityPoleValue (fun i => ι (MvPolynomial.X (i,s.1))) s.2) := by
  classical
  intro s t h
  apply blockScalarPoleSupport_injective q m
  apply mvPolynomial_subset_sum_injective (R := K)
  apply hι
  have he (x : m × scalarObservabilityPoleIndex q) :
      ι (∑ z ∈ blockScalarPoleSupport x, (MvPolynomial.X z : MvPolynomial (Fin q × m) K)) =
        -scalarObservabilityPoleValue (fun i => ι (MvPolynomial.X (i,x.1))) x.2 := by
    simp [blockScalarPoleSupport, blockScalarPoleEmbedding, scalarObservabilityPoleValue]
  rw [he,he]
  exact congrArg Neg.neg h

variable {K m : Type*} [Field K] [Fintype m] [DecidableEq m] {q : ℕ}

def blockScalarState (a : Fin q × m → K) : Matrix (Fin q × m) (Fin q × m) K[X] :=
  Matrix.diagonal (fun j => C (a j) * X + C (a j ^ 2))

def blockScalarOutput (a : Fin q × m → K) : Matrix m (Fin q × m) K[X] :=
  fun b j => if b = j.2 then X + C (a j) else 0

omit [Fintype m] in
theorem blockScalarState_degree (a : Fin q × m → K) : DegreeBound (blockScalarState a) 1 := by
  intro i j
  by_cases h : i = j
  · subst j
    simp only [blockScalarState, Matrix.diagonal_apply_eq]
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp
  · simp [blockScalarState, Matrix.diagonal_apply_ne _ h]

omit [Fintype m] in
theorem blockScalarOutput_degree (a : Fin q × m → K) : DegreeBound (blockScalarOutput a) 1 := by
  intro i j
  dsimp only [blockScalarOutput]
  split_ifs
  · exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)
  · simp

theorem blockScalarObservability_eq_selected (a : Fin q × m → K) :
    observabilitySelectedMatrix (blockScalarState a) (blockScalarOutput a)
      (fun i => i.1.val) Prod.snd =
      Matrix.blockDiagonal (fun b => scalarDiagonalObservability (fun i => a (i,b))) := by
  funext i j
  simp only [observabilitySelectedMatrix, blockScalarState, Matrix.diagonal_pow,
    Matrix.mul_diagonal, blockScalarOutput, Matrix.blockDiagonal_apply,
    scalarDiagonalObservability]
  by_cases h : i.2 = j.2 <;> simp [h]

theorem blockScalarObservability_natDegree (a : Fin q × m → K)
    (ha : ∀ b, Function.Injective (fun i => a (i,b))) :
    (observabilitySelectedMatrix (blockScalarState a) (blockScalarOutput a)
      (fun i => i.1.val) Prod.snd).det.natDegree = ∑ i : Fin q × m, (i.1.val + 1) := by
  rw [blockScalarObservability_eq_selected, Matrix.det_blockDiagonal]
  rw [Polynomial.natDegree_prod _ _ (by
    intro b _
    rw [scalarDiagonalObservability_factorization]
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr (ha b))
    · apply Finset.prod_ne_zero_iff.mpr
      intro s _
      exact Polynomial.X_sub_C_ne_zero _)]
  simp_rw [scalarDiagonalObservability_natDegree _ (ha _)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem blockScalarObservability_separable {R F : Type*} [Field R] [Field F]
    (ι : MvPolynomial (Fin q × m) R →+* F) (hι : Function.Injective ι) :
    (observabilitySelectedMatrix
      (blockScalarState (fun i => ι (MvPolynomial.X i)))
      (blockScalarOutput (fun i => ι (MvPolynomial.X i)))
      (fun i => i.1.val) Prod.snd).det.Separable := by
  rw [blockScalarObservability_eq_selected, Matrix.det_blockDiagonal]
  simp_rw [scalarDiagonalObservability_factorization]
  rw [Finset.prod_mul_distrib]
  apply Polynomial.Separable.unit_mul
  · rw [← map_prod]
    apply isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j h
    exact congrArg Prod.fst (MvPolynomial.X_injective (hι h))
  · rw [← Fintype.prod_prod_type (fun s : m × scalarObservabilityPoleIndex q =>
      X - C (scalarObservabilityPoleValue (fun i => ι (MvPolynomial.X (i,s.1))) s.2))]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr
      (independent_block_scalar_poles_injective q ι hι)

end FD56
