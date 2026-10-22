/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleGL

/-! Weighted degree bounds for the middle SL parametrization. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] in
theorem middle_product_columns_leading_injective
    (V : Matrix n r K[X]) (P : Matrix m n K[X]) (a : r → ℕ)
    (hV : ∀ x i, (V x i).natDegree ≤ a i)
    (hVlead : Function.Injective (Matrix.mulVec (fun x i => (V x i).coeff (a i))))
    (hP : DegreeBound P 1)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) :
    Function.Injective (Matrix.mulVec (fun (xy : n × n) (ij : r × m) =>
      (V xy.1 ij.1 * P ij.2 xy.2).coeff (a ij.1 + 1))) := by
  have hcoeff (xy : n × n) (ij : r × m) :
      (V xy.1 ij.1 * P ij.2 xy.2).coeff (a ij.1 + 1) =
        (V xy.1 ij.1).coeff (a ij.1) * (P ij.2 xy.2).coeff 1 :=
    Polynomial.coeff_mul_add_eq_of_natDegree_le (hV xy.1 ij.1) (hP ij.2 xy.2)
  simpa only [hcoeff, matrixCoeff] using tensorColumns_injective
    (show Matrix n r K from fun x i => (V x i).coeff (a i)) (matrixCoeff P 1)
    hVlead hPlead

omit [DecidableEq n] [DecidableEq m] in
theorem middle_one_column_product_leading_injective
    (V : Matrix n (Fin 1) K[X]) (P : Matrix m n K[X]) (a : ℕ)
    (hV : ∀ x i, (V x i).natDegree ≤ a)
    (hVlead : Function.Injective (Matrix.mulVec (fun x i => (V x i).coeff a)))
    (hP : DegreeBound P 1)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) :
    Function.Injective (Matrix.mulVec (fun (xy : n × n) j =>
      (V xy.1 0 * P j xy.2).coeff (a + 1))) := by
  have hi := middle_product_columns_leading_injective V P (fun _ => a) hV hVlead hP hPlead
  intro c d h
  have hh : Matrix.mulVec (fun (xy : n × n) (ij : Fin 1 × m) =>
        (V xy.1 ij.1 * P ij.2 xy.2).coeff (a + 1)) (fun ij => c ij.2) =
      Matrix.mulVec (fun (xy : n × n) (ij : Fin 1 × m) =>
        (V xy.1 ij.1 * P ij.2 xy.2).coeff (a + 1)) (fun ij => d ij.2) := by
    funext xy
    simpa only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_one] using
      congrFun h xy
  have he := hi hh
  funext j
  exact congrFun he (0, j)

omit [Fintype n] [DecidableEq n] in
theorem middle_one_column_product_single
    (V : Matrix n (Fin 1) K[X]) (P : Matrix m n K[X]) (j : m) :
    V * (show Matrix (Fin 1) m K[X] from fun _ => Pi.single j 1) * P =
      (fun x y => V x 0 * P j y) := by
  apply Matrix.ext
  intro x y
  simp [Matrix.mul_apply, Fin.sum_univ_one, Pi.single_apply]

omit [Fintype n] [DecidableEq n] in
theorem middle_one_column_single_degree
    (V : Matrix n (Fin 1) K[X]) (P : Matrix m n K[X]) (a : ℕ)
    (hV : ∀ x i, (V x i).natDegree ≤ a) (hP : DegreeBound P 1) (j : m) :
    DegreeBound (V * (show Matrix (Fin 1) m K[X] from fun _ => Pi.single j 1) * P) (a + 1) := by
  rw [middle_one_column_product_single]
  intro x y
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hV x 0) (hP j y))

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] in
theorem middle_product_degree_iff
    (V : Matrix n r K[X]) (P : Matrix m n K[X]) (E : Matrix r m K[X])
    (a : r → ℕ) (d : ℕ)
    (hV : ∀ x i, (V x i).natDegree ≤ a i)
    (hVlead : Function.Injective (Matrix.mulVec (fun x i => (V x i).coeff (a i))))
    (hP : DegreeBound P 1)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) :
    DegreeBound (V * E * P) d ↔
      ∀ i j, E i j = 0 ∨ (a i + 1 ≤ d ∧ (E i j).natDegree ≤ d - (a i + 1)) := by
  let Z : Matrix (n × n) (r × m) K[X] := fun xy ij => V xy.1 ij.1 * P ij.2 xy.2
  have hZ : ∀ xy ij, (Z xy ij).natDegree ≤ a ij.1 + 1 := by
    intro xy ij
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hV xy.1 ij.1) (hP ij.2 xy.2))
  have hcoeff (xy : n × n) (ij : r × m) :
      (Z xy ij).coeff (a ij.1 + 1) =
        (V xy.1 ij.1).coeff (a ij.1) * (P ij.2 xy.2).coeff 1 :=
    Polynomial.coeff_mul_add_eq_of_natDegree_le (hV xy.1 ij.1) (hP ij.2 xy.2)
  have hlead : Function.Injective (Matrix.mulVec (fun xy ij =>
      (Z xy ij).coeff (a ij.1 + 1))) := by
    simpa only [hcoeff, matrixCoeff] using tensorColumns_injective
      (show Matrix n r K from fun x i => (V x i).coeff (a i)) (matrixCoeff P 1)
      hVlead hPlead
  have hmul : Z *ᵥ (fun ij => E ij.1 ij.2) = fun xy => (V * E * P) xy.1 xy.2 :=
    tensorColumns_mulVec V P (fun ij => E ij.1 ij.2)
  have hiff := polynomial_combination_degree_iff Z (fun ij => a ij.1 + 1)
    (fun ij => E ij.1 ij.2) d hZ hlead
  constructor
  · intro hb i j
    apply hiff.mp _ (i, j)
    intro xy
    rw [hmul]
    exact hb xy.1 xy.2
  · intro hb x y
    have hh := hiff.mpr (fun ij => hb ij.1 ij.2) (x, y)
    rw [hmul] at hh
    exact hh

omit [DecidableEq n] [DecidableEq m] [Fintype r] in
theorem middle_scalar_degree_of_weighted
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (E : Matrix r m K[X]) (a : r → ℕ) (c : K[X]) (i₀ : r) (d : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (V x i).natDegree ≤ a i)
    (hE : ∀ i j, E i j = 0 ∨ (a i + 1 ≤ d ∧ (E i j).natDegree ≤ d - (a i + 1)))
    (hrel : E * (P * M * V) = (-c) • (1 : Matrix r r K[X])) :
    c.natDegree ≤ d + 1 := by
  have hG : ∀ x i, ((P * M * V) x i).natDegree ≤ a i + 2 := by
    intro x i
    have hh := (matrixCoeff_mul_column (P * M) V 2 a (degreeBound_mul hP hM) hV x i).1
    omega
  have hb : ((E * (P * M * V)) i₀ i₀).natDegree ≤ d + 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    change (E i₀ j * (P * M * V) j i₀).natDegree ≤ d + 1
    rcases hE i₀ j with hz | ⟨ha, he⟩
    · simp [hz]
    · have hh := Polynomial.natDegree_mul_le (p := E i₀ j) (q := (P * M * V) j i₀)
      have hg := hG j i₀
      omega
  rw [hrel] at hb
  simpa using hb

omit [DecidableEq n] [DecidableEq m] in
theorem middle_scalar_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (E : Matrix r m K[X]) (a : r → ℕ) (c : K[X]) (i₀ : r) (d : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (V x i).natDegree ≤ a i)
    (hVlead : Function.Injective (Matrix.mulVec (fun x i => (V x i).coeff (a i))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (hX : DegreeBound (V * E * P) d)
    (hrel : E * (P * M * V) = (-c) • (1 : Matrix r r K[X])) :
    c.natDegree ≤ d + 1 :=
  middle_scalar_degree_of_weighted M P V E a c i₀ d hM hP hV
    ((middle_product_degree_iff V P E a d hV hVlead hP hPlead).mp hX) hrel

omit [DecidableEq m] in
theorem middle_translation_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]) (d : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (hX : DegreeBound X d) (hc : c.natDegree ≤ d + 1)
    (hcomm : M * X - X * M = U * P + c • (1 : Matrix n n K[X])) :
    DegreeBound U d := by
  have hMX : DegreeBound (M * X) (d + 1) := by
    simpa only [Nat.add_comm] using degreeBound_mul hM hX
  have hXM : DegreeBound (X * M) (d + 1) := degreeBound_mul hX hM
  have hscalar : DegreeBound (c • (1 : Matrix n n K[X])) (d + 1) := by
    intro i j
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using hc
    · simp [Matrix.one_apply, hij]
  have hUP : U * P = (M * X - X * M) - c • (1 : Matrix n n K[X]) := by
    rw [hcomm, add_sub_cancel_right]
  have hb : DegreeBound (U * P) (d + 1) := by
    rw [hUP]
    exact degreeBound_sub (degreeBound_sub hMX hXM) hscalar
  have hcoord := row_coordinates_degree_bound P U (fun _ => 1) (fun _ => d + 1)
    hP hPlead hb
  intro i j
  rcases hcoord i j with hz | ⟨_, hj⟩
  · simp [hz]
  · simpa using hj

end FD56
