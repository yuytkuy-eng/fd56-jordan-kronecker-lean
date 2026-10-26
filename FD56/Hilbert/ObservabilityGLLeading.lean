/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.StructuredLeading
import FD56.LinearAlgebra.DualBasis

/-! Leading independence for structured GL columns from actual observability
annihilation and the leading ranks of the two auxiliary bases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

omit [Fintype m] [DecidableEq m] [DecidableEq r] in
theorem observability_terminal_restriction_injective
    (M : Matrix n n K) (P : Matrix m n K) (V : Matrix n r K) (q : ℕ)
    (hV : Function.Injective V.mulVec)
    (hzero : ∀ i < q, P * M ^ i * V = 0)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec) :
    Function.Injective (P * M ^ q * V).mulVec := by
  intro c d h
  apply hV
  apply hO
  funext ix
  rcases ix with ⟨i,x⟩
  change ((P * M ^ i.val) *ᵥ (V *ᵥ c)) x = ((P * M ^ i.val) *ᵥ (V *ᵥ d)) x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  by_cases hi : i.val < q
  · rw [hzero i.val hi, Matrix.zero_mulVec, Matrix.zero_mulVec]
  · have hiq : i.val = q := by omega
    rw [hiq]
    exact congrFun h x

omit [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r] in
theorem observability_kernel_leading_annihilation
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (q : ℕ) (a : r → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hzero : ∀ i < q, P * M ^ i * V = 0) :
    ∀ i < q, matrixCoeff P 1 * matrixCoeff M 1 ^ i *
      (show Matrix n r K from fun x k => (V x k).coeff (a k)) = 0 := by
  intro i hi
  have hp : DegreeBound (M ^ i) i := by simpa using degreeBound_pow M 1 hM i
  have hPM : DegreeBound (P * M ^ i) (i+1) := by
    simpa only [Nat.add_comm] using degreeBound_mul hP hp
  have hc : matrixCoeff (P * M ^ i) (i+1) = matrixCoeff P 1 * matrixCoeff M 1 ^ i := by
    rw [Nat.add_comm i 1, matrixCoeff_mul P (M ^ i) 1 i hP hp]
    have hpow := matrixCoeff_pow M 1 hM i
    simpa only [Nat.mul_one] using congrArg (fun B => matrixCoeff P 1 * B) hpow
  funext x k
  have he := (matrixCoeff_mul_column (P * M ^ i) V (i+1) a hPM hV x k).2
  rw [hzero i hi, hc] at he
  simpa only [Matrix.zero_apply, Polynomial.coeff_zero] using he.symm

theorem observability_structuredXColumns_leading_injective
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (T : Matrix s m K[X])
    (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hH : ∀ i < q+1, ∀ j y, (H i j y).natDegree ≤ b j+q+1-i)
    (hend : H q = T * P)
    (hzero : ∀ i < q+1, P * M ^ i * V = 0)
    (hVL : Function.Injective (Matrix.mulVec (fun x k => (V x k).coeff (a k))))
    (hTL : Function.Injective (Matrix.mulVec (fun y j => (T j y).coeff (b j))))
    (hPL : Function.Surjective (matrixCoeff P 1).mulVec)
    (hO : Function.Injective (Matrix.mulVec (fun (ij : Fin (q+2) × m) x =>
      (observabilityMatrix M P (q+2) ij x).coeff (ij.1.val+1)))) :
    Function.Injective (Matrix.mulVec (fun xy kj =>
      (structuredXColumns M V H q xy kj).coeff (a kj.1+b kj.2+q+1))) := by
  let V₀ : Matrix n r K := fun x k => (V x k).coeff (a k)
  let T₀ : Matrix s m K := fun j y => (T j y).coeff (b j)
  let H₀ : ℕ → Matrix s n K := fun i j y => (H i j y).coeff (b j+q+1-i)
  let M₀ := matrixCoeff M 1
  let P₀ := matrixCoeff P 1
  have hobs : ∀ i < q+1, P₀ * M₀ ^ i * V₀ = 0 :=
    observability_kernel_leading_annihilation M P V (q+1) a hM hP hV hzero
  have hO₀ : Function.Injective (observabilityMatrix M₀ P₀ (q+2)).mulVec := by
    have he : (fun (ij : Fin (q+2) × m) x =>
        (observabilityMatrix M P (q+2) ij x).coeff (ij.1.val+1)) =
        observabilityMatrix M₀ P₀ (q+2) := by
      funext ij x
      exact (observability_polynomial_degree_top M P (q+2) hM hP ij x).2
    rwa [he] at hO
  have hF := observability_terminal_restriction_injective M₀ P₀ V₀ (q+1) hVL hobs hO₀
  have hTs : Function.Surjective T₀.mulVec := matrix_surjective_of_transpose_injective T₀ hTL
  have hTPs : Function.Surjective (T₀ * P₀).mulVec := by
    intro z
    obtain ⟨y,hy⟩ := hTs z
    obtain ⟨x,hx⟩ := hPL y
    refine ⟨x, ?_⟩
    rw [← Matrix.mulVec_mulVec, hx, hy]
  obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hTPs
  have hHq : H₀ q = T₀ * P₀ := by
    funext j x
    dsimp only [H₀]
    rw [hend, show b j+q+1-q = b j+1 by omega]
    simp only [Matrix.mul_apply, Polynomial.finset_sum_coeff, T₀, P₀, matrixCoeff]
    apply Finset.sum_congr rfl
    intro y _
    exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hT j y) (hP y x)
  apply structuredXColumns_leading_injective M V H q a b hM hV hH P₀ hobs
    (fun C D h => by
      funext x y
      exact congrFun (hF (funext fun z => congrFun (congrFun h z) y)) x) B
  change H₀ q * B = 1
  rw [hHq, hB]

theorem observability_structuredColumns_leading_injective
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hH : ∀ i < q+1, ∀ j y, (H i j y).natDegree ≤ b j+q+1-i)
    (hend : H q = T * P)
    (hzero : ∀ i < q+1, P * M ^ i * V = 0)
    (hVL : Function.Injective (Matrix.mulVec (fun x k => (V x k).coeff (a k))))
    (hTL : Function.Injective (Matrix.mulVec (fun y j => (T j y).coeff (b j))))
    (hPL : Function.Surjective (matrixCoeff P 1).mulVec)
    (hO : Function.Injective (Matrix.mulVec (fun (ij : Fin (q+2) × m) x =>
      (observabilityMatrix M P (q+2) ij x).coeff (ij.1.val+1)))) :
    Function.Injective (Matrix.mulVec (fun xy kj =>
      (structuredColumns M V H D T q xy kj).coeff (a kj.1+b kj.2+q+1))) :=
  structuredColumns_leading_of_X M V H D T q _
    (observability_structuredXColumns_leading_injective M P V H T q a b
      hM hP hV hT hH hend hzero hVL hTL hPL hO)

end FD56
