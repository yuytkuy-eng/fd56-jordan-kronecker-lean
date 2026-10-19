/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialLeading
import FD56.Stabilizer.Krylov
import FD56.Stabilizer.ObservabilityMatrix
import FD56.Hilbert.GLMatrix

/-! Degree bounds and highest coefficients of the structured GL columns.
Observability and a right inverse for the last row block prevent cancellation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K] [Fintype n] [DecidableEq n]

def structuredXColumns (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (q : ℕ) : Matrix (n × n) (r × s) K[X] :=
  fun xy kj => ∑ i ∈ Finset.range (q + 1), (M ^ i * V) xy.1 kj.1 * H i kj.2 xy.2

omit [DecidableEq n] in
theorem structured_rows_degree [Fintype m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (b : s → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P)
    (hD : ∀ i < q + 1, ∀ j y, (D i j y).natDegree ≤ b j + q + 1 - i)
    (hT : ∀ j y, (T j y).natDegree ≤ b j) :
    ∀ i < q + 1, ∀ j y, (H i j y).natDegree ≤ b j + q + 1 - i := by
  intro i hi
  apply Nat.decreasingInduction
    (motive := fun k _ => ∀ j y, (H k j y).natDegree ≤ b j + q + 1 - k) ?_ ?_ (by omega : i ≤ q)
  · intro k hk ih j y
    have hH : ∀ j x, (H (k + 1) j x).natDegree ≤ b j + (q - k) := by
      intro j x
      have hh := ih j x
      omega
    have hDD : ∀ j x, (D (k + 1) j x).natDegree ≤ b j + (q - k) := by
      intro j x
      have hh := hD (k + 1) (by omega) j x
      omega
    have he : H k = H (k + 1) * M - D (k + 1) * P := by
      rw [hstep k hk, add_sub_cancel_right]
    rw [he]
    have hb := (Polynomial.natDegree_sub_le ((H (k + 1) * M) j y) ((D (k + 1) * P) j y)).trans
      (max_le (matrix_mul_row_degree (H (k + 1)) M (fun j => b j + (q - k)) 1 hH hM j y)
        (matrix_mul_row_degree (D (k + 1)) P (fun j => b j + (q - k)) 1 hDD hP j y))
    exact hb.trans (by omega)
  · intro j y
    rw [hend]
    have h := matrix_mul_row_degree T P b 1 hT hP j y
    exact h.trans (by omega)
theorem structuredXColumns_degree_top (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hH : ∀ i < q + 1, ∀ j y, (H i j y).natDegree ≤ b j + q + 1 - i)
    (xy : n × n) (kj : r × s) :
    (structuredXColumns M V H q xy kj).natDegree ≤ a kj.1 + b kj.2 + q + 1 ∧
      (structuredXColumns M V H q xy kj).coeff (a kj.1 + b kj.2 + q + 1) =
        ∑ i ∈ Finset.range (q + 1),
          (matrixCoeff M 1 ^ i *
            (show Matrix n r K from fun x k => (V x k).coeff (a k))) xy.1 kj.1 *
              (H i kj.2 xy.2).coeff (b kj.2 + q + 1 - i) := by
  have hp (i : ℕ) : DegreeBound (M ^ i) i := by
    simpa using degreeBound_pow M 1 hM i
  have hv (i : ℕ) := matrixCoeff_mul_column (M ^ i) V i a (hp i) hV xy.1 kj.1
  have he (i : ℕ) : matrixCoeff (M ^ i) i = matrixCoeff M 1 ^ i := by
    simpa using matrixCoeff_pow M 1 hM i
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hh := hH i hi' kj.2 xy.2
    have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hv i).1 hh)
    have hsum : i + a kj.1 + (b kj.2 + q + 1 - i) = a kj.1 + b kj.2 + q + 1 := by omega
    exact hsum ▸ h
  · simp only [structuredXColumns, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hsum : i + a kj.1 + (b kj.2 + q + 1 - i) = a kj.1 + b kj.2 + q + 1 := by omega
    rw [← hsum, Polynomial.coeff_mul_add_eq_of_natDegree_le (hv i).1 (hH i hi' kj.2 xy.2),
      (hv i).2, he]

theorem structured_leading_map_injective [Fintype m] [Fintype r] [Fintype s]
    [DecidableEq s]
    (M : Matrix n n K) (P : Matrix m n K) (V : Matrix n r K)
    (H : ℕ → Matrix s n K) (q : ℕ)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (hF : Function.Injective (fun C : Matrix r n K => (P * M ^ (q + 1) * V) * C))
    (B : Matrix n s K) (hB : H q * B = 1) :
    Function.Injective (fun C : Matrix r s K =>
      ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) := by
  intro C D h
  have hz : ∑ i ∈ Finset.range (q + 1), M ^ i * V * ((C - D) * H i) = 0 := by
    simpa only [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul,
      Finset.sum_sub_distrib, sub_eq_zero] using h
  have hl := krylov_blocks_independent M V (q + 1) P hobs hF
    (fun i => (C - D) * H i) hz q (Nat.lt_succ_self q)
  have hh := congrArg (fun A => A * B) hl
  change ((C - D) * H q) * B = 0 * B at hh
  rw [Matrix.mul_assoc, hB, Matrix.mul_one, Matrix.zero_mul] at hh
  exact sub_eq_zero.mp hh

omit [Fintype n] [DecidableEq n] in
theorem structured_flat_mulVec [Fintype r] [Fintype s]
    (A : ℕ → Matrix n r K) (H : ℕ → Matrix s n K) (q : ℕ)
    (c : r × s → K) (x y : n) :
    (Matrix.mulVec (fun xy kj => ∑ i ∈ Finset.range (q + 1),
      A i xy.1 kj.1 * H i kj.2 xy.2) c) (x, y) =
      (∑ i ∈ Finset.range (q + 1), A i * (show Matrix r s K from fun k j => c (k,j)) * H i) x y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, Matrix.sum_apply]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem structured_flat_injective [Fintype m] [Fintype r] [Fintype s] [DecidableEq s]
    (M : Matrix n n K) (P : Matrix m n K) (V : Matrix n r K)
    (H : ℕ → Matrix s n K) (q : ℕ)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (hF : Function.Injective (fun C : Matrix r n K => (P * M ^ (q + 1) * V) * C))
    (B : Matrix n s K) (hB : H q * B = 1) :
    Function.Injective (Matrix.mulVec (fun (xy : n × n) (kj : r × s) => ∑ i ∈ Finset.range (q + 1),
      (M ^ i * V) xy.1 kj.1 * H i kj.2 xy.2)) := by
  intro c d h
  have he : (show Matrix r s K from fun k j => c (k,j)) = (fun k j => d (k,j)) := by
    apply structured_leading_map_injective M P V H q hobs hF B hB
    funext x y
    have hh := congrFun h (x,y)
    simpa only [structured_flat_mulVec] using hh
  funext kj
  exact congrFun (congrFun he kj.1) kj.2

theorem structuredXColumns_leading_injective [Fintype m] [Fintype r] [Fintype s]
    [DecidableEq s]
    (M : Matrix n n K[X]) (V : Matrix n r K[X]) (H : ℕ → Matrix s n K[X])
    (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hH : ∀ i < q + 1, ∀ j y, (H i j y).natDegree ≤ b j + q + 1 - i) :
    let V₀ : Matrix n r K := fun x k => (V x k).coeff (a k)
    let H₀ : ℕ → Matrix s n K := fun i j y => (H i j y).coeff (b j + q + 1 - i)
    ∀ (P₀ : Matrix m n K),
      (∀ i < q + 1, P₀ * matrixCoeff M 1 ^ i * V₀ = 0) →
      Function.Injective (fun C : Matrix r n K => (P₀ * matrixCoeff M 1 ^ (q + 1) * V₀) * C) →
      ∀ (B : Matrix n s K), H₀ q * B = 1 →
        Function.Injective (Matrix.mulVec (fun xy kj =>
          (structuredXColumns M V H q xy kj).coeff (a kj.1 + b kj.2 + q + 1))) := by
  intro V₀ H₀ P₀ hobs hF B hB
  have he : (fun xy kj => (structuredXColumns M V H q xy kj).coeff
      (a kj.1 + b kj.2 + q + 1)) =
      (fun xy kj => ∑ i ∈ Finset.range (q + 1),
        (matrixCoeff M 1 ^ i * V₀) xy.1 kj.1 * H₀ i kj.2 xy.2) := by
    funext xy kj
    exact (structuredXColumns_degree_top M V H q a b hM hV hH xy kj).2
  rw [he]
  exact structured_flat_injective (matrixCoeff M 1) P₀ V₀ H₀ q hobs hF B hB

def structuredColumns (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) : Matrix ((n × n) ⊕ (n × m)) (r × s) K[X] :=
  Sum.elim (structuredXColumns M V H q) (fun xy kj =>
    (M ^ (q + 1) * V) xy.1 kj.1 * T kj.2 xy.2 -
      ∑ i ∈ Finset.range (q + 1), (M ^ i * V) xy.1 kj.1 * D i kj.2 xy.2)

theorem structuredColumns_degree (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hH : ∀ i < q + 1, ∀ j y, (H i j y).natDegree ≤ b j + q + 1 - i)
    (hD : ∀ i < q + 1, ∀ j y, (D i j y).natDegree ≤ b j + q + 1 - i)
    (hT : ∀ j y, (T j y).natDegree ≤ b j) :
    ∀ xy kj, (structuredColumns M V H D T q xy kj).natDegree ≤ a kj.1 + b kj.2 + q + 1 := by
  intro xy kj
  rcases xy with xy | xy
  · exact (structuredXColumns_degree_top M V H q a b hM hV hH xy kj).1
  · have hp (i : ℕ) : DegreeBound (M ^ i) i := by
      simpa using degreeBound_pow M 1 hM i
    have hv (i : ℕ) := (matrixCoeff_mul_column (M ^ i) V i a (hp i) hV xy.1 kj.1).1
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hv (q + 1)) (hT kj.2 xy.2))
      omega
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hv i) (hD i hi' kj.2 xy.2))
      omega

theorem structuredColumns_leading_of_X [Fintype r] [Fintype s]
    (M : Matrix n n K[X]) (V : Matrix n r K[X]) (H : ℕ → Matrix s n K[X])
    (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X]) (q : ℕ) (e : r × s → ℕ)
    (hX : Function.Injective (Matrix.mulVec (fun xy kj =>
      (structuredXColumns M V H q xy kj).coeff (e kj)))) :
    Function.Injective (Matrix.mulVec (fun xy kj =>
      (structuredColumns M V H D T q xy kj).coeff (e kj))) := by
  intro c d h
  apply hX
  funext xy
  exact congrFun h (.inl xy)

theorem structuredXColumns_map {F : Type*} [Field F]
    (φ : K[X] →+* F) (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (q : ℕ) :
    (structuredXColumns M V H q).map φ =
      (fun xy kj => ∑ i ∈ Finset.range (q + 1),
        ((M.map φ) ^ i * V.map φ) xy.1 kj.1 * (H i).map φ kj.2 xy.2) := by
  funext xy kj
  simp only [Matrix.map_apply, structuredXColumns, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hp : (M ^ i).map φ = (M.map φ) ^ i := map_pow φ.mapMatrix M i
  rw [RingHom.map_matrix_mul, hp]

theorem structuredXColumns_point_injective {F : Type*} [Field F]
    [Fintype m] [Fintype r] [Fintype s] [DecidableEq s]
    (φ : K[X] →+* F) (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (q : ℕ) (P₀ : Matrix m n F)
    (hobs : ∀ i < q + 1, P₀ * (M.map φ) ^ i * V.map φ = 0)
    (hF : Function.Injective (fun C : Matrix r n F =>
      (P₀ * (M.map φ) ^ (q + 1) * V.map φ) * C))
    (B : Matrix n s F) (hB : (H q).map φ * B = 1) :
    Function.Injective ((structuredXColumns M V H q).map φ).mulVec := by
  rw [structuredXColumns_map]
  exact structured_flat_injective (M.map φ) P₀ (V.map φ) (fun i => (H i).map φ)
    q hobs hF B hB

omit [Fintype n] [DecidableEq n] in
theorem matrix_unit_sandwich {R : Type*} [CommRing R] [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s] (A : Matrix n r R) (B : Matrix s m R)
    (k : r) (j : s) (x : n) (y : m) :
    (A * Matrix.stdBasisMatrix k j (1 : R) * B) x y = A x k * B j y := by
  simp [Matrix.mul_apply, Matrix.stdBasisMatrix, ite_and]

theorem structuredColumns_stabilizer [Fintype m] [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P) (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (kj : r × s) :
    TraceZeroStabilizer M P
      (fun x y => structuredColumns M V H D T q (.inl (x,y)) kj)
      (fun x y => structuredColumns M V H D T q (.inr (x,y)) kj) := by
  let C : Matrix r s K[X] := Matrix.stdBasisMatrix kj.1 kj.2 1
  have hx : (fun x y => structuredColumns M V H D T q (.inl (x,y)) kj) =
      ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i := by
    funext x y
    simp only [structuredColumns, Sum.elim_inl, structuredXColumns, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (matrix_unit_sandwich (M ^ i * V) (H i) kj.1 kj.2 x y).symm
  have hu : (fun x y => structuredColumns M V H D T q (.inr (x,y)) kj) =
      M ^ (q + 1) * V * C * T - ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * D i := by
    funext x y
    simp only [structuredColumns, Sum.elim_inr, Matrix.sub_apply, Matrix.sum_apply,
      C, matrix_unit_sandwich]
  rw [hx, hu]
  obtain ⟨hp, hm⟩ := structured_kernel M P V C H D T q hzero hstep hend hobs
  exact ⟨hp, hm, structured_kernel_trace_zero M P V C H D T q hstep hend hobs⟩

theorem structuredColumns_sl_equations [Fintype m] [Fintype r] [Fintype s]
    [DecidableEq m] [DecidableEq r] [DecidableEq s]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (i₀ : n) (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P) (hobs : ∀ i < q + 1, P * M ^ i * V = 0) :
    slEquationMatrix M P i₀ * structuredColumns M V H D T q = 0 := by
  funext xy kj
  have h := (slEquationMatrix_kernel_iff M P i₀
    (fun ij => structuredColumns M V H D T q ij kj)).mpr
      (strict_stabilizer_mem_radical M P _ _
        (structuredColumns_stabilizer M P V H D T q hzero hstep hend hobs kj))
  exact congrFun h xy

theorem structuredColumns_predictable_degree [Fintype r] [Fintype s]
    (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (a : r → ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hV : ∀ x k, (V x k).natDegree ≤ a k)
    (hH : ∀ i < q + 1, ∀ j y, (H i j y).natDegree ≤ b j + q + 1 - i)
    (hD : ∀ i < q + 1, ∀ j y, (D i j y).natDegree ≤ b j + q + 1 - i)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hX : Function.Injective (Matrix.mulVec (fun xy kj =>
      (structuredXColumns M V H q xy kj).coeff (a kj.1 + b kj.2 + q + 1))))
    (c : r × s → K[X]) (hc : c ≠ 0) :
    (∀ xy, ((structuredColumns M V H D T q *ᵥ c) xy).natDegree ≤
      weightedDegree (fun kj => a kj.1 + b kj.2 + q + 1) c) ∧
    ∃ xy, ((structuredColumns M V H D T q *ᵥ c) xy).natDegree =
      weightedDegree (fun kj => a kj.1 + b kj.2 + q + 1) c ∧
      (structuredColumns M V H D T q *ᵥ c) xy ≠ 0 :=
  predictable_weighted_degree _ _ c
    (structuredColumns_degree M V H D T q a b hM hV hH hD hT)
    (structuredColumns_leading_of_X M V H D T q _ hX) hc

theorem structuredColumns_gl_equations [Fintype m] [Fintype r] [Fintype s]
    [DecidableEq m] [DecidableEq r] [DecidableEq s]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P) (hobs : ∀ i < q + 1, P * M ^ i * V = 0) :
    glEquationMatrix M P * structuredColumns M V H D T q = 0 := by
  funext xy kj
  have hs := structuredColumns_stabilizer M P V H D T q hzero hstep hend hobs kj
  have h := (glEquationMatrix_kernel_iff M P
    (fun ij => structuredColumns M V H D T q ij kj)).mpr ⟨hs.1, sub_eq_zero.mpr hs.2.1⟩
  exact congrFun h xy

theorem structuredColumns_point_of_X {F : Type*} [Field F] [Fintype r] [Fintype s]
    (φ : K[X] →+* F) (M : Matrix n n K[X]) (V : Matrix n r K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X]) (q : ℕ)
    (hX : Function.Injective ((structuredXColumns M V H q).map φ).mulVec) :
    Function.Injective ((structuredColumns M V H D T q).map φ).mulVec := by
  intro c d h
  apply hX
  funext xy
  exact congrFun h (.inl xy)

theorem observability_polynomial_degree_top [Fintype m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (ij : Fin q × m) (y : n) :
    (observabilityMatrix M P q ij y).natDegree ≤ ij.1.val + 1 ∧
      (observabilityMatrix M P q ij y).coeff (ij.1.val + 1) =
        (matrixCoeff P 1 * matrixCoeff M 1 ^ ij.1.val) ij.2 y := by
  have hp : DegreeBound (M ^ ij.1.val) ij.1.val := by
    simpa using degreeBound_pow M 1 hM ij.1.val
  constructor
  · have h := degreeBound_mul hP hp ij.2 y
    simpa [observabilityMatrix, Nat.add_comm] using h
  · have he := matrixCoeff_mul P (M ^ ij.1.val) 1 ij.1.val hP hp
    have hpow : matrixCoeff (M ^ ij.1.val) ij.1.val = matrixCoeff M 1 ^ ij.1.val := by
      simpa using matrixCoeff_pow M 1 hM ij.1.val
    rw [hpow] at he
    simpa [matrixCoeff, observabilityMatrix, Nat.add_comm] using congrFun (congrFun he ij.2) y

def structuredCoefficientRows (D : ℕ → Matrix s m K[X]) (q : ℕ) :
    Matrix s (Fin (q + 1) × m) K[X] := fun j im => D im.1.val j im.2

theorem structuredCoefficientRows_relation [Fintype m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X])
    (q : ℕ) (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P) (hend : H q = T * P) :
    structuredCoefficientRows D q * observabilityMatrix M P (q + 1) = T * P * M ^ (q + 1) := by
  have he : structuredCoefficientRows D q * observabilityMatrix M P (q + 1) =
      ∑ i ∈ Finset.range (q + 1), D i * (P * M ^ i) := by
    funext j y
    simp only [Matrix.mul_apply, structuredCoefficientRows, observabilityMatrix,
      Fintype.sum_prod_type, Matrix.sum_apply]
    simpa only [Matrix.mul_apply] using
      (Fin.sum_univ_eq_sum_range (fun i => (D i * (P * M ^ i)) j y) (q + 1))
  rw [he]
  simp_rw [← Matrix.mul_assoc]
  rw [← backward_recurrence_relation M P H D q hzero hstep, hend]

theorem structured_coefficients_degree [Fintype m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (D : ℕ → Matrix s m K[X]) (T : Matrix s m K[X]) (q : ℕ) (b : s → ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hT : ∀ j y, (T j y).natDegree ≤ b j)
    (hrel : structuredCoefficientRows D q *
      observabilityMatrix M P (q + 1) = T * P * M ^ (q + 1))
    (hlead : Function.Injective (Matrix.mulVec
      (show Matrix n (Fin (q + 1) × m) K from fun y im =>
        (matrixCoeff P 1 * matrixCoeff M 1 ^ im.1.val) im.2 y))) :
    ∀ i < q + 1, ∀ j y, (D i j y).natDegree ≤ b j + q + 1 - i := by
  have ha := fun im y => (observability_polynomial_degree_top M P (q + 1) hM hP im y).1
  have hl : Function.Injective (Matrix.mulVec (show Matrix n (Fin (q + 1) × m) K from
      fun y im => (observabilityMatrix M P (q + 1) im y).coeff (im.1.val + 1))) := by
    have he : (show Matrix n (Fin (q + 1) × m) K from
        fun y im => (observabilityMatrix M P (q + 1) im y).coeff (im.1.val + 1)) =
        (fun y im => (matrixCoeff P 1 * matrixCoeff M 1 ^ im.1.val) im.2 y) := by
      funext y im
      exact (observability_polynomial_degree_top M P (q + 1) hM hP im y).2
    rw [he]
    exact hlead
  have hbound : ∀ j y, ((structuredCoefficientRows D q *
      observabilityMatrix M P (q + 1)) j y).natDegree ≤ b j + q + 2 := by
    rw [hrel]
    have hp := matrix_mul_row_degree T P b 1 hT hP
    have hm : DegreeBound (M ^ (q + 1)) (q + 1) := by
      simpa using degreeBound_pow M 1 hM (q + 1)
    intro j y
    have h := matrix_mul_row_degree (T * P) (M ^ (q + 1)) (fun j => b j + 1) (q + 1) hp hm j y
    exact h.trans (by omega)
  have hd := row_coordinates_degree_bound (observabilityMatrix M P (q + 1))
    (structuredCoefficientRows D q) (fun im => im.1.val + 1)
    (fun j => b j + q + 2) ha hl hbound
  intro i hi j y
  rcases hd j (⟨i, hi⟩, y) with hz | ⟨_, hb⟩
  · change D i j y = 0 at hz
    simp [hz]
  · change (D i j y).natDegree ≤ b j + q + 2 - (i + 1) at hb
    exact hb.trans (by omega)

end FD56
