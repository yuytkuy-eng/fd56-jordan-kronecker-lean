/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSLRelationDegree
import FD56.Hilbert.MiddleGLShift
import FD56.Hilbert.MixedKernelBasis

/-! Weighted finite relations give lower bounds for mixed-degree SL radicals. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def rowBoundedEntries (k : r → ℕ) (E : ∀ i, m → BoundedPoly K (k i)) : Matrix r m K[X] :=
  fun i j => (E i j).val

def weightedSLRelation (G : Matrix m r K[X]) (a k : r → ℕ) (d : ℕ)
    (hG : ∀ x j, (G x j).natDegree ≤ a j + 2)
    (hscalar : ∀ i, d + 1 ≤ k i + a i + 2) :
    ((∀ i, m → BoundedPoly K (k i)) × BoundedPoly K (d + 1)) →ₗ[K]
      (∀ i j, BoundedPoly K (k i + a j + 2)) where
  toFun z i j := boundedPolyOf
    ((rowBoundedEntries k z.1 * G + z.2.val • (1 : Matrix r r K[X])) i j) (by
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro x _
        have hh := Polynomial.natDegree_mul_le
          (p := rowBoundedEntries k z.1 i x) (q := G x j)
        have he := boundedPoly_degree _ (z.1 i x)
        have hg := hG x j
        change ((z.1 i x).val * G x j).natDegree ≤ _
        dsimp only [rowBoundedEntries] at hh
        omega
      · by_cases hij : i = j
        · subst j
          simpa using (boundedPoly_degree _ z.2).trans (hscalar i)
        · simp [Matrix.one_apply, hij])
  map_add' z w := by
    funext i j
    apply Subtype.ext
    change (((rowBoundedEntries k z.1 + rowBoundedEntries k w.1) * G +
      (z.2.val + w.2.val) • (1 : Matrix r r K[X])) i j) =
      (rowBoundedEntries k z.1 * G + z.2.val • (1 : Matrix r r K[X])) i j +
      (rowBoundedEntries k w.1 * G + w.2.val • (1 : Matrix r r K[X])) i j
    simp only [Matrix.add_mul, add_smul, Matrix.add_apply]
    abel
  map_smul' t z := by
    funext i j
    apply Subtype.ext
    change (((t • rowBoundedEntries k z.1) * G + (t • z.2.val) • (1 : Matrix r r K[X])) i j) = _
    rw [Matrix.smul_mul, smul_assoc, ← smul_add]
    rfl

omit [Fintype r] [DecidableEq m] in
theorem weightedSLRelation_mem_ker (G : Matrix m r K[X]) (a k : r → ℕ) (d : ℕ)
    (hG : ∀ x j, (G x j).natDegree ≤ a j + 2)
    (hscalar : ∀ i, d + 1 ≤ k i + a i + 2)
    (z : (∀ i, m → BoundedPoly K (k i)) × BoundedPoly K (d + 1)) :
    z ∈ LinearMap.ker (weightedSLRelation G a k d hG hscalar) ↔
      rowBoundedEntries k z.1 * G = (-z.2.val) • (1 : Matrix r r K[X]) := by
  change weightedSLRelation G a k d hG hscalar z = 0 ↔ _
  constructor
  · intro hz
    have hh : rowBoundedEntries k z.1 * G + z.2.val • (1 : Matrix r r K[X]) = 0 := by
      funext i j
      exact congrArg Subtype.val (congrFun (congrFun hz i) j)
    simpa only [neg_smul] using add_eq_zero_iff_eq_neg.mp hh
  · intro hz
    funext i j
    apply Subtype.ext
    change (rowBoundedEntries k z.1 * G + z.2.val • (1 : Matrix r r K[X])) i j = 0
    rw [hz, neg_smul, neg_add_cancel]
    rfl

omit [DecidableEq m] in
theorem weightedSLRelation_kernel_lower (G : Matrix m r K[X]) (a k : r → ℕ) (d : ℕ)
    (hG : ∀ x j, (G x j).natDegree ≤ a j + 2)
    (hscalar : ∀ i, d + 1 ≤ k i + a i + 2) :
    (∑ i, Fintype.card m * (k i + 1)) + (d + 2) -
      (∑ i, ∑ j, (k i + a j + 3)) ≤
      Module.finrank K (LinearMap.ker (weightedSLRelation G a k d hG hscalar)) := by
  have hd := (weightedSLRelation G a k d hG hscalar).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (weightedSLRelation G a k d hG hscalar))
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, boundedPoly_finrank,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at hd hr
  simp only [Nat.add_assoc] at hd hr ⊢
  norm_num only [Nat.reduceAdd] at hd hr
  omega

variable (M : Matrix n n K[X]) (P : Matrix m n K[X])
  (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
  (R : Matrix n m K[X]) (hPR : P * R = 1) (a k : r → ℕ) (d : ℕ)
  (hM : DegreeBound M 1) (hP : DegreeBound P 1)
  (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
  (hBL : Function.Injective (Matrix.mulVec
    (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
  (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec)
  (hrow : ∀ i, a i + 1 + k i ≤ d)
  (hscalar : ∀ i, d + 1 ≤ k i + a i + 2)

include hM hP hB in
omit [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r] in
theorem weighted_middle_matrix_degree :
    ∀ x j, ((P * M * polynomialKernelBasisMatrix P B) x j).natDegree ≤ a j + 2 := by
  intro x j
  have hh := (matrixCoeff_mul_column (P * M) (polynomialKernelBasisMatrix P B) 2 a
    (degreeBound_mul hP hM) hB x j).1
  omega

def weightedSLRelationLift [Nonempty n] :
    LinearMap.ker (weightedSLRelation (P * M * polynomialKernelBasisMatrix P B) a k d
      (weighted_middle_matrix_degree M P B a hM hP hB) hscalar) →ₗ[K]
      boundedSLKernel M P d where
  toFun z := by
    let E := rowBoundedEntries k z.val.1
    have hrel := (weightedSLRelation_mem_ker _ _ _ _ _ _ z.val).mp z.property
    have he := middle_sl_reconstruct M P B R hPR E z.val.2.val hrel
    have hX : DegreeBound (middleSLX P B E) d := by
      apply (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E a d
        hB hBL hP hPL).mpr
      intro i j
      apply Or.inr
      have hr := hrow i
      have hb := boundedPoly_degree _ (z.val.1 i j)
      change (E i j).natDegree ≤ k i at hb
      constructor <;> omega
    have hU := middle_translation_degree M P _ _ _ d hM hP hPL hX
      (boundedPoly_degree _ z.val.2) he.2.2
    exact ⟨(boundedMatrixOf _ hX, boundedMatrixOf _ hU),
      (slRadical_iff_equations M P _ _).mpr ⟨he.1, he.2.1, z.val.2.val, he.2.2⟩⟩
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective d
      change middleSLX P B (rowBoundedEntries k z.val.1 + rowBoundedEntries k w.val.1) =
        middleSLX P B (rowBoundedEntries k z.val.1) + middleSLX P B (rowBoundedEntries k w.val.1)
      simp only [middleSLX, Matrix.mul_add, Matrix.add_mul]
    · apply entries_injective d
      change middleSLTranslation M P B R (rowBoundedEntries k z.val.1 + rowBoundedEntries k w.val.1)
        (z.val.2.val + w.val.2.val) =
        middleSLTranslation M P B R (rowBoundedEntries k z.val.1) z.val.2.val +
        middleSLTranslation M P B R (rowBoundedEntries k w.val.1) w.val.2.val
      simp only [middleSLTranslation, middleSLX, Matrix.mul_add, Matrix.add_mul,
        Matrix.sub_mul, add_smul]
      abel
  map_smul' t z := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective d
      change middleSLX P B (t • rowBoundedEntries k z.val.1) =
        t • middleSLX P B (rowBoundedEntries k z.val.1)
      simp only [middleSLX, Matrix.mul_smul, Matrix.smul_mul]
    · apply entries_injective d
      change middleSLTranslation M P B R (t • rowBoundedEntries k z.val.1) (t • z.val.2.val) =
        t • middleSLTranslation M P B R (rowBoundedEntries k z.val.1) z.val.2.val
      simp only [middleSLTranslation, middleSLX, Matrix.mul_smul, Matrix.smul_mul,
        smul_assoc, smul_sub]
      rw [← smul_sub, ← smul_sub, Matrix.smul_mul]

theorem weightedSLRelationLift_injective [Nonempty n] (j₀ : r) :
    Function.Injective (weightedSLRelationLift M P B R hPR a k d hM hP hB hBL hPL hrow hscalar) := by
  intro z w h
  have hX := congrArg (fun y : boundedSLKernel M P d => entries y.val.1) h
  change middleSLX P B (rowBoundedEntries k z.val.1) =
    middleSLX P B (rowBoundedEntries k w.val.1) at hX
  have hEe := middleSLX_injective P B R hPR hX
  have hE : z.val.1 = w.val.1 := by
    funext i j
    apply Subtype.ext
    exact congrFun (congrFun hEe i) j
  apply Subtype.ext
  apply Prod.ext hE
  apply Subtype.ext
  have hz := (weightedSLRelation_mem_ker _ _ _ _ _ _ z.val).mp z.property
  have hw := (weightedSLRelation_mem_ker _ _ _ _ _ _ w.val).mp w.property
  rw [hE] at hz
  have hc := congrArg (fun A : Matrix r r K[X] => A j₀ j₀) (hz.symm.trans hw)
  simpa using hc

include B R hPR hM hP hB hBL hPL hrow hscalar in
theorem weighted_middle_slHilbert_lower [Nonempty n] (j₀ : r) :
    (∑ i, Fintype.card m * (k i + 1)) + (d + 2) -
      (∑ i, ∑ j, (k i + a j + 3)) ≤ slHilbert M P d := by
  exact (weightedSLRelation_kernel_lower _ a k d
    (weighted_middle_matrix_degree M P B a hM hP hB) hscalar).trans
      (LinearMap.finrank_le_finrank_of_injective
        (weightedSLRelationLift_injective M P B R hPR a k d hM hP hB hBL hPL hrow hscalar j₀))

theorem mixed_relation_dimension_identity (a u v m : ℕ) (ha : 4 ≤ a)
    (hm : m = a * (u + v) + v) :
    u * (m * 2) + v * m + (a + 4) -
      (u * (u * (a + 4) + v * (a + 5)) + v * (u * (a + 3) + v * (a + 4))) =
      u * (m - 4 * (u + v)) + (a + 4) - 3 * (u + v) * v := by
  have hle : 4 * (u + v) ≤ m := by nlinarith
  have hs := Nat.sub_add_cancel hle
  have he :
      (u * (u * (a + 4) + v * (a + 5)) + v * (u * (a + 3) + v * (a + 4))) +
        u * (m - 4 * (u + v)) = u * (m * 2) + v * m + 3 * (u + v) * v := by
    nlinarith [congrArg (fun z => u * z) hs]
  omega

theorem mixed_middle_slHilbert_critical_lower
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (a u v : ℕ) (ha : 4 ≤ a)
    (hm : Fintype.card m = a * (u + v) + v)
    (B : Basis (Fin u ⊕ Fin v) K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤
      Sum.elim (fun _ => a) (fun _ => a + 1) i)
    (hBL : Function.Injective (Matrix.mulVec (fun x i =>
      (polynomialKernelBasisMatrix P B x i).coeff (Sum.elim (fun _ => a) (fun _ => a + 1) i))))
    (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec) (i₀ : n) (j₀ : Fin u ⊕ Fin v) :
    u * (Fintype.card m - 4 * (u + v)) + (a + 4) - 3 * (u + v) * v ≤
      slHilbert M P (a + 2) := by
  letI : Nonempty n := ⟨i₀⟩
  have hh := weighted_middle_slHilbert_lower M P B R hPR
    (Sum.elim (fun _ => a) (fun _ => a + 1))
    (Sum.elim (fun _ => 1) (fun _ => 0)) (a + 2) hM hP hB hBL hPL
    (by intro i; cases i <;> simp) (by intro i; cases i <;> dsimp <;> omega) j₀
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    zero_add, Nat.reduceAdd, mul_one, Nat.add_assoc] at hh
  have he := mixed_relation_dimension_identity a u v (Fintype.card m) ha hm
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at he hh ⊢
  norm_num only [Nat.reduceAdd] at he hh
  omega

theorem generic_mixed_glHilbert_critical (a u v : ℕ) (ha : 4 ≤ a) (hu : 0 < u)
    (hm : Fintype.card m = a * (u + v) + v)
    (hn : Fintype.card n = Fintype.card m + (u + v)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) (a + 2)) =
      u * (Fintype.card m - 4 * (u + v)) := by
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2 * Fintype.card m := by rw [hn, hm]; nlinarith
  have hdiff : Fintype.card n - Fintype.card m = u + v := by omega
  obtain ⟨B, hB, hBL⟩ := generic_mixed_kernel_basis (K := K) a u v hu hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hs := middle_gl_kernel_hilbert_shifted _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B) (mixedKernelDegree a u v)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    (a + 2) (by intro i; cases i <;> simp [mixedKernelDegree])
  have haux (e : ℕ) :
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (genericAffineRows K n m * genericAffineSquare K n m *
            polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose e) =
        (Fintype.card m - (u + v)) * (e + 1) - (Fintype.card m + 2 * (u + v)) := by
    have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_middle_auxiliary_minimal_degrees B hmn hnm) e
    rw [balancedDegreeList_hilbert _ _ e (by omega), hdiff] at hh
    exact hh
  have hlow : (Fintype.card m - (u + v)) * 2 - (Fintype.card m + 2 * (u + v)) =
      Fintype.card m - 4 * (u + v) := by omega
  have hhigh : (Fintype.card m - (u + v)) * 1 - (Fintype.card m + 2 * (u + v)) = 0 := by omega
  rw [hs]
  simp only [Fintype.sum_sum_type, mixedKernelDegree_inl, mixedKernelDegree_inr,
    haux, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h1 : a + 2 - (a + 1) = 1 := by omega
  have h0 : a + 2 - (a + 1 + 1) = 0 := by omega
  simp only [h1, h0, Nat.reduceAdd, hlow, hhigh, mul_zero, add_zero]

theorem generic_mixed_slHilbert_critical_lower (a u v : ℕ) (ha : 4 ≤ a) (hu : 0 < u)
    (hm : Fintype.card m = a * (u + v) + v)
    (hn : Fintype.card n = Fintype.card m + (u + v)) (i₀ : n) :
    u * (Fintype.card m - 4 * (u + v)) + (a + 4 - 3 * (u + v) * v) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (a + 2) := by
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2 * Fintype.card m := by rw [hn, hm]; nlinarith
  obtain ⟨B, hB, hBL⟩ := generic_mixed_kernel_basis (K := K) a u v hu hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hraw := mixed_middle_slHilbert_critical_lower _ _ a u v ha hm B R hPR
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    i₀ (Sum.inl ⟨0, hu⟩)
  have hg := (generic_middle_slHilbert_bounds (K := K) i₀ hmn hnm (a + 2)).1
  rw [generic_mixed_glHilbert_critical a u v ha hu hm hn] at hg
  omega

end FD56
