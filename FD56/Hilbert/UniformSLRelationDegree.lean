/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSLCriticalBound

/-! A finite coefficient relation embeds into the actual bounded SL radical.
The auxiliary matrix has arbitrary bounded degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def uniformSLRelation (G : Matrix m r K[X]) (k b : ℕ) (hG : DegreeBound G b) :
    (BoundedMatrix K r m k × BoundedPoly K (k + b)) →ₗ[K] BoundedMatrix K r r (k + b) where
  toFun z := boundedMatrixOf (entries z.1 * G + z.2.val • 1) (by
    intro i j
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simpa using degreeBound_mul (entries_degree z.1) hG i j
    · by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using boundedPoly_degree (k + b) z.2
      · simp [Matrix.one_apply, hij])
  map_add' z w := by
    apply entries_injective (k + b)
    simp only [entries_boundedMatrixOf, entries_add]
    change (entries z.1 + entries w.1) * G + (z.2.val + w.2.val) • 1 = _
    rw [Matrix.add_mul, add_smul]
    abel
  map_smul' t z := by
    apply entries_injective (k + b)
    simp only [entries_boundedMatrixOf, entries_smul]
    change (t • entries z.1) * G + (t • z.2.val) • 1 = _
    rw [Matrix.smul_mul, smul_assoc, smul_add]
    rfl

omit [Fintype r] [DecidableEq m] in
theorem uniformSLRelation_mem_ker (G : Matrix m r K[X]) (k b : ℕ)
    (hG : DegreeBound G b) (z : BoundedMatrix K r m k × BoundedPoly K (k + b)) :
    z ∈ LinearMap.ker (uniformSLRelation G k b hG) ↔
      entries z.1 * G = (-z.2.val) • 1 := by
  change uniformSLRelation G k b hG z = 0 ↔ _
  rw [← (entries_injective (k + b)).eq_iff]
  change entries z.1 * G + z.2.val • 1 = 0 ↔ _
  rw [add_eq_zero_iff_eq_neg, neg_smul]

omit [DecidableEq m] in
theorem uniformSLRelation_kernel_lower (G : Matrix m r K[X]) (k b : ℕ)
    (hG : DegreeBound G b) :
    Fintype.card r * Fintype.card m * (k + 1) + (k + b + 1) -
      Fintype.card r * Fintype.card r * (k + b + 1) ≤
      Module.finrank K (LinearMap.ker (uniformSLRelation G k b hG)) := by
  have hd := (uniformSLRelation G k b hG).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (uniformSLRelation G k b hG))
  simp only [Module.finrank_prod, boundedMatrix_finrank, boundedPoly_finrank,
    zero_add, mul_one] at hd hr
  omega

variable (M : Matrix n n K[X]) (P : Matrix m n K[X])
  (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
  (R : Matrix n m K[X]) (hPR : P * R = 1) (a k : ℕ)
  (hM : DegreeBound M 1) (hP : DegreeBound P 1)
  (hB : DegreeBound (polynomialKernelBasisMatrix P B) a)
  (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)

def uniformSLRelationLift [Nonempty n] :
    LinearMap.ker (uniformSLRelation (P * M * polynomialKernelBasisMatrix P B)
      k (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB)) →ₗ[K]
      boundedSLKernel M P (a + k + 1) where
  toFun z := by
    have hrel := (uniformSLRelation_mem_ker _ _ _ _ z.val).mp z.property
    have he := middle_sl_reconstruct M P B R hPR (entries z.val.1) z.val.2.val hrel
    have hX : DegreeBound (middleSLX P B (entries z.val.1)) (a + k + 1) := by
      simpa only [Nat.add_zero] using degreeBound_mul
        (degreeBound_mul hB (entries_degree z.val.1)) hP
    have hU := middle_translation_degree M P _ _ _ (a + k + 1)
      hM hP hPlead hX (by have := boundedPoly_degree _ z.val.2; omega) he.2.2
    exact ⟨(boundedMatrixOf _ hX, boundedMatrixOf _ hU),
      (slRadical_iff_equations M P _ _).mpr ⟨he.1, he.2.1, z.val.2.val, he.2.2⟩⟩
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective (a + k + 1)
      change middleSLX P B (entries z.val.1 + entries w.val.1) =
        middleSLX P B (entries z.val.1) + middleSLX P B (entries w.val.1)
      simp only [middleSLX, Matrix.mul_add, Matrix.add_mul]
    · apply entries_injective (a + k + 1)
      change middleSLTranslation M P B R (entries z.val.1 + entries w.val.1)
        (z.val.2.val + w.val.2.val) =
        middleSLTranslation M P B R (entries z.val.1) z.val.2.val +
        middleSLTranslation M P B R (entries w.val.1) w.val.2.val
      simp only [middleSLTranslation, middleSLX, Matrix.mul_add, Matrix.add_mul,
        Matrix.sub_mul, add_smul]
      abel
  map_smul' t z := by
    apply Subtype.ext
    apply Prod.ext
    · apply entries_injective (a + k + 1)
      change middleSLX P B (t • entries z.val.1) = t • middleSLX P B (entries z.val.1)
      simp only [middleSLX, Matrix.mul_smul, Matrix.smul_mul]
    · apply entries_injective (a + k + 1)
      change middleSLTranslation M P B R (t • entries z.val.1) (t • z.val.2.val) =
        t • middleSLTranslation M P B R (entries z.val.1) z.val.2.val
      simp only [middleSLTranslation, middleSLX, Matrix.mul_smul, Matrix.smul_mul,
        smul_assoc, smul_sub]
      rw [← smul_sub, ← smul_sub, Matrix.smul_mul]

theorem uniformSLRelationLift_injective [Nonempty n] (j₀ : r) :
    Function.Injective (uniformSLRelationLift M P B R hPR a k hM hP hB hPlead) := by
  intro z w h
  have hX := congrArg (fun y : boundedSLKernel M P (a + k + 1) => entries y.val.1) h
  change middleSLX P B (entries z.val.1) = middleSLX P B (entries w.val.1) at hX
  have hE := (entries_injective k) (middleSLX_injective P B R hPR hX)
  apply Subtype.ext
  apply Prod.ext hE
  apply Subtype.ext
  have hz := (uniformSLRelation_mem_ker _ _ _ _ z.val).mp z.property
  have hw := (uniformSLRelation_mem_ker _ _ _ _ w.val).mp w.property
  rw [hE] at hz
  have hc := congrArg (fun A : Matrix r r K[X] => A j₀ j₀) (hz.symm.trans hw)
  simpa using hc

theorem uniformSLRelationLift_surjective [Nonempty n] (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a))) :
    Function.Surjective (uniformSLRelationLift M P B R hPR a k hM hP hB hPlead) := by
  intro z
  obtain ⟨E, c, hrel, hX, hU⟩ := (middle_sl_radical_iff M P B R hPR hG
    (entries z.val.1) (entries z.val.2)).mp z.property
  have hweight := (middle_product_degree_iff (polynomialKernelBasisMatrix P B) P E
    (fun _ => a) (a + k + 1) hB hBL hP hPlead).mp (by
      change DegreeBound (middleSLX P B E) (a + k + 1)
      rw [← hX]
      exact entries_degree z.val.1)
  have hE : DegreeBound E k := by
    intro i j
    rcases hweight i j with hz | ⟨_, hb⟩
    · simp [hz]
    · simpa [Nat.add_comm a k, Nat.add_assoc] using hb
  have hc : c.natDegree ≤ k + (a + 2) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using middle_scalar_degree_of_weighted M P
      (polynomialKernelBasisMatrix P B) E (fun _ => a) c j₀ (a + k + 1) hM hP hB hweight hrel
  let w : LinearMap.ker (uniformSLRelation (P * M * polynomialKernelBasisMatrix P B)
      k (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB)) :=
    ⟨(boundedMatrixOf E hE, boundedPolyOf c hc),
      (uniformSLRelation_mem_ker _ _ _ _ _).mpr hrel⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply entries_injective (a + k + 1)
    exact hX.symm
  · apply entries_injective (a + k + 1)
    exact hU.symm

def uniformSLRelationEquiv [Nonempty n] (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a))) :
    LinearMap.ker (uniformSLRelation (P * M * polynomialKernelBasisMatrix P B)
      k (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB)) ≃ₗ[K]
      boundedSLKernel M P (a + k + 1) :=
  LinearEquiv.ofBijective (uniformSLRelationLift M P B R hPR a k hM hP hB hPlead)
    ⟨uniformSLRelationLift_injective M P B R hPR a k hM hP hB hPlead j₀,
      uniformSLRelationLift_surjective M P B R hPR a k hM hP hB hPlead j₀ hG hBL⟩

include R hPR hM hP hPlead in
theorem uniform_middle_slHilbert_relation_eq [Nonempty n] (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a))) :
    slHilbert M P (a + k + 1) = Module.finrank K
      (LinearMap.ker (uniformSLRelation (P * M * polynomialKernelBasisMatrix P B)
        k (a + 2) (uniform_middle_matrix_degree M P B a hM hP hB))) :=
  (uniformSLRelationEquiv M P B R hPR a k hM hP hB hPlead j₀ hG hBL).finrank_eq.symm

include B R hPR hM hP hB hPlead in
theorem uniform_middle_slHilbert_relation_lower [Nonempty n] (j₀ : r) :
    Fintype.card r * Fintype.card m * (k + 1) + (a + k + 3) -
      Fintype.card r * Fintype.card r * (a + k + 3) ≤ slHilbert M P (a + k + 1) := by
  have hi := LinearMap.finrank_le_finrank_of_injective
    (uniformSLRelationLift_injective M P B R hPR a k hM hP hB hPlead j₀)
  have hh := (uniformSLRelation_kernel_lower _ k _
    (uniform_middle_matrix_degree M P B a hM hP hB)).trans hi
  have he : k + (a + 2) + 1 = a + k + 3 := by omega
  rw [he] at hh
  exact hh


def uniformSLRelationSelector (G : Matrix m r K[X]) (k b : ℕ) (hG : DegreeBound G b)
    (t : ℕ) (f : Fin t → ℕ) :
    LinearMap.ker (uniformSLRelation G k b hG) →ₗ[K] (Fin t → K) where
  toFun z j := z.val.2.val.coeff (f j)
  map_add' z w := by ext j; exact Polynomial.coeff_add _ _ _
  map_smul' t z := by ext j; exact Polynomial.coeff_smul _ _ _

omit [Fintype r] [DecidableEq m] in
theorem uniformSLRelationSelector_injective
    (G : Matrix m r K[X]) (k b : ℕ) (hG : DegreeBound G b) (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]), DegreeBound E k →
      E * G = (-c) • 1 → (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    Function.Injective (uniformSLRelationSelector G k b hG t f) := by
  intro x y hxy
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  let z := x - y
  have hz : uniformSLRelationSelector G k b hG t f z = 0 := by
    dsimp only [z]
    exact ((uniformSLRelationSelector G k b hG t f).map_sub x y).trans
      (by rw [hxy, sub_self])
  have hc : ∀ j, z.val.2.val.coeff (f j) = 0 := congrFun hz
  have hh := hzero (entries z.val.1) z.val.2.val (entries_degree z.val.1)
    ((uniformSLRelation_mem_ker G k b hG z.val).mp z.property) hc
  change z = 0
  apply Subtype.ext
  apply Prod.ext
  · apply entries_injective k
    exact hh.1
  · apply Subtype.ext
    exact hh.2

omit [Fintype r] [DecidableEq m] in
theorem uniformSLRelation_kernel_upper
    (G : Matrix m r K[X]) (k b : ℕ) (hG : DegreeBound G b) (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]), DegreeBound E k →
      E * G = (-c) • 1 → (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    Module.finrank K (LinearMap.ker (uniformSLRelation G k b hG)) ≤ t := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (uniformSLRelationSelector_injective G k b hG t f hzero)
  simpa using hh

theorem uniform_middle_slHilbert_relation_upper [Nonempty n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (a k : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : DegreeBound (polynomialKernelBasisMatrix P B) a)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a)))
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]), DegreeBound E k →
      E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 →
      (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    slHilbert M P (a + k + 1) ≤ t := by
  rw [uniform_middle_slHilbert_relation_eq M P B R hPR a k hM hP hB hPlead j₀ hG hBL]
  exact uniformSLRelation_kernel_upper _ _ _ _ t f hzero

theorem generic_uniform_slHilbert_relation_lower (a k r : ℕ) (ha : 1 ≤ a) (hr : 0 < r)
    (hm : Fintype.card m = a * r) (hn : Fintype.card n = (a + 1) * r) (i₀ : n) :
    r * (a * r) * (k + 1) + (a + k + 3) - r * r * (a + k + 3) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (a + k + 1) := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by rw [hm, hn]; nlinarith
  obtain ⟨B, hB, _⟩ := generic_uniform_kernel_basis (K := K) a r hr hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n
    (by rw [hm]; positivity) hmn
  have hh := uniform_middle_slHilbert_relation_lower _ _ B R hPR a k
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB
    (matrix_transpose_injective_of_surjective _
      (generic_affine_rows_leading_surjective K m n hmn.le)) (⟨0, hr⟩ : Fin r)
  simpa only [Fintype.card_fin, hm] using hh

theorem generic_uniform_three_slHilbert_five_lower (r : ℕ) (hr : 0 < r)
    (hm : Fintype.card m = 3 * r) (hn : Fintype.card n = 4 * r) (i₀ : n) :
    7 - r ^ 2 ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 := by
  have hh := generic_uniform_slHilbert_relation_lower (K := K) 3 1 r (by omega) hr hm hn i₀
  have he : r * r * (3 + 1 + 3) = r * (3 * r) * (1 + 1) + r ^ 2 := by ring
  rw [he, Nat.add_sub_add_left] at hh
  exact hh

end FD56
