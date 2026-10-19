import FD56.RankOne

/-! A degree-five special-linear stabilizer for every affine full-row-rank
pair of sizes (11k, 8k). This is the direct argument in Section 6.3. -/

noncomputable section
open Matrix Polynomial

namespace FD56
variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [Fintype n]

def columnMap (P : Matrix m n K[X]) (hP : DegreeBound P 1) :
    BoundedMatrix K n Unit 2 →ₗ[K] BoundedMatrix K m Unit 3 where
  toFun v i j := boundedPolyOf ((P * entries v) i j)
    ((degreeBound_mul hP (entries_degree v)) i j)
  map_add' v w := by
    apply entries_injective 3
    change P * entries (v + w) = P * entries v + P * entries w
    rw [entries_add, Matrix.mul_add]
  map_smul' c v := by
    apply entries_injective 3
    change P * entries (c • v) = c • (P * entries v)
    rw [entries_smul, Matrix.mul_smul]

def relationMap (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    (BoundedMatrix K Unit m 2 × BoundedMatrix K Unit m 3) →ₗ[K]
      BoundedMatrix K Unit n 4 where
  toFun z i j := boundedPolyOf
    ((entries z.1 * P * M - entries z.2 * P) i j)
    ((degreeBound_sub
      (degreeBound_mul (degreeBound_mul (entries_degree z.1) hP) hM)
      (degreeBound_mul (entries_degree z.2) hP)) i j)
  map_add' z w := by
    apply entries_injective 4
    change entries (z.1 + w.1) * P * M - entries (z.2 + w.2) * P =
      (entries z.1 * P * M - entries z.2 * P) +
      (entries w.1 * P * M - entries w.2 * P)
    simp only [entries_add, Matrix.add_mul]
    abel
  map_smul' c z := by
    apply entries_injective 4
    change entries (c • z.1) * P * M - entries (c • z.2) * P =
      c • (entries z.1 * P * M - entries z.2 * P)
    simp only [entries_smul, Matrix.smul_mul, smul_sub]

theorem exists_column (P : Matrix m n K[X]) (hP : DegreeBound P 1)
    (hdim : 4 * Fintype.card m < 3 * Fintype.card n) :
    ∃ v : Matrix n Unit K[X], v ≠ 0 ∧ DegreeBound v 2 ∧ P * v = 0 := by
  have hf : Module.finrank K (BoundedMatrix K m Unit 3) <
      Module.finrank K (BoundedMatrix K n Unit 2) := by
    simpa [mul_comm] using hdim
  obtain ⟨v, hv, hzero⟩ := exists_nonzero_kernel (columnMap P hP) hf
  refine ⟨entries v, ?_, entries_degree v, ?_⟩
  · intro h
    apply hv
    exact (entries_injective 2) (h.trans (entries_zero 2).symm)
  · exact congrArg entries hzero

theorem exists_relation (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (hrow : RowIndependent P)
    (hdim : 5 * Fintype.card n < 7 * Fintype.card m) :
    ∃ w D : Matrix Unit m K[X], w ≠ 0 ∧ DegreeBound w 2 ∧ DegreeBound D 3 ∧
      w * P * M = D * P := by
  have hf : Module.finrank K (BoundedMatrix K Unit n 4) <
      Module.finrank K (BoundedMatrix K Unit m 2 × BoundedMatrix K Unit m 3) := by
    simp only [Module.finrank_prod, boundedMatrix_finrank, Fintype.card_unit, one_mul]
    nlinarith
  obtain ⟨z, hz, hzero⟩ := exists_nonzero_kernel (relationMap M P hM hP) hf
  have hrel : entries z.1 * P * M = entries z.2 * P := by
    have hh : entries z.1 * P * M - entries z.2 * P = 0 := congrArg entries hzero
    exact sub_eq_zero.mp hh
  refine ⟨entries z.1, entries z.2, ?_, entries_degree z.1, entries_degree z.2, hrel⟩
  intro hw
  have hD : entries z.2 = 0 := by
    apply hrow
    rw [hw, Matrix.zero_mul, Matrix.zero_mul] at hrel
    exact hrel.symm
  apply hz
  apply Prod.ext
  · exact (entries_injective 2) (hw.trans (entries_zero 2).symm)
  · exact (entries_injective 3) (hD.trans (entries_zero 3).symm)

/-- The trace-zero GL stabilizer, a subspace of the full SL radical. -/
def TraceZeroStabilizer (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) : Prop :=
  P * X = 0 ∧ M * X - X * M = U * P ∧ Matrix.trace X = 0

/-- The general coefficient-count criterion, before specializing dimensions. -/
theorem exists_degree_five_stabilizer
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (hrow : RowIndependent P)
    (hcolumn : 4 * Fintype.card m < 3 * Fintype.card n)
    (hrelation : 5 * Fintype.card n < 7 * Fintype.card m) :
    ∃ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      X ≠ 0 ∧ DegreeBound X 5 ∧ DegreeBound U 5 ∧ TraceZeroStabilizer M P X U := by
  obtain ⟨v, hv, hvdeg, hPv⟩ := exists_column P hP hcolumn
  obtain ⟨w, D, hw, hwdeg, hDdeg, hrel⟩ := exists_relation M P hM hP hrow hrelation
  refine ⟨v * w * P, M * v * w - v * D, rankOne_nonzero P hrow v w hv hw, ?_, ?_, ?_⟩
  · exact degreeBound_mul (degreeBound_mul hvdeg hwdeg) hP
  · exact degreeBound_sub (degreeBound_mul (degreeBound_mul hM hvdeg) hwdeg)
      (degreeBound_mul hvdeg hDdeg)
  · exact rankOne_stabilizer M P v w D hPv hrel

/-- Unconditional in k, M and P except for the explicit hypotheses from the paper.
No generic-rank, bundle-theoretic, or classification theorem is assumed. -/
theorem family_has_degree_five_stabilizer (k : ℕ) (hk : 0 < k)
    (M : Matrix (Fin (11 * k)) (Fin (11 * k)) K[X])
    (P : Matrix (Fin (8 * k)) (Fin (11 * k)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (hrow : RowIndependent P) :
    ∃ (X : Matrix (Fin (11 * k)) (Fin (11 * k)) K[X])
      (U : Matrix (Fin (11 * k)) (Fin (8 * k)) K[X]),
      X ≠ 0 ∧ DegreeBound X 5 ∧ DegreeBound U 5 ∧ TraceZeroStabilizer M P X U := by
  apply exists_degree_five_stabilizer M P hM hP hrow
  · simp only [Fintype.card_fin]
    omega
  · simp only [Fintype.card_fin]
    omega

end FD56
