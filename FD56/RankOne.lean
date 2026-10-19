import FD56.PolynomialMatrix

/-! The rank-one construction in Section 6.3, over any field. -/

noncomputable section
open Matrix Polynomial

namespace FD56
variable {R : Type*} [CommRing R] [IsDomain R]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Polynomial row independence; full row rank over the fraction field implies this. -/
def RowIndependent (P : Matrix m n R) : Prop :=
  ∀ w : Matrix Unit m R, w * P = 0 → w = 0

omit [Fintype n] in
theorem outer_product_ne_zero {v : Matrix n Unit R} {w : Matrix Unit n R}
    (hv : v ≠ 0) (hw : w ≠ 0) : v * w ≠ 0 := by
  intro h
  have hv' : ∃ i, v i () ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hv
    ext i j
    cases j
    exact hn i
  have hw' : ∃ j, w () j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hw
    ext i j
    cases i
    exact hn j
  obtain ⟨i, hi⟩ := hv'
  obtain ⟨j, hj⟩ := hw'
  have hij := congrFun (congrFun h i) j
  simp [Matrix.mul_apply, hi, hj] at hij

omit [IsDomain R] in
/-- The identities hold over an arbitrary commutative ring, without genericity. -/
theorem rankOne_stabilizer
    (M : Matrix n n R) (P : Matrix m n R)
    (v : Matrix n Unit R) (w D : Matrix Unit m R)
    (hv : P * v = 0) (hw : w * P * M = D * P) :
    P * (v * w * P) = 0 ∧
    M * (v * w * P) - (v * w * P) * M = (M * v * w - v * D) * P ∧
    Matrix.trace (v * w * P) = 0 := by
  constructor
  · calc
      P * (v * w * P) = (P * v) * w * P := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hv]; simp
  constructor
  · calc
      M * (v * w * P) - (v * w * P) * M =
          (M * v * w) * P - v * (w * P * M) := by simp only [Matrix.mul_assoc]
      _ = (M * v * w) * P - v * (D * P) := by rw [hw]
      _ = (M * v * w - v * D) * P := by simp only [Matrix.sub_mul, Matrix.mul_assoc]
  · calc
      Matrix.trace (v * w * P) = Matrix.trace ((w * P) * v) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace (w * (P * v)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hv]; simp

omit [Fintype n] in
theorem rankOne_nonzero (P : Matrix m n R) (hP : RowIndependent P)
    (v : Matrix n Unit R) (w : Matrix Unit m R) (hv : v ≠ 0) (hw : w ≠ 0) :
    v * w * P ≠ 0 := by
  rw [Matrix.mul_assoc]
  apply outer_product_ne_zero hv
  intro h
  exact hw (hP w h)

omit [IsDomain R] in
theorem rowIndependent_of_right_inverse [DecidableEq m]
    (P : Matrix m n R) (Q : Matrix n m R) (hPQ : P * Q = 1) : RowIndependent P := by
  intro w hw
  calc
    w = w * (P * Q) := by rw [hPQ, Matrix.mul_one]
    _ = (w * P) * Q := (Matrix.mul_assoc w P Q).symm
    _ = 0 := by rw [hw, Matrix.zero_mul]

end FD56
