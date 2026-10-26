/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLNormalForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Scalar commutators raise the observability filtration. No integer is inverted. -/

noncomputable section
namespace FD56
open Matrix Polynomial

section Ring
variable {R n m r : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n]

theorem scalar_commutator_on_observability_kernel
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R) (V : Matrix n r R)
    (q : ℕ) (hcomm : M*X-X*M=U*P+c • 1)
    (hV : ∀ j<q, P*M^j*V=0) (i : ℕ) (hi : i<q) :
    M^(i+1)*X*V=X*M^(i+1)*V+(i+1) • (c • (M^i*V)) := by
  have hstep (j : ℕ) (hj : j<q) :
      M*X*M^j*V=X*M^(j+1)*V+c • (M^j*V) := by
    have he := congrArg (fun Y : Matrix n n R => Y*M^j*V) hcomm
    have hz : U*P*M^j*V=0 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P, hV j hj,
        Matrix.mul_zero]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
      hz, zero_add] at he
    have hh := (sub_eq_iff_eq_add).mp he
    simpa only [pow_succ', Matrix.mul_assoc, add_comm] using hh
  induction i with
  | zero => simpa using hstep 0 hi
  | succ i ih =>
    have hp : M^(i+1+1)*X*V=M*(M^(i+1)*X*V) := by
      rw [pow_succ']; simp only [Matrix.mul_assoc]
    rw [hp, ih (by omega), Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
    have ht : M*(X*M^(i+1)*V)=X*M^(i+1+1)*V+c • (M^(i+1)*V) := by
      simpa only [Matrix.mul_assoc] using hstep (i+1) hi
    rw [ht]
    have hm : M*(M^i*V)=M^(i+1)*V := by rw [pow_succ']; simp only [Matrix.mul_assoc]
    rw [hm]
    simp only [add_nsmul, one_nsmul]
    abel

theorem scalar_commutator_raises_observability
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R)
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1)
    (q : ℕ) (V : Matrix n r R) (hV : ∀ j<q, P*M^j*V=0) :
    ∀ j<q+1, P*M^j*(X*V)=0 := by
  intro j hj
  cases j with
  | zero => simp only [pow_zero, Matrix.mul_one, ← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  | succ i =>
    calc
      P*M^(i+1)*(X*V)=P*(M^(i+1)*X*V) := by simp only [Matrix.mul_assoc]
      _ = P*(X*M^(i+1)*V+(i+1) • (c • (M^i*V))) := by
        rw [scalar_commutator_on_observability_kernel M P X U c V q hcomm hV i (by omega)]
      _ = 0 := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
        simp only [← Matrix.mul_assoc, hPX, Matrix.zero_mul, hV i (by omega),
          smul_zero, add_zero]

theorem scalar_commutator_power_observability
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R)
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1) (q : ℕ) :
    ∀ j<q, P*M^j*X^q=0 := by
  induction q with
  | zero => intro j hj; omega
  | succ q ih =>
    simpa only [← pow_succ'] using
      scalar_commutator_raises_observability M P X U c hPX hcomm q (X^q) ih

theorem observable_scalar_commutator_pow_eq_zero
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R)
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1)
    (q : ℕ) (hO : Function.Injective (observabilityMatrix M P q).mulVec) :
    X^q=0 := by
  have hz : observabilityMatrix M P q*X^q=0 := by
    funext i j
    exact congrFun (congrFun
      (scalar_commutator_power_observability M P X U c hPX hcomm q i.1.val i.1.isLt) i.2) j
  exact matrix_left_mul_injective_of_mulVec _ hO (hz.trans (Matrix.mul_zero _).symm)

theorem observable_scalar_commutator_nilpotent
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R)
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1)
    (q : ℕ) (hO : Function.Injective (observabilityMatrix M P q).mulVec) :
    IsNilpotent X :=
  ⟨q,observable_scalar_commutator_pow_eq_zero M P X U c hPX hcomm q hO⟩

theorem observable_scalar_commutator_trace_zero [IsReduced R]
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R)
    (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1)
    (q : ℕ) (hO : Function.Injective (observabilityMatrix M P q).mulVec) :
    Matrix.trace X=0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent
    (observable_scalar_commutator_nilpotent M P X U c hPX hcomm q hO)).eq_zero

theorem scalar_commutator_annihilates_observability_kernel
    (M : Matrix n n R) (P : Matrix m n R)
    (X : Matrix n n R) (U : Matrix n m R) (c : R) (V : Matrix n r R)
    (q : ℕ) (hPX : P*X=0) (hcomm : M*X-X*M=U*P+c • 1)
    (hV : ∀ j<q, P*M^j*V=0)
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec) : X*V=0 := by
  have hz : observabilityMatrix M P (q+1)*(X*V)=0 := by
    funext i j
    exact congrFun (congrFun
      (scalar_commutator_raises_observability M P X U c hPX hcomm q V hV
        i.1.val i.1.isLt) i.2) j
  exact matrix_left_mul_injective_of_mulVec _ hO (hz.trans (Matrix.mul_zero _).symm)

end Ring
end FD56
