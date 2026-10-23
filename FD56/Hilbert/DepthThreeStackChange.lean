/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoStackChange
import FD56.Stabilizer.ObservabilityMatrix

/-! Polynomial row changes for the third observability stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

def depthThreeStack (P Q R : Matrix m n K[X]) : Matrix ((m ⊕ m) ⊕ m) n K[X] :=
  Matrix.fromRows (depthTwoStack P Q) R

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem depthThreeStack_mulVec_zero_iff (P Q R : Matrix m n K[X]) (v : n → K[X]) :
    depthThreeStack P Q R *ᵥ v = 0 ↔ P *ᵥ v = 0 ∧ Q *ᵥ v = 0 ∧ R *ᵥ v = 0 := by
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (Sum.inl (Sum.inl i))),
      funext (fun i => congrFun h (Sum.inl (Sum.inr i))),
      funext (fun i => congrFun h (Sum.inr i))⟩
  · rintro ⟨hP,hQ,hR⟩
    funext i
    rcases i with (i | i) | i
    · exact congrFun hP i
    · exact congrFun hQ i
    · exact congrFun hR i

omit [Fintype m] [DecidableEq m] in
theorem observability_three_mulVec_zero_iff (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (v : n → K[X]) :
    observabilityMatrix M P 3 *ᵥ v = 0 ↔
      P *ᵥ v = 0 ∧ (P*M) *ᵥ v = 0 ∧ (P*M^2) *ᵥ v = 0 := by
  have happ (i : Fin 3) (j : m) :
      (observabilityMatrix M P 3 *ᵥ v) (i,j) = ((P*M^i.val) *ᵥ v) j := rfl
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · funext j
      simpa only [happ,Fin.val_zero,pow_zero,Matrix.mul_one,Pi.zero_apply] using
        congrFun h (0,j)
    · funext j
      simpa only [happ,Fin.val_one,pow_one,Pi.zero_apply] using congrFun h (1,j)
    · funext j
      exact congrFun h (2,j)
  · rintro ⟨hP,hPM,hPMM⟩
    funext i
    obtain ⟨i,j⟩ := i
    fin_cases i
    · simpa only [happ,Fin.val_zero,pow_zero,Matrix.mul_one,Pi.zero_apply] using congrFun hP j
    · simpa only [happ,Fin.val_one,pow_one,Pi.zero_apply] using congrFun hPM j
    · exact congrFun hPMM j

theorem depthThree_stack_change_kernel
    (M : Matrix n n K[X]) (P Q R : Matrix m n K[X])
    (A D E : Matrix m m K[X]) (S : Matrix m (m ⊕ m) K[X])
    (hED : E*D=1) (hPM : P*M=A*P+D*Q)
    (hQM : Q*M=R+S*depthTwoStack P Q) (v : n → K[X]) :
    observabilityMatrix M P 3 *ᵥ v = 0 ↔ depthThreeStack P Q R *ᵥ v = 0 := by
  rw [observability_three_mulVec_zero_iff,depthThreeStack_mulVec_zero_iff]
  have hD (w : m → K[X]) (hw : D *ᵥ w=0) : w=0 := by
    have hh := congrArg (fun z => E *ᵥ z) hw
    simpa only [Matrix.mulVec_mulVec,hED,Matrix.one_mulVec,Matrix.mulVec_zero] using hh
  have hstack (hP : P *ᵥ v=0) (hQ : Q *ᵥ v=0) : depthTwoStack P Q *ᵥ v=0 := by
    funext i
    cases i with
    | inl i => exact congrFun hP i
    | inr i => exact congrFun hQ i
  have hterm : P*M^2=A*(P*M)+D*(Q*M) := by
    calc
      P*M^2=(P*M)*M := by rw [pow_two,Matrix.mul_assoc]
      _=(A*P+D*Q)*M := by rw [hPM]
      _=A*(P*M)+D*(Q*M) := by rw [Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_assoc]
  constructor
  · rintro ⟨hP,hPMv,hPMMv⟩
    have hQ : Q *ᵥ v=0 := by
      apply hD
      simpa only [hPM,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hP,
        Matrix.mulVec_zero,zero_add] using hPMv
    have hQMv : (Q*M) *ᵥ v=0 := by
      apply hD
      simpa only [hterm,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hPMv,
        Matrix.mulVec_zero,zero_add] using hPMMv
    refine ⟨hP,hQ,?_⟩
    simpa only [hQM,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hstack hP hQ,
      Matrix.mulVec_zero,add_zero] using hQMv
  · rintro ⟨hP,hQ,hR⟩
    have hPMv : (P*M) *ᵥ v=0 := by
      simp only [hPM,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hP,hQ,
        Matrix.mulVec_zero,add_zero]
    have hQMv : (Q*M) *ᵥ v=0 := by
      simp only [hQM,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hstack hP hQ,hR,
        Matrix.mulVec_zero,add_zero]
    refine ⟨hP,hPMv,?_⟩
    simp only [hterm,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hPMv,hQMv,
      Matrix.mulVec_zero,add_zero]

theorem depthThree_stack_change_bounded_kernel
    (M : Matrix n n K[X]) (P Q R : Matrix m n K[X])
    (A D E : Matrix m m K[X]) (S : Matrix m (m ⊕ m) K[X])
    (hED : E*D=1) (hPM : P*M=A*P+D*Q)
    (hQM : Q*M=R+S*depthTwoStack P Q) (d : ℕ) :
    polynomialKernelAtDegree (observabilityMatrix M P 3) d =
      polynomialKernelAtDegree (depthThreeStack P Q R) d := by
  ext v
  exact depthThree_stack_change_kernel M P Q R A D E S hED hPM hQM _

end FD56
