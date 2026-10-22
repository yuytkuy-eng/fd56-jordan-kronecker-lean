/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleGL

/-! The full SL equations reduce to a scalar relation on the first
polynomial kernel module. The scalar correction is retained throughout. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def middleSLX (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P))) (E : Matrix r m K[X]) :
    Matrix n n K[X] := polynomialKernelBasisMatrix P B * E * P

def middleSLTranslation (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (E : Matrix r m K[X]) (c : K[X]) : Matrix n m K[X] :=
  (M * middleSLX P B E - middleSLX P B E * M - c • 1) * R

omit [DecidableEq r] in
theorem middleSLX_injective (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) : Function.Injective (middleSLX P B) := by
  intro E F h
  have hh := congrArg (fun X : Matrix n n K[X] => X * R) h
  simp only [middleSLX, Matrix.mul_assoc, hPR, Matrix.mul_one] at hh
  exact matrix_left_mul_injective_of_mulVec _ (polynomialKernelBasisMatrix_injective P B) hh

theorem middle_sl_forward
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X])
    (hPX : P * X = 0) (hcomm : M * X - X * M = U * P + c • 1) :
    ∃! E : Matrix r m K[X],
      E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 ∧
      X = middleSLX P B E ∧ U = middleSLTranslation M P B R E c := by
  let V := polynomialKernelBasisMatrix P B
  have hV := polynomialKernelBasisMatrix_injective P B
  have hPV : P * V = 0 := polynomialKernelBasisMatrix_mul P B
  obtain ⟨C, hC⟩ := matrix_factor_through_kernel_basis P B X hPX
  change X = V * C at hC
  have hGC : (P * M * V) * (C * V) = 0 := by
    have hh := congrArg (fun Z : Matrix n n K[X] => P * Z * V) hcomm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, hPV, Matrix.mul_zero, smul_zero, add_zero] at hh
    rw [← Matrix.mul_assoc P X, hPX, Matrix.zero_mul, sub_zero] at hh
    simpa only [hC, Matrix.mul_assoc] using hh
  have hCV : C * V = 0 := matrix_left_mul_injective_of_mulVec _ hG
    (hGC.trans (Matrix.mul_zero _).symm)
  have hCP : C = (C * R) * P := row_factor_through_of_kernel_basis P B R hPR C hCV
  let E := C * R
  have hXE : X = V * E * P := by rw [hC, hCP]; simp only [E, Matrix.mul_assoc]
  have hEG : E * (P * M * V) = (-c) • 1 := by
    have hh := congrArg (fun Z : Matrix n n K[X] => Z * V) hcomm
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_assoc, hPV, Matrix.mul_zero, zero_add] at hh
    have hXV : X * V = 0 := by rw [hXE]; simp [Matrix.mul_assoc, hPV]
    rw [hXV, Matrix.mul_zero, zero_sub] at hh
    have hv : -(V * (E * (P * M * V))) = c • V := by
      simpa only [hXE, Matrix.mul_assoc] using hh
    apply matrix_left_mul_injective_of_mulVec V hV
    change V * (E * (P * M * V)) = V * ((-c) • (1 : Matrix r r K[X]))
    rw [Matrix.mul_smul, Matrix.mul_one, neg_smul]
    exact (neg_eq_iff_eq_neg.mp hv)
  have hres : M * X - X * M - c • 1 = U * P := by rw [hcomm]; abel
  have hu : U = middleSLTranslation M P B R E c := by
    unfold middleSLTranslation
    change U = (M * (V * E * P) - (V * E * P) * M - c • 1) * R
    rw [← hXE, hres, Matrix.mul_assoc, hPR, Matrix.mul_one]
  refine ⟨E, ⟨hEG, hXE, hu⟩, ?_⟩
  intro F hF
  exact middleSLX_injective P B R hPR (hF.2.1.symm.trans hXE)

theorem middle_sl_reconstruct
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (E : Matrix r m K[X]) (c : K[X])
    (hEG : E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1) :
    Matrix.trace (middleSLX P B E) = 0 ∧ P * middleSLX P B E = 0 ∧
      M * middleSLX P B E - middleSLX P B E * M =
        middleSLTranslation M P B R E c * P + c • 1 := by
  let V := polynomialKernelBasisMatrix P B
  let X := middleSLX P B E
  let S := M * X - X * M - c • (1 : Matrix n n K[X])
  have hPV : P * V = 0 := polynomialKernelBasisMatrix_mul P B
  have htr : Matrix.trace X = 0 := by
    change Matrix.trace (V * E * P) = 0
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc P V, hPV,
      Matrix.zero_mul, Matrix.trace_zero]
  have hPX : P * X = 0 := by
    change P * (V * E * P) = 0
    simp [← Matrix.mul_assoc, hPV]
  have hXV : X * V = 0 := by
    change V * E * P * V = 0
    simp [Matrix.mul_assoc, hPV]
  have hSV : S * V = 0 := by
    dsimp only [S]
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_assoc M, hXV, Matrix.mul_zero, zero_sub]
    have he : X * M * V = V * ((-c) • (1 : Matrix r r K[X])) := by
      change V * E * P * M * V = _
      simpa only [Matrix.mul_assoc] using congrArg (fun Z : Matrix r r K[X] => V * Z) hEG
    rw [he, Matrix.mul_smul, Matrix.mul_one, neg_smul, neg_neg, sub_self]
  have hfactor : S = (S * R) * P := row_factor_through_of_kernel_basis P B R hPR S hSV
  refine ⟨htr, hPX, ?_⟩
  change M * X - X * M = (S * R) * P + c • 1
  rw [← hfactor]
  dsimp only [S]
  abel

theorem middle_sl_equations_iff
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]) :
    (P * X = 0 ∧ M * X - X * M = U * P + c • 1) ↔
      ∃! E : Matrix r m K[X],
        E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 ∧
        X = middleSLX P B E ∧ U = middleSLTranslation M P B R E c := by
  constructor
  · rintro ⟨hPX, hcomm⟩
    exact middle_sl_forward M P B R hPR hG X U c hPX hcomm
  · rintro ⟨E, ⟨hEG, rfl, rfl⟩, _⟩
    exact (middle_sl_reconstruct M P B R hPR E c hEG).2

theorem middle_sl_radical_iff [Nonempty n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    SLRadical M P X U ↔ ∃ (E : Matrix r m K[X]) (c : K[X]),
      E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 ∧
      X = middleSLX P B E ∧ U = middleSLTranslation M P B R E c := by
  rw [slRadical_iff_equations]
  constructor
  · rintro ⟨_, hPX, c, hc⟩
    obtain ⟨E, hE, _⟩ := middle_sl_forward M P B R hPR hG X U c hPX hc
    exact ⟨E, c, hE⟩
  · rintro ⟨E, c, hEG, rfl, rfl⟩
    obtain ⟨htr, hPX, hc⟩ := middle_sl_reconstruct M P B R hPR E c hEG
    exact ⟨htr, hPX, c, hc⟩

end FD56
