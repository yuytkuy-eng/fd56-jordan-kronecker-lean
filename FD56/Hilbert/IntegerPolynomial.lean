/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Integer coefficient certificates for polynomial identities. -/

namespace FD56
open Polynomial

def integerPolynomialAdd : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: integerPolynomialAdd as bs

def integerPolynomialMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => integerPolynomialAdd (b.map (a * ·)) (0 :: integerPolynomialMul as b)

def integerPolynomialTrim : List ℤ → List ℤ
  | [] => []
  | a :: as =>
    let t := integerPolynomialTrim as
    if t = [] ∧ a = 0 then [] else a :: t

noncomputable section
variable {K : Type*} [CommRing K]

def integerPolynomial (coefficients : List ℤ) : K[X] :=
  coefficients.foldr (fun (a : ℤ) p => (a : K[X]) + X * p) 0

@[simp] theorem integerPolynomial_nil : integerPolynomial (K := K) [] = 0 := rfl

theorem integerPolynomial_cons (a : ℤ) (as : List ℤ) :
    integerPolynomial (K := K) (a :: as) = (a : K[X]) + X * integerPolynomial as := rfl

@[simp] theorem integerPolynomial_singleton (a : ℤ) :
    integerPolynomial (K := K) [a] = a := by
  simp [integerPolynomial_cons]

theorem integerPolynomial_zero_cons (as : List ℤ) :
    integerPolynomial (K := K) (0 :: as) = X * integerPolynomial as := by
  simp [integerPolynomial_cons]

theorem integerPolynomial_add (as bs : List ℤ) :
    integerPolynomial (K := K) (integerPolynomialAdd as bs) =
      integerPolynomial as + integerPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [integerPolynomialAdd]
  | cons a as ih =>
    cases bs with
    | nil => simp [integerPolynomialAdd]
    | cons b bs =>
      simp only [integerPolynomialAdd,integerPolynomial_cons,ih,Int.cast_add]
      ring

theorem integerPolynomial_map_mul (a : ℤ) (bs : List ℤ) :
    integerPolynomial (K := K) (bs.map (a * ·)) = (a : K[X]) * integerPolynomial bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons,integerPolynomial_cons,ih,Int.cast_mul]
    ring

theorem integerPolynomial_mul (as bs : List ℤ) :
    integerPolynomial (K := K) (integerPolynomialMul as bs) =
      integerPolynomial as * integerPolynomial bs := by
  induction as with
  | nil => simp [integerPolynomialMul]
  | cons a as ih =>
    rw [integerPolynomialMul,integerPolynomial_add,integerPolynomial_map_mul,
      integerPolynomial_zero_cons,ih,integerPolynomial_cons]
    ring

theorem integerPolynomial_neg (as : List ℤ) :
    integerPolynomial (K := K) (as.map (- ·)) = -integerPolynomial as := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,integerPolynomial_cons,ih,Int.cast_neg]
    ring

theorem integerPolynomial_trim (as : List ℤ) :
    integerPolynomial (K := K) (integerPolynomialTrim as) = integerPolynomial as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    dsimp only [integerPolynomialTrim]
    split_ifs with h
    · rw [integerPolynomial_nil,integerPolynomial_cons,← ih,h.1,integerPolynomial_nil,h.2]
      simp
    · simp only [integerPolynomial_cons,ih]

theorem integerPolynomial_eq_of_trim_eq {as bs : List ℤ}
    (h : integerPolynomialTrim as = integerPolynomialTrim bs) :
    integerPolynomial (K := K) as = integerPolynomial bs := by
  rw [← integerPolynomial_trim as,← integerPolynomial_trim bs,h]

theorem integerPolynomial_coeff (as : List ℤ) (n : ℕ) :
    (integerPolynomial (K := K) as).coeff n = (as.getD n 0 : K) := by
  induction as generalizing n with
  | nil => simp [List.getD]
  | cons a as ih =>
    rw [integerPolynomial_cons,← Polynomial.C_eq_intCast (R := K) a,Polynomial.coeff_add]
    cases n with
    | zero => simp [List.getD,Polynomial.coeff_C]
    | succ n =>
      rw [Polynomial.coeff_C,Polynomial.coeff_X_mul,ih]
      simp [List.getD]

end
end FD56
