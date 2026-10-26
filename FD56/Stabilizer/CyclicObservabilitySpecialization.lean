/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityMatrix
import FD56.LinearAlgebra.MaximalMinorColumnOperations
import FD56.LinearAlgebra.GenericEndpointCyclic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Cyclic output specializations bound common observability divisors. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {R K : Type*} [CommRing R] [Field K] {n : ℕ}

def cyclicMatrixAt (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (c : Fin (n+1)) :
    Matrix (Fin (n+1)) (Fin (n+1)) R := fun i j => (M^i.val) c j

def cyclicOutputRows (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (c : Fin (n+1))
    (q m : ℕ) : Matrix (Fin m) (Fin (n+1)) R := fun j k => (M^(q*j.val)) c k

def cyclicObservabilityRow (q m : ℕ) (h : q*m ≤ n+1) :
    Fin q × Fin m → Fin (n+1) := fun ij => ⟨q*ij.2.val+ij.1.val,by
      have hi := ij.1.isLt
      have hj := ij.2.isLt
      nlinarith⟩

theorem cyclicObservabilityRow_injective (q m : ℕ) (h : q*m ≤ n+1) :
    Function.Injective (cyclicObservabilityRow q m h) := by
  intro i j he
  have hv : q*i.2.val+i.1.val = q*j.2.val+j.1.val := congrArg Fin.val he
  have hi : i.1 = j.1 := by
    apply Fin.ext
    have hemod := congrArg (fun z => z % q) hv
    simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt i.1.isLt,Nat.mod_eq_of_lt j.1.isLt] using hemod
  have hj : i.2 = j.2 := by
    apply Fin.ext
    have hpos : 0 < q := Nat.zero_lt_of_lt i.1.isLt
    have hm : q*i.2.val = q*j.2.val := by simpa [hi] using hv
    exact Nat.eq_of_mul_eq_mul_left hpos hm
  exact Prod.ext hi hj

theorem observability_cyclic_output (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (c : Fin (n+1)) (q m : ℕ) (h : q*m ≤ n+1) :
    observabilityMatrix M (cyclicOutputRows M c q m) q =
      (cyclicMatrixAt M c).submatrix (cyclicObservabilityRow q m h) id := by
  funext ij k
  change (∑ x, (M^(q*ij.2.val)) c x * (M^ij.1.val) x k) =
    (M^(q*ij.2.val+ij.1.val)) c k
  rw [pow_add,Matrix.mul_apply]

theorem cyclic_observability_common_divisor_dvd_power
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (c : Fin (n+1))
    (q m : ℕ) (h : q*m ≤ n+1) (d : R)
    (hd : ∀ r : Fin q × Fin m → Fin (n+1),
      d ∣ ((observabilityMatrix M (cyclicOutputRows M c q m) q).submatrix id r).det) :
    d ∣ (cyclicMatrixAt M c).det^(q*m) := by
  let C := cyclicMatrixAt M c
  let e := cyclicObservabilityRow q m h
  let B := C.adjugate.submatrix id e
  have hAB : observabilityMatrix M (cyclicOutputRows M c q m) q * B =
      C.det • (1 : Matrix (Fin q × Fin m) (Fin q × Fin m) R) := by
    rw [observability_cyclic_output M c q m h]
    change C.submatrix e (Equiv.refl _) * C.adjugate.submatrix (Equiv.refl _) e = _
    rw [Matrix.submatrix_mul_equiv,Matrix.mul_adjugate]
    change C.det • (1 : Matrix (Fin (n+1)) (Fin (n+1)) R).submatrix e e = _
    rw [Matrix.submatrix_one e (cyclicObservabilityRow_injective q m h)]
  have hh := dvd_power_of_rectangular_product_eq_scalar _ B C.det d hAB hd
  simpa only [Fintype.card_prod,Fintype.card_fin] using hh

theorem universal_state_common_divisor_isUnit
    (q m : ℕ) (h : q*m ≤ n+1)
    (d : MvPolynomial (Fin (n+1) × Fin (n+1)) K)
    (hd : ∀ P : Matrix (Fin m) (Fin (n+1)) (MvPolynomial (Fin (n+1) × Fin (n+1)) K),
      ∀ r : Fin q × Fin m → Fin (n+1),
        d ∣ ((observabilityMatrix (cyclicVariableMatrix id) P q).submatrix id r).det) : IsUnit d := by
  apply generic_endpoint_cyclic_powers_common_divisor_isUnit (q*m) (q*m) d
  · exact cyclic_observability_common_divisor_dvd_power _ 0 q m h d (hd _)
  · exact cyclic_observability_common_divisor_dvd_power _ (Fin.last n) q m h d (hd _)

end FD56
