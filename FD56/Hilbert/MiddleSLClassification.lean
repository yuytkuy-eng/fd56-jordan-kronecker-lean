/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformBalancedSL
import FD56.Hilbert.MixedSLClassification
import FD56.Hilbert.MixedThreeSLClassification
import FD56.Hilbert.MixedTwoSLClassification

/-! Complete generic SL degree lists when the first auxiliary quotient is at least two. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def middleSLDegreeList (a u v : ℕ) : List ℕ :=
  if v = 0 then balancedDegreeList ((a^2+a+1)*u^2-1) ((a-1)*u^2+1)
  else if a = 2 then
    if u ≤ v then
      let A := u*(v-u)
      let B := 2*u^2+v^2
      let C := v*(2*u+v)
      let t := 7-C
      List.replicate (A+t) 5 ++ List.replicate (B+8-2*t) 6 ++ List.replicate (C-7) 7
    else
      let A := 3*u*v
      let B := u*(u-v)+3*v^2
      let C := v*(u-v)
      let t := 8-C
      List.replicate (A+t) 6 ++ List.replicate (B+9-2*t) 7 ++ List.replicate (C-8) 8
  else if a = 3 then
    let A := u*(u+3*v)
    let B := u^2+u*v+3*v^2
    let C := u*v
    let t := 8-C
    List.replicate (A+t) 6 ++ List.replicate (B+9-2*t) 7 ++ List.replicate (C-8) 8
  else
    let r := u+v
    let g := (a-4)*r+v
    let A := u*g
    let B := 3*u*r+v*g
    let C := 3*v*r
    let t := a+4-C
    List.replicate (A+t) (a+2) ++ List.replicate (B+a+5-2*t) (a+3) ++
      List.replicate (C-(a+4)) (a+4)

theorem generic_middle_sl_minimal_degrees_of_parameters {K : Type*} [Field K]
    (a u v : ℕ) (ha : 2 ≤ a) (hu : 0 < u)
    (i₀ : Fin ((a+1)*(u+v)+v)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a+1)*(u+v)+v)) (Fin (a*(u+v)+v)))
      (genericAffineRows K (Fin ((a+1)*(u+v)+v)) (Fin (a*(u+v)+v))) i₀)
      (middleSLDegreeList a u v) := by
  by_cases hv : v = 0
  · subst v
    simpa only [middleSLDegreeList,if_pos rfl,Nat.add_zero] using
      generic_uniform_middle_sl_balanced (K := K) a u ha hu i₀
  · have hvp : 0 < v := by omega
    by_cases ha2 : a = 2
    · subst a
      by_cases huv : u ≤ v
      · simpa only [middleSLDegreeList,if_neg hv,if_pos rfl,if_pos huv] using
          generic_mixed_two_sl_minimal_degrees_le (K := K) u v hu hvp huv i₀
      · simpa only [middleSLDegreeList,if_neg hv,if_pos rfl,if_neg huv] using
          generic_mixed_two_sl_minimal_degrees_gt (K := K) u v hu hvp (by omega) i₀
    · by_cases ha3 : a = 3
      · subst a
        simpa only [middleSLDegreeList,if_neg hv,if_neg ha2,if_pos rfl] using
          generic_mixed_three_sl_minimal_degrees (K := K) u v hu hvp i₀
      · simpa only [middleSLDegreeList,if_neg hv,if_neg ha2,if_neg ha3] using
          generic_mixed_sl_minimal_degrees (K := K) a u v (by omega) hu hvp i₀

theorem generic_middle_sl_minimal_degrees_of_twice_le {K : Type*} [Field K]
    (n m : ℕ) (hmn : m < n) (hnm : 2*n ≤ 3*m) (i₀ : Fin n) :
    let r := n-m
    let a := m/r
    let v := m%r
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin m))
      (genericAffineRows K (Fin n) (Fin m)) i₀)
      (middleSLDegreeList a (r-v) v) := by
  let r := n-m
  let a := m/r
  let v := m%r
  let u := r-v
  have hr : 0 < r := by dsimp [r]; omega
  have hv : v < r := Nat.mod_lt m hr
  have hu : 0 < u := Nat.sub_pos_of_lt hv
  have huv : u+v = r := Nat.sub_add_cancel hv.le
  have hsum : r+m = n := by dsimp [r]; omega
  have ha : 2 ≤ a := by
    apply (Nat.le_div_iff_mul_le hr).mpr
    dsimp [r]
    omega
  have hm : a*(u+v)+v = m := by
    rw [huv]
    simpa only [a,v,Nat.mul_comm] using Nat.div_add_mod m r
  have hn : (a+1)*(u+v)+v = n := by
    nlinarith only [hm,huv,hsum]
  have h := generic_middle_sl_minimal_degrees_of_parameters (K := K) a u v ha hu
  rw [hm,hn] at h
  exact h i₀

end FD56
