/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile

/-! Three bounded Hilbert tests and a global slope bound determine adjacent degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem hasMinimalKernelDegrees_adjacent_of_bounds
    {K x y : Type*} [Field K] [Fintype y] [DecidableEq y]
    (F : Matrix x y K[X]) (D A B C : ℕ) (hD : 0 < D)
    (hzero : Module.finrank K (polynomialKernelAtDegree F (D-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree F D)=A)
    (hlater : 3*A+2*B ≤ Module.finrank K (polynomialKernelAtDegree F (D+2)))
    (hupper : ∀ d, Module.finrank K (polynomialKernelAtDegree F d) ≤ (A+B)*(d+1)+C) :
    HasMinimalKernelDegrees F (List.replicate A D ++ List.replicate B (D+1)) := by
  classical
  obtain ⟨r,Bf,e,hB,hL,_,hH⟩ := polynomial_kernel_has_minimal_basis F
  have he : ∀ i, D ≤ e i := by
    intro i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (D-1+1-e j))
      (Finset.mem_univ i)
    rw [← hH,hzero] at hi
    omega
  have hcard : r ≤ A+B := by
    let T := ∑ i, e i
    let d := T+C
    have hi : ∀ i, e i ≤ d+1 := by
      intro i
      have hh := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
      dsimp [d,T]
      omega
    have heq : Module.finrank K (polynomialKernelAtDegree F d)+T=r*(d+1) := by
      rw [hH]
      dsimp only [T]
      rw [← Finset.sum_add_distrib]
      simp only [Nat.sub_add_cancel (hi _),Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,smul_eq_mul]
    have hu := hupper d
    by_contra hh
    have hr : A+B+1 ≤ r := by omega
    have hm := Nat.mul_le_mul_right (d+1) hr
    dsimp [d] at heq hu hm
    nlinarith
  have hterm : ∀ i, D+2+1-e i ≤ 2+(D+1-e i) := by
    intro i; have := he i; omega
  have hcrit : (∑ i, (D+1-e i))=A := by rw [← hH,hcritical]
  have hsum : (∑ i, (D+2+1-e i)) ≤ 2*r+A := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    simpa only [Finset.sum_add_distrib,hcrit,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,Nat.mul_comm] using hh
  rw [hH] at hlater
  have hr : r=A+B := by omega
  have hsumEq : (∑ i, (D+2+1-e i)) = ∑ i, (2+(D+1-e i)) := by
    simp only [Finset.sum_add_distrib,hcrit,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    omega
  have hupperDegree : ∀ i, e i ≤ D+1 := by
    intro i
    have ht := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => hterm j)).mp hsumEq i (Finset.mem_univ i)
    have := he i
    omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [hH]
  simp only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,
    smul_eq_mul]
  by_cases hd : d<D
  · have hzero' : ∀ i, d+1-e i=0 := by intro i; have := he i; omega
    have h0 : d+1-D=0 := by omega
    have h1 : d+1-(D+1)=0 := by omega
    simp [hzero',h0,h1]
  · have ht : ∀ i, d+1-e i=(d-D)+(D+1-e i) := by
      intro i; have := he i; have := hupperDegree i; omega
    simp only [ht,Finset.sum_add_distrib,hcrit,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,hr]
    have h0 : d+1-D=(d-D)+1 := by omega
    have h1 : d+1-(D+1)=d-D := by omega
    rw [h0,h1]
    ring

end FD56
