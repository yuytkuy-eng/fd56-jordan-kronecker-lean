/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PredictableDegree
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Basis.Basic

/-! A finite polynomial basis can be chosen with independent leading columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem identity_updateCol_det {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (j : ι) (c : ι → R) : ((1 : Matrix ι ι R).updateCol j c).det = c j := by
  have hh := Matrix.det_updateCol_sum (1 : Matrix ι ι R) j c
  simpa [Matrix.one_apply] using hh

def basisReplaceColumn {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (B : Basis ι R V) (j : ι) (c : ι → R) (hc : c j = 1) :
    Basis ι R V :=
  B.map (Matrix.toLinearEquiv B ((1 : Matrix ι ι R).updateCol j c)
    (by rw [identity_updateCol_det, hc]; exact isUnit_one))

theorem basisReplaceColumn_self {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (B : Basis ι R V) (j : ι) (c : ι → R) (hc : c j = 1) :
    basisReplaceColumn B j c hc j = ∑ i, c i • B i := by
  simp [basisReplaceColumn, Matrix.toLin_self]

theorem basisReplaceColumn_of_ne {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (B : Basis ι R V) (j : ι) (c : ι → R) (hc : c j = 1)
    (i : ι) (hi : i ≠ j) : basisReplaceColumn B j c hc i = B i := by
  simp [basisReplaceColumn, Matrix.toLin_self, Matrix.updateCol_apply, hi, Matrix.one_apply]

variable {K n ι : Type*} [Field K] [Fintype n] [Fintype ι] [DecidableEq ι]

def polynomialVectorDegree (v : n → K[X]) : ℕ := Finset.univ.sup (fun i => (v i).natDegree)

theorem polynomialVectorDegree_bound (v : n → K[X]) (i : n) :
    (v i).natDegree ≤ polynomialVectorDegree v :=
  Finset.le_sup (f := fun i => (v i).natDegree) (Finset.mem_univ i)

theorem polynomialVectorDegree_lt_of_top_zero (v : n → K[X]) (e : ℕ)
    (hv : v ≠ 0) (hb : ∀ i, (v i).natDegree ≤ e) (hz : ∀ i, (v i).coeff e = 0) :
    polynomialVectorDegree v < e := by
  have hp (i : n) (hi : v i ≠ 0) : (v i).natDegree < e := by
    have hne : (v i).natDegree ≠ e := by
      intro he
      have hh := hz i
      rw [← he, Polynomial.coeff_natDegree] at hh
      exact Polynomial.leadingCoeff_ne_zero.mpr hi hh
    exact lt_of_le_of_ne (hb i) hne
  have he : 0 < e := by
    by_contra hn
    apply hv
    funext i
    by_contra hi
    have hh := hp i hi
    omega
  have hall : ∀ i, (v i).natDegree ≤ e - 1 := by
    intro i
    by_cases hi : v i = 0
    · simp [hi]
    · have hh := hp i hi; omega
  have hh : polynomialVectorDegree v ≤ e - 1 := Finset.sup_le (fun i _ => hall i)
  omega

theorem basis_degree_lowering (S : Submodule K[X] (n → K[X])) (B : Basis ι K[X] S)
    (c : ι → K) (hc : c ≠ 0)
    (hzero : (show Matrix n ι K from fun i j =>
      ((B j).val i).coeff (polynomialVectorDegree (B j).val)) *ᵥ c = 0) :
    ∃ B' : Basis ι K[X] S,
      (∑ j, polynomialVectorDegree (B' j).val) < ∑ j, polynomialVectorDegree (B j).val := by
  classical
  let e : ι → ℕ := fun j => polynomialVectorDegree (B j).val
  let supp := Finset.univ.filter (fun i => c i ≠ 0)
  have hsupp : supp.Nonempty := by
    by_contra h
    apply hc
    funext i
    by_contra hi
    change c i ≠ 0 at hi
    exact h ⟨i, by simp [supp, hi]⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup supp hsupp e
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hej (i : ι) (hi : c i ≠ 0) : e i ≤ e j := by
    rw [← hmax]
    exact Finset.le_sup (by simp [supp, hi])
  let a : ι → K[X] := fun i => Polynomial.C (c i / c j) * Polynomial.X ^ (e j - e i)
  have haj : a j = 1 := by simp [a, hcj]
  let B' := basisReplaceColumn B j a haj
  have hsame (i : ι) (hi : i ≠ j) : B' i = B i := basisReplaceColumn_of_ne B j a haj i hi
  have hexpr (x : n) : ((B' j).val x) = ∑ i, a i * (B i).val x := by
    dsimp only [B']
    rw [basisReplaceColumn_self]
    simp
  have hb (x : n) : ((B' j).val x).natDegree ≤ e j := by
    rw [hexpr]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    by_cases hi : c i = 0
    · simp [a, hi]
    · have he := hej i hi
      have ha : (a i).natDegree ≤ e j - e i := Polynomial.natDegree_C_mul_X_pow_le _ _
      have hv : ((B i).val x).natDegree ≤ e i := polynomialVectorDegree_bound (B i).val x
      exact Polynomial.natDegree_mul_le.trans (by omega)
  have hz (x : n) : ((B' j).val x).coeff (e j) = 0 := by
    rw [hexpr, Polynomial.finset_sum_coeff]
    have hterm (i : ι) : (a i * (B i).val x).coeff (e j) =
        (c i / c j) * ((B i).val x).coeff (e i) := by
      by_cases hi : c i = 0
      · simp [a, hi]
      · have he := hej i hi
        dsimp only [a]
        rw [mul_assoc, Polynomial.coeff_C_mul]
        congr 1
        conv_lhs => arg 2; rw [show e j = e i + (e j - e i) by omega]
        exact Polynomial.coeff_X_pow_mul _ _ _
    simp_rw [hterm]
    have hh := congrFun hzero x
    change ∑ i, ((B i).val x).coeff (e i) * c i = 0 at hh
    calc
      ∑ i, (c i / c j) * ((B i).val x).coeff (e i) =
          (∑ i, ((B i).val x).coeff (e i) * c i) / c j := by
            simp only [Finset.sum_div, div_mul_eq_mul_div, mul_comm]
      _ = 0 := by rw [hh]; simp
  have hne : (B' j).val ≠ 0 := by
    intro h
    exact B'.ne_zero j (Subtype.ext h)
  have hlt : polynomialVectorDegree (B' j).val < e j :=
    polynomialVectorDegree_lt_of_top_zero (B' j).val (e j) hne hb hz
  refine ⟨B', ?_⟩
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = j
    · subst i; exact le_of_lt hlt
    · rw [hsame i hi]
  · exact ⟨j, Finset.mem_univ j, hlt⟩

theorem exists_reduced_polynomial_basis (S : Submodule K[X] (n → K[X]))
    (B₀ : Basis ι K[X] S) :
    ∃ B : Basis ι K[X] S, Function.Injective (Matrix.mulVec
      (show Matrix n ι K from fun i j => ((B j).val i).coeff (polynomialVectorDegree (B j).val))) := by
  classical
  have hex : ∃ w : ℕ, ∃ B : Basis ι K[X] S, (∑ j, polynomialVectorDegree (B j).val) = w :=
    ⟨_, B₀, rfl⟩
  obtain ⟨B, hB⟩ := Nat.find_spec hex
  have hmin (B' : Basis ι K[X] S) :
      (∑ j, polynomialVectorDegree (B j).val) ≤ ∑ j, polynomialVectorDegree (B' j).val := by
    rw [hB]
    exact Nat.find_min' hex ⟨B', rfl⟩
  refine ⟨B, ?_⟩
  change Function.Injective (Matrix.toLin' (fun i j =>
    ((B j).val i).coeff (polynomialVectorDegree (B j).val)))
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  by_contra hne
  obtain ⟨B', hlt⟩ := basis_degree_lowering S B c hne hc
  exact (not_lt_of_ge (hmin B')) hlt

end FD56
