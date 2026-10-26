/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DisjointVariableDivisors
import FD56.Stabilizer.ObservabilityMatrix
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fintype.EquivFin

/-! Maximal minors of diagonal observability matrices with independent output entries. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
open scoped BigOperators

variable {K n m : Type*} [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def diagonalGenericObservability (ev : n → K) (q : ℕ) :
    Matrix (Fin q × m) n (MvPolynomial (m × n) K) :=
  fun ka j => X (ka.2, j) * C ((ev j) ^ ka.1.val)

omit [Fintype m] [DecidableEq m] in
theorem diagonalGenericObservability_eq (ev : n → K) (q : ℕ) :
    diagonalGenericObservability (m := m) ev q =
      observabilityMatrix (Matrix.diagonal (fun j => C (ev j)))
        (fun a j => X (a,j)) q := by
  ext ka j
  simp [diagonalGenericObservability,observabilityMatrix,Matrix.diagonal_pow,
    Matrix.mul_diagonal,map_pow]

omit [Fintype n] [DecidableEq n] in
theorem diagonal_generic_observability_minor_ne_zero
    (ev : n → K) (hev : Function.Injective ev) (q : ℕ)
    (r : (Fin q × m) ↪ n) :
    ((diagonalGenericObservability ev q).submatrix id r).det ≠ 0 := by
  classical
  let p : m × n → K := fun aj =>
    Function.extend r (fun kb => if aj.1 = kb.2 then 1 else 0) (fun _ => 0) aj.2
  let φ : MvPolynomial (m × n) K →+* K := MvPolynomial.eval₂Hom (RingHom.id K) p
  let V : m → Matrix (Fin q) (Fin q) K :=
    fun a => (Matrix.vandermonde (fun k => ev (r (k,a)))).transpose
  have he : ((diagonalGenericObservability ev q).submatrix id r).map φ =
      Matrix.blockDiagonal V := by
    funext ka kb
    simp only [Matrix.map_apply,Matrix.submatrix_apply,id_eq,
      diagonalGenericObservability,φ,map_mul,MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C,RingHom.id_apply,Matrix.blockDiagonal_apply,
      V,Matrix.transpose_apply,Matrix.vandermonde_apply]
    dsimp only [p]
    rw [r.injective.extend_apply]
    split_ifs with h
    · simp only [one_mul,h,Prod.eta]
    · simp
  have hd : (Matrix.blockDiagonal V).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    dsimp only [V]
    rw [Matrix.det_transpose]
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j hij
    exact congrArg Prod.fst (r.injective (hev hij))
  intro hz
  apply hd
  rw [← he]
  have hh := RingHom.map_det φ ((diagonalGenericObservability ev q).submatrix id r)
  rw [hz,map_zero] at hh
  exact hh.symm

theorem mvPolynomial_det_degreeOf_eq_zero
    {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : σ) (A : Matrix ι ι (MvPolynomial σ K))
    (hA : ∀ a b, (A a b).degreeOf j = 0) : A.det.degreeOf j = 0 := by
  let e := coordinatePolynomialEquiv (R := K) j
  let B : Matrix ι ι (MvPolynomial {i : σ // i ≠ j} K) := fun a b => (e (A a b)).coeff 0
  have hm : A.map e.toRingHom = B.map Polynomial.C := by
    funext a b
    change e (A a b) = Polynomial.C ((e (A a b)).coeff 0)
    apply Polynomial.eq_C_of_natDegree_le_zero
    rw [coordinatePolynomialEquiv_natDegree,hA]
  have hd : e A.det = Polynomial.C B.det := by
    calc
      e A.det = (A.map e.toRingHom).det := RingHom.map_det e.toRingHom A
      _ = (B.map Polynomial.C).det := congrArg Matrix.det hm
      _ = Polynomial.C B.det := (Polynomial.C.map_det B).symm
  rw [← coordinatePolynomialEquiv_natDegree j A.det]
  change (e A.det).natDegree = 0
  rw [hd,Polynomial.natDegree_C]

omit [Fintype n] in
theorem diagonal_generic_observability_minor_omits_column
    (ev : n → K) (q : ℕ) (r : (Fin q × m) → n)
    (j : n) (hr : ∀ ka, r ka ≠ j) (a : m) :
    (((diagonalGenericObservability ev q).submatrix id r).det).degreeOf (a,j) = 0 := by
  apply mvPolynomial_det_degreeOf_eq_zero
  intro ka kb
  apply Nat.eq_zero_of_le_zero
  apply (MvPolynomial.degreeOf_mul_le (a,j) _ _).trans
  have hne : (a,j) ≠ (ka.2,r kb) := by
    intro he
    exact hr kb (congrArg Prod.snd he).symm
  simp only [MvPolynomial.degreeOf_X,id_eq,if_neg hne,MvPolynomial.degreeOf_C,zero_add]
  exact le_rfl

theorem diagonal_generic_observability_common_divisor_isUnit
    (ev : n → K) (hev : Function.Injective ev) (q : ℕ)
    (hn : q * Fintype.card m < Fintype.card n)
    (d : MvPolynomial (m × n) K)
    (hd : ∀ r : (Fin q × m) → n,
      d ∣ ((diagonalGenericObservability ev q).submatrix id r).det) : IsUnit d := by
  classical
  apply common_divisor_isUnit_of_variable_omissions
    (fun r : (Fin q × m) → n => ((diagonalGenericObservability ev q).submatrix id r).det)
    ?_ ?_ d hd
  · obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin q × m) ≤ Fintype.card n by
        simpa only [Fintype.card_prod,Fintype.card_fin] using hn.le)
    exact ⟨r,diagonal_generic_observability_minor_ne_zero ev hev q r⟩
  · rintro ⟨a,j⟩
    have hcard : Fintype.card {x : n // x ≠ j} = Fintype.card n - 1 := by
      simp
    obtain ⟨r⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin q × m) ≤ Fintype.card {x : n // x ≠ j} by
        rw [hcard,Fintype.card_prod,Fintype.card_fin]
        omega)
    let r' : (Fin q × m) ↪ n := r.trans (Function.Embedding.subtype _)
    refine ⟨r',diagonal_generic_observability_minor_ne_zero ev hev q r',?_⟩
    exact diagonal_generic_observability_minor_omits_column ev q r' j (fun ka => (r ka).property) a

end FD56
