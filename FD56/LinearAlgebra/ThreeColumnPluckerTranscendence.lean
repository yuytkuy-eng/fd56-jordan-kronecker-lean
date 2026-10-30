/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ThreeColumnUniversalFrame
import FD56.LinearAlgebra.SubalgebraGeneratorBound
import Mathlib.Algebra.Polynomial.Lifts

/-! A universal equal-degree three-column minor algebra has at most
3m(h+1)-8 algebraically independent coefficients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

def threeColumnMinorCoefficientAlgebra (K : Type*) [Field K]
    {R n : Type*} [CommRing R] [Algebra K R] (G : Matrix n (Fin 3) R[X]) : Subalgebra K R :=
  Algebra.adjoin K (Set.range (fun z : (Fin 3 → n) × ℕ => (pluckerMinorVector G z.1).coeff z.2))

private theorem minor_coeff_mem {K L n : Type*} [Field K] [CommRing L] [Algebra K L]
    (T : Subalgebra K L) (G : Matrix n (Fin 3) L[X])
    (hG : ∀ i j k, (G i j).coeff k ∈ T) (row : Fin 3 → n) (k : ℕ) :
    (pluckerMinorVector G row).coeff k ∈ T := by
  have hlift (i : n) (j : Fin 3) : ∃ p : T[X], p.map T.val.toRingHom=G i j := by
    apply (Polynomial.mem_lifts _).mp
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro l
    exact ⟨⟨_,hG i j l⟩,rfl⟩
  choose H hH using hlift
  have he : (pluckerMinorVector H row).map T.val.toRingHom=pluckerMinorVector G row := by
    calc
      _ = ((Matrix.submatrix H row id).map (Polynomial.mapRingHom T.val.toRingHom)).det :=
        (Polynomial.mapRingHom T.val.toRingHom).map_det _
      _ = _ := by
        apply congrArg Matrix.det
        apply Matrix.ext
        intro i j
        exact hH (row i) j
  have hc := congrArg (fun p : L[X] => p.coeff k) he
  dsimp only at hc
  rw [Polynomial.coeff_map] at hc
  rw [← hc]
  exact ((pluckerMinorVector H row).coeff k).property

private theorem minor_algebra_bound_of_normalization
    {K R L n : Type*} [Field K] [CommRing R] [Algebra K R]
    [Field L] [Algebra K L] [Fintype n]
    (φ : R →ₐ[K] L) (hφ : Function.Injective φ) (G : Matrix n (Fin 3) R[X])
    (h : ℕ) (H : Matrix n (Fin 3) L[X]) (c : L)
    (hH : ∀ i j, (H i j).natDegree≤h)
    (hminor : ∀ row, (pluckerMinorVector G row).map φ.toRingHom=C c*pluckerMinorVector H row)
    (S : Finset (ThreeColumnCoefficientIndex n h))
    (hfixed : ∀ z ∈ S, (H z.1 z.2.1).coeff z.2.2.val ∈ Set.range (algebraMap K L)) :
    Algebra.trdeg K (threeColumnMinorCoefficientAlgebra K G) ≤
      (Fintype.card (ThreeColumnCoefficientIndex n h)-S.card+1 : ℕ) := by
  classical
  let A := threeColumnMinorCoefficientAlgebra K G
  let x : ThreeColumnCoefficientIndex n h → L := fun z => (H z.1 z.2.1).coeff z.2.2.val
  let T := Algebra.adjoin K (insert c (Set.range x))
  have hx z : x z ∈ T := Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_range_self z))
  have hc : c ∈ T := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hHT (i : n) (j : Fin 3) (k : ℕ) : (H i j).coeff k ∈ T := by
    by_cases hk : k≤h
    · exact hx (i,j,⟨k,by omega⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hH i j).trans_lt (by omega))]
      exact T.zero_mem
  have hA : A≤T.comap φ := by
    apply Algebra.adjoin_le
    rintro y ⟨⟨row,k⟩,rfl⟩
    change φ ((pluckerMinorVector G row).coeff k) ∈ T
    have he := congrArg (fun p : L[X] => p.coeff k) (hminor row)
    dsimp only at he
    rw [Polynomial.coeff_map,Polynomial.coeff_C_mul] at he
    change φ ((pluckerMinorVector G row).coeff k) = c*(pluckerMinorVector H row).coeff k at he
    rw [he]
    exact T.mul_mem hc (minor_coeff_mem T H hHT row k)
  exact trdeg_le_card_sub_fixed_add_one (φ.comp A.val)
    (hφ.comp Subtype.val_injective) x c S hfixed (fun z => hA z.property)

theorem three_column_universal_equal_trdeg (K n : Type*) [Field K] [Fintype n]
    (h : ℕ) (pivot : Fin 3 ↪ n) :
    Algebra.trdeg K (threeColumnMinorCoefficientAlgebra K (threeColumnUniversalFrame K n h)) ≤
      (3*Fintype.card n*(h+1)-8 : ℕ) := by
  classical
  let R := ThreeColumnCoefficientRing K n h
  let L := ThreeColumnCoefficientField K n h
  obtain ⟨H,c,_,hH,hfixed,hminor⟩ := three_column_equal_normalization
    (threeColumnFractionFrame K n h) h pivot (threeColumnFractionFrame_degree K n h)
    (three_column_fraction_pivot_ne_zero K n h pivot)
  let f : Fin 3 × Fin 3 → ThreeColumnCoefficientIndex n h :=
    fun z => (pivot z.1,z.2,Fin.last h)
  let S := Finset.univ.image f
  have hf : Function.Injective f := by
    intro i j he
    apply Prod.ext
    · exact pivot.injective (congrArg Prod.fst he)
    · exact congrArg (fun z : ThreeColumnCoefficientIndex n h => z.2.1) he
  have hScard : S.card=9 := by
    rw [Finset.card_image_of_injective _ hf]
    decide
  have hfix : ∀ z ∈ S, (H z.1 z.2.1).coeff z.2.2.val ∈ Set.range (algebraMap K L) := by
    intro z hz
    obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨(1 : Matrix (Fin 3) (Fin 3) K) ij.1 ij.2,?_⟩
    change algebraMap K L ((1 : Matrix (Fin 3) (Fin 3) K) ij.1 ij.2)=(H (pivot ij.1) ij.2).coeff h
    rw [hfixed]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hmap (row : Fin 3 → n) :
      (pluckerMinorVector (threeColumnUniversalFrame K n h) row).map (algebraMap R L)=
        pluckerMinorVector (threeColumnFractionFrame K n h) row := by
    simpa only [pluckerMinorVector,RingHom.mapMatrix_apply] using
      (Polynomial.mapRingHom (algebraMap R L)).map_det
        ((threeColumnUniversalFrame K n h).submatrix row id)
  have hb := minor_algebra_bound_of_normalization (IsScalarTower.toAlgHom K R L)
    (IsFractionRing.injective R L) (threeColumnUniversalFrame K n h) h H c hH
    (fun row => (hmap row).trans (hminor row)) S hfix
  have hcard : Fintype.card (ThreeColumnCoefficientIndex n h)=3*Fintype.card n*(h+1) := by
    simp only [ThreeColumnCoefficientIndex,Fintype.card_prod,Fintype.card_fin]
    ring
  have hlarge : 9≤3*Fintype.card n*(h+1) := by
    have hs := Finset.card_le_univ S
    rwa [hScard,hcard] at hs
  rw [hScard,hcard,show 3*Fintype.card n*(h+1)-9+1=3*Fintype.card n*(h+1)-8 by omega] at hb
  exact hb

end FD56
