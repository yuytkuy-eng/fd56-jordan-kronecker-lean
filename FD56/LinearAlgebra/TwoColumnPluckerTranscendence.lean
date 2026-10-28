/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnUniversalFrame
import FD56.LinearAlgebra.SubalgebraGeneratorBound

/-! The coefficient algebra of universal balanced two-column minors has
at most m(W+2)-3 algebraically independent parameters. -/

noncomputable section
namespace FD56
open Polynomial

variable {K R L n : Type*} [Field K] [CommRing R] [Algebra K R]
  [Field L] [Algebra K L] [Fintype n]

def twoColumnMinorCoefficientAlgebra (K : Type*) [Field K] [Algebra K R]
    (u v : n → R[X]) : Subalgebra K R :=
  Algebra.adjoin K (Set.range (fun z : n × n × ℕ => (u z.1*v z.2.1-u z.2.1*v z.1).coeff z.2.2))

private def normalizedCoefficients (a b : ℕ) (u v : n → L[X]) :
    TwoColumnCoefficientIndex n a b → L :=
  Sum.elim (fun ik => (u ik.1).coeff ik.2.val) (fun ik => (v ik.1).coeff ik.2.val)

private theorem minor_algebra_bound_of_normalization
    (φ : R →ₐ[K] L) (hφ : Function.Injective φ) (u v : n → R[X])
    (a b : ℕ) (u' v' : n → L[X]) (c : L)
    (hu : ∀ i, (u' i).natDegree≤a) (hv : ∀ i, (v' i).natDegree≤b)
    (hminor : ∀ i j, (u i).map φ.toRingHom*(v j).map φ.toRingHom-
      (u j).map φ.toRingHom*(v i).map φ.toRingHom=C c*(u' i*v' j-u' j*v' i))
    (S : Finset (TwoColumnCoefficientIndex n a b))
    (hfixed : ∀ z ∈ S, normalizedCoefficients a b u' v' z ∈ Set.range (algebraMap K L)) :
    Algebra.trdeg K (twoColumnMinorCoefficientAlgebra K u v) ≤
      (Fintype.card (TwoColumnCoefficientIndex n a b)-S.card+1 : ℕ) := by
  classical
  let A := twoColumnMinorCoefficientAlgebra K u v
  let x := normalizedCoefficients a b u' v'
  let T := Algebra.adjoin K (insert c (Set.range x))
  have hx (z) : x z ∈ T := Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_range_self z))
  have hc : c ∈ T := Algebra.subset_adjoin (Set.mem_insert _ _)
  have huT (i : n) (k : ℕ) : (u' i).coeff k ∈ T := by
    by_cases hk : k≤a
    · exact hx (Sum.inl (i,⟨k,by omega⟩))
    · rw [coeff_eq_zero_of_natDegree_lt ((hu i).trans_lt (by omega))]
      exact T.zero_mem
  have hvT (i : n) (k : ℕ) : (v' i).coeff k ∈ T := by
    by_cases hk : k≤b
    · exact hx (Sum.inr (i,⟨k,by omega⟩))
    · rw [coeff_eq_zero_of_natDegree_lt ((hv i).trans_lt (by omega))]
      exact T.zero_mem
  have hA : A ≤ T.comap φ := by
    apply Algebra.adjoin_le
    rintro y ⟨⟨i,j,k⟩,rfl⟩
    change φ ((u i*v j-u j*v i).coeff k) ∈ T
    have h := congrArg (fun p : L[X] => p.coeff k) (hminor i j)
    dsimp only at h
    rw [← Polynomial.map_mul,← Polynomial.map_mul,← Polynomial.map_sub,coeff_map] at h
    change φ ((u i*v j-u j*v i).coeff k)=(C c*(u' i*v' j-u' j*v' i)).coeff k at h
    rw [h]
    exact scaled_two_column_minor_coeff_mem T c u' v' hc huT hvT i j k
  exact trdeg_le_card_sub_fixed_add_one (φ.comp A.val)
    (hφ.comp Subtype.val_injective) x c S hfixed (fun z => hA z.property)

theorem two_column_universal_equal_trdeg (K n : Type*) [Field K] [Fintype n]
    (a : ℕ) (i₀ i₁ : n) (hi : i₀≠i₁) :
    Algebra.trdeg K (twoColumnMinorCoefficientAlgebra K
      (twoColumnUniversalU K n a a) (twoColumnUniversalV K n a a)) ≤
      (Fintype.card n*(2*a+2)-3 : ℕ) := by
  classical
  let R := TwoColumnCoefficientRing K n a a
  let L := TwoColumnCoefficientField K n a a
  obtain ⟨u',v',c,_,hu,hv,hu0,hu1,hv0,hv1,hminor⟩ :=
    two_column_equal_normalization (twoColumnFractionU K n a a)
      (twoColumnFractionV K n a a) a i₀ i₁
      (twoColumnFractionU_degree K n a a) (twoColumnFractionV_degree K n a a)
      (two_column_fraction_pivots K n a a i₀ i₁ hi).2
  let S : Finset (TwoColumnCoefficientIndex n a a) :=
    {Sum.inl (i₀,Fin.last a),Sum.inl (i₁,Fin.last a),
      Sum.inr (i₀,Fin.last a),Sum.inr (i₁,Fin.last a)}
  have hScard : S.card=4 := by simp [S,hi,Ne.symm hi]
  have hfixed : ∀ z ∈ S, normalizedCoefficients a a u' v' z ∈ Set.range (algebraMap K L) := by
    intro z hz
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨1,by simpa [normalizedCoefficients] using hu0.symm⟩
    · exact ⟨0,by simpa [normalizedCoefficients] using hu1.symm⟩
    · exact ⟨0,by simpa [normalizedCoefficients] using hv0.symm⟩
    · exact ⟨1,by simpa [normalizedCoefficients] using hv1.symm⟩
  have h := minor_algebra_bound_of_normalization (IsScalarTower.toAlgHom K R L)
    (IsFractionRing.injective R L) (twoColumnUniversalU K n a a)
    (twoColumnUniversalV K n a a) a a u' v' c hu hv hminor S hfixed
  rw [hScard] at h
  have hcard : Fintype.card (TwoColumnCoefficientIndex n a a)=Fintype.card n*(2*a+2) := by
    simp only [TwoColumnCoefficientIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    ring
  rw [hcard] at h
  have hfour : 4≤Fintype.card n*(2*a+2) := by
    have hh := Finset.card_le_univ S
    rwa [hScard,hcard] at hh
  convert h using 1 <;> congr 1 <;> omega

theorem two_column_universal_adjacent_trdeg (K n : Type*) [Field K] [Fintype n]
    (a : ℕ) (i₀ i₁ : n) (hi : i₀≠i₁) :
    Algebra.trdeg K (twoColumnMinorCoefficientAlgebra K
      (twoColumnUniversalU K n a (a+1)) (twoColumnUniversalV K n a (a+1))) ≤
      (Fintype.card n*(2*a+3)-3 : ℕ) := by
  classical
  let R := TwoColumnCoefficientRing K n a (a+1)
  let L := TwoColumnCoefficientField K n a (a+1)
  have hp := two_column_fraction_pivots K n a (a+1) i₀ i₁ hi
  obtain ⟨u',v',c,_,hu,hv,hu0,hvtop,hv0,hv1,hminor⟩ :=
    two_column_adjacent_normalization (twoColumnFractionU K n a (a+1))
      (twoColumnFractionV K n a (a+1)) a i₀ i₁
      (twoColumnFractionU_degree K n a (a+1)) (twoColumnFractionV_degree K n a (a+1)) hp.1 hp.2
  let S : Finset (TwoColumnCoefficientIndex n a (a+1)) :=
    {Sum.inl (i₀,Fin.last a),Sum.inr (i₀,Fin.last (a+1)),
      Sum.inr (i₀,(Fin.last a).castSucc),Sum.inr (i₁,Fin.last (a+1))}
  have hlast : Fin.last (a+1) ≠ (Fin.last a).castSucc := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_last,Fin.coe_castSucc] at hh
    omega
  have hScard : S.card=4 := by simp [S,hi,Ne.symm hi,hlast,Ne.symm hlast]
  have hfixed : ∀ z ∈ S, normalizedCoefficients a (a+1) u' v' z ∈ Set.range (algebraMap K L) := by
    intro z hz
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨1,by simpa [normalizedCoefficients] using hu0.symm⟩
    · exact ⟨0,by simpa [normalizedCoefficients] using hvtop.symm⟩
    · exact ⟨0,by simpa [normalizedCoefficients] using hv0.symm⟩
    · exact ⟨1,by simpa [normalizedCoefficients] using hv1.symm⟩
  have h := minor_algebra_bound_of_normalization (IsScalarTower.toAlgHom K R L)
    (IsFractionRing.injective R L) (twoColumnUniversalU K n a (a+1))
    (twoColumnUniversalV K n a (a+1)) a (a+1) u' v' c hu hv hminor S hfixed
  rw [hScard] at h
  have hcard : Fintype.card (TwoColumnCoefficientIndex n a (a+1))=Fintype.card n*(2*a+3) := by
    simp only [TwoColumnCoefficientIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    ring
  rw [hcard] at h
  have hfour : 4≤Fintype.card n*(2*a+3) := by
    have hh := Finset.card_le_univ S
    rwa [hScard,hcard] at hh
  convert h using 1 <;> congr 1 <;> omega

end FD56
