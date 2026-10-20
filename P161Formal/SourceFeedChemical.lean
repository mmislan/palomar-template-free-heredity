module

public import P161Formal.SourceFuelTilt
public import P161Formal.ChemicalDriftBounds

/-! Exact chemical part of the accepted-feed/fuel occupation tilt. Seed and
passive-loss channels preserve fuel; recharge and every fueled consuming
channel are retained with their literal source rates. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019
open scoped BigOperators Classical
noncomputable section

theorem source_fuel_witness_update (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (i : SiteId) (s : FunctionalCapacity.Site 3 2048) :
    sourceFuelWitness (Function.update x i s) = sourceFuelWitness x*
      Real.exp (stockS*((bitFuel (x i).R : ℝ)-(bitFuel s.R : ℝ))) := by
  have hf : (fun j => (Function.update x i s j).R) =
      Function.update (fun j => (x j).R) i s.R := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  change fuelOccupationWitness (fun j => (Function.update x i s j).R) = _
  rw [hf,fuel_occupation_update]
  rfl

def sourceChemicalFuelLoad (s : FunctionalCapacity.Site 3 2048) : ℝ :=
  4000000+∑ j : SpeciesId,
    (4000000*((s.a j).val : ℝ)/2048+
      800*(s.a j).val*(1-((s.a j).val : ℝ)/2048)+400*(s.a j).val)

theorem source_chemical_fuel_load_bound (s : FunctionalCapacity.Site 3 2048) :
    sourceChemicalFuelLoad s ≤ 18457600 := by
  have h := Finset.sum_le_sum (fun (j : SpeciesId) (_ : j ∈ Finset.univ) =>
    single_foreign_chemical_rate_bound (s.a j))
  norm_num at h
  unfold sourceChemicalFuelLoad
  linarith

def sourceSiteChemicalFuelDrift (seed : ℝ) (x : SourceState (literalSourcePar seed)) (i : SiteId) : ℝ :=
  ∑ k : FunctionalCapacity.Chem 3,
    (FunctionalCapacity.cf3 (literalSourcePar seed)).rc (x i) k*
      (sourceFuelWitness (Function.update x i ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc (x i) k))-
        sourceFuelWitness x)

set_option backward.isDefEq.respectTransparency false in
theorem source_site_chemical_fuel_expansion (seed : ℝ)
    (x : SourceState (literalSourcePar seed)) (i : SiteId) :
    sourceSiteChemicalFuelDrift seed x i =
      if (x i).R then sourceChemicalFuelLoad (x i)*sourceFuelWitness x*(Real.exp stockS-1)
      else 4000000*sourceFuelWitness x*(Real.exp (-stockS)-1) := by
  rw [sourceSiteChemicalFuelDrift,FunctionalCapacity.cf3_chem_sum (literalSourcePar seed) (x i)
    (fun s => sourceFuelWitness (Function.update x i s)-sourceFuelWitness x)]
  simp_rw [source_fuel_witness_update seed x i]
  cases hr : (x i).R <;>
    norm_num [sourceChemicalFuelLoad,bitFuel,hr,literalSourcePar,FunctionalCapacity.Site.u,
      FunctionalCapacity.Site.r,Fin.sum_univ_three] <;> ring

def sourceSiteFeedChemicalTilt (seed : ℝ) (x : SourceState (literalSourcePar seed)) (i : SiteId) : ℝ :=
  sourceSiteChemicalFuelDrift seed x i+
    (if (x i).R then 0 else 4000000)*(Real.exp stockEta-1)*
      sourceFuelWitness (Function.update x i {x i with R := true})

theorem source_site_feed_chemical_expansion (seed : ℝ)
    (x : SourceState (literalSourcePar seed)) (i : SiteId) :
    sourceSiteFeedChemicalTilt seed x i =
      if (x i).R then sourceChemicalFuelLoad (x i)*sourceFuelWitness x*(Real.exp stockS-1)
      else 4000000*sourceFuelWitness x*(Real.exp (stockEta-stockS)-1) := by
  rw [sourceSiteFeedChemicalTilt,source_site_chemical_fuel_expansion,source_fuel_witness_update]
  have he : Real.exp stockEta*Real.exp (-stockS) = Real.exp (stockEta-stockS) := by
    rw [←Real.exp_add,sub_eq_add_neg]
  cases hr : (x i).R
  · norm_num only [hr,Bool.false_eq_true,ite_false,bitFuel,ite_true,Nat.cast_zero,Nat.cast_one,
      zero_sub,mul_neg,mul_one]
    calc
      _ = 4000000*sourceFuelWitness x*(Real.exp stockEta*Real.exp (-stockS)-1) := by ring
      _ = _ := by rw [he]
  · simp only [ite_true,zero_mul,add_zero]

theorem fuel_affine_sum (F : SiteId → Bool) (a b : ℝ) :
    (∑ i : SiteId, if F i then a else b) =
      (totalFuel F : ℝ)*a+(4-(totalFuel F : ℝ))*b := by
  have he (i : SiteId) : (if F i then a else b) =
      (bitFuel (F i) : ℝ)*a+(1-(bitFuel (F i) : ℝ))*b := by
    cases F i <;> norm_num [bitFuel]
  simp_rw [he]
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,Finset.sum_sub_distrib]
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  simp only [totalFuel,Nat.cast_sum]

def sourceFeedChemicalTilt (seed : ℝ) (x : SourceState (literalSourcePar seed)) : ℝ :=
  ∑ i : SiteId, sourceSiteFeedChemicalTilt seed x i

theorem source_feed_chemical_bound (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    sourceFeedChemicalTilt seed x ≤ sourceFuelWitness x*
      (18457600*(sourceFuelCount x : ℝ)*(Real.exp stockS-1)+
        4000000*(4-(sourceFuelCount x : ℝ))*(Real.exp (stockEta-stockS)-1)) := by
  have hd : 0 ≤ Real.exp stockS-1 := by
    have h := Real.add_one_le_exp stockS
    have hs := stock_tilt_parameters.1
    linarith
  have hW : 0 ≤ sourceFuelWitness x := (fuel_occupation_positive _).le
  calc
    _ ≤ ∑ i : SiteId, if (x i).R then
        18457600*sourceFuelWitness x*(Real.exp stockS-1)
      else 4000000*sourceFuelWitness x*(Real.exp (stockEta-stockS)-1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [source_site_feed_chemical_expansion]
      split_ifs
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (source_chemical_fuel_load_bound (x i)) hW) hd
      · exact le_rfl
    _ = _ := by
      rw [fuel_affine_sum]
      unfold sourceFuelCount
      ring

end
end P161Formal
