module

public import P161Formal.ServiceSourceParameters

/-! Exact source chemical drift of the service-credit witness. Seeding changes
counts only, so the identity holds for both literal seed phases. The8-rate
allowance below is reserved for parent/victim division impacts. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def serviceSitePotential (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℝ :=
  serviceFuelWeight s.R*serviceZ^(s.q j)

def sourceServiceSiteChemical (seed : ℝ) (s : FunctionalCapacity.Site 3 2048)
    (j : SpeciesId) : ℝ :=
  ∑ k : FunctionalCapacity.Chem 3, (FunctionalCapacity.cf3 (literalSourcePar seed)).rc s k*
    (serviceSitePotential ((FunctionalCapacity.cf3 (literalSourcePar seed)).tc s k) j-
      serviceSitePotential s j)

theorem source_service_site_chemical_expansion (seed : ℝ)
    (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    sourceServiceSiteChemical seed s j =
      if s.R then
        (4000000*((s.a j).val : ℝ)/2048*(serviceZ-serviceRho)+
          serviceUncreditedChemicalLoad s j*(1-serviceRho))*serviceZ^(s.q j)
      else 4000000*(serviceRho-1)*serviceZ^(s.q j) := by
  unfold sourceServiceSiteChemical
  rw [FunctionalCapacity.cf3_chem_sum (literalSourcePar seed) s
    (fun z => serviceSitePotential z j-serviceSitePotential s j)]
  simp only [Fin.sum_univ_three]
  fin_cases j <;> cases hR : s.R <;>
    norm_num [serviceSitePotential,serviceFuelWeight,serviceUncreditedChemicalLoad,
      serviceActiveConsumption,Finset.sum_erase_eq_sub (Finset.mem_univ _),
      literalSourcePar,FunctionalCapacity.Site.u,FunctionalCapacity.Site.r,hR,
      Function.update_apply,Fin.sum_univ_three,pow_succ]
  all_goals ring

theorem source_service_chemical_and_division_allowance (seed : ℝ)
    (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) (hfloor : 16 ≤ (s.a j).val) :
    sourceServiceSiteChemical seed s j+
      8*(1-serviceFuelWeight s.R)*serviceZ^(s.q j) ≤
        -serviceTheta*serviceSitePotential s j := by
  have hp := (service_power_bounds (s.q j)).1.le
  rw [source_service_site_chemical_expansion]
  cases hR : s.R
  · norm_num [serviceFuelWeight,serviceSitePotential,hR,serviceRho,serviceTheta]
  · have hload := service_uncredited_chemical_load_bound s j
    have hgap : 0 ≤ 1-serviceRho := by norm_num [serviceRho]
    have hloadMul := mul_le_mul_of_nonneg_right hload hgap
    have ha : (16 : ℝ) ≤ (s.a j).val := by exact_mod_cast hfloor
    have hdrift := service_fueled_live_drift ((s.a j).val : ℝ) ha
    have hlocal : 4000000*((s.a j).val : ℝ)/2048*(serviceZ-serviceRho)+
        serviceUncreditedChemicalLoad s j*(1-serviceRho)+8*(1-serviceRho) ≤
          -serviceTheta*serviceRho := by
      nlinarith
    have h := mul_le_mul_of_nonneg_right hlocal hp
    norm_num only [serviceFuelWeight,serviceSitePotential,hR,ite_true] at h ⊢
    nlinarith

end
end P161Formal
