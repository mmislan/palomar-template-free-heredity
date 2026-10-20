module

public import P161Formal.SourceServiceChemical

/-! Full literal beta4m service drift, using the source one-site generator
identity. Parent and victim ledgers keep their spatial-slot semantics. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def serviceGapPotential (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℝ :=
  (1-serviceFuelWeight s.R)*serviceZ^(s.q j)

theorem service_gap_nonnegative (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) :
    0 ≤ serviceGapPotential s j := by
  unfold serviceGapPotential
  exact mul_nonneg (sub_nonneg.mpr (service_fuel_weight_bounds s.R).2.1)
    (service_power_bounds (s.q j)).1.le

theorem service_first_daughter_bound (seed : ℝ) (s : FunctionalCapacity.Site 3 2048)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048) (j : SpeciesId) :
    serviceSitePotential ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td s k) o) j ≤ serviceZ^(s.q j) := by
  cases k with
  | none =>
      change serviceFuelWeight (s.R && o.2)*serviceZ^(s.q j) ≤ serviceZ^(s.q j)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (service_fuel_weight_bounds (s.R && o.2)).2.1 (service_power_bounds (s.q j)).1.le
  | some l =>
      by_cases h : j = l
      · subst l
        simpa [serviceSitePotential,serviceFuelWeight,FunctionalCapacity.cf3] using
          service_power_succ_le (s.q j)
      · simp [serviceSitePotential,serviceFuelWeight,FunctionalCapacity.cf3,h]

theorem service_victim_daughter_bound (seed : ℝ)
    (parent victim : FunctionalCapacity.Site 3 2048) (k : Option SpeciesId)
    (o : FunctionalCapacity.Split 3 2048) (j : SpeciesId) :
    serviceSitePotential ((FunctionalCapacity.cf3 (literalSourcePar seed)).merge victim
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
        ((FunctionalCapacity.cf3 (literalSourcePar seed)).td parent k) o)) j ≤ serviceZ^(victim.q j) := by
  change serviceFuelWeight
    (((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td parent k) o).R)*
        serviceZ^(victim.q j) ≤ serviceZ^(victim.q j)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (service_fuel_weight_bounds _).2.1 (service_power_bounds (victim.q j)).1.le

theorem service_first_daughter_delta (seed : ℝ) (s : FunctionalCapacity.Site 3 2048)
    (k : Option SpeciesId) (o : FunctionalCapacity.Split 3 2048) (j : SpeciesId) :
    serviceSitePotential ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td s k) o) j-serviceSitePotential s j ≤
        serviceGapPotential s j := by
  have h := service_first_daughter_bound seed s k o j
  unfold serviceGapPotential
  change _-serviceFuelWeight s.R*serviceZ^(s.q j) ≤ _
  nlinarith

theorem service_victim_daughter_delta (seed : ℝ)
    (parent victim : FunctionalCapacity.Site 3 2048) (k : Option SpeciesId)
    (o : FunctionalCapacity.Split 3 2048) (j : SpeciesId) :
    serviceSitePotential ((FunctionalCapacity.cf3 (literalSourcePar seed)).merge victim
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
        ((FunctionalCapacity.cf3 (literalSourcePar seed)).td parent k) o)) j-
          serviceSitePotential victim j ≤ serviceGapPotential victim j := by
  have h := service_victim_daughter_bound seed parent victim k o j
  unfold serviceGapPotential
  change _-serviceFuelWeight victim.R*serviceZ^(victim.q j) ≤ _
  nlinarith

theorem service_split_average_le (seed : ℝ) (s : FunctionalCapacity.Site 3 2048)
    (f : FunctionalCapacity.Split 3 2048 → ℝ) (c : ℝ) (hf : ∀ o, f o ≤ c) :
    (∑ o, (FunctionalCapacity.cf3 (literalSourcePar seed)).ps s o*f o) ≤ c := by
  calc
    _ ≤ ∑ o, (FunctionalCapacity.cf3 (literalSourcePar seed)).ps s o*c :=
      Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left (hf o)
        (FunctionalCapacity.cf3_ps_nonneg (p := literalSourcePar seed) s o))
    _ = c := by
      rw [←Finset.sum_mul,FunctionalCapacity.cf3_ps_sum (p := literalSourcePar seed) s,one_mul]

theorem source_service_generator_bound (seed : ℝ)
    (x : CTMCHeredity20261019.SourceState (literalSourcePar 0))
    (i : SiteId) (j : SpeciesId) (hfloor : 16 ≤ ((x i).a j).val) :
    FunctionalCapacity.cf3Gen (literalSourcePar seed) (sourceServicePotential i j) x ≤
      -serviceTheta*sourceServicePotential i j x := by
  let m := FunctionalCapacity.cf3 (literalSourcePar seed)
  let c := serviceGapPotential (x i) j
  have hc : 0 ≤ c := service_gap_nonnegative (x i) j
  have hnu (s : FunctionalCapacity.Site 3 2048) :
      (∑ k : Option SpeciesId, m.rd s k) ≤ 4 := by
    have h := FunctionalCapacity.cf3_rd_sum_le (p := literalSourcePar seed) s
    norm_num only [literalSourcePar,Nat.cast_ofNat] at h
    norm_num at h
    exact h
  have hout : (∑ k : Option SpeciesId, m.rd (x i) k *
      ∑ o, m.ps (m.td (x i) k) o *
        (serviceSitePotential (m.d1 (m.td (x i) k) o) j-serviceSitePotential (x i) j)) ≤ 4*c := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left
        (service_split_average_le seed (m.td (x i) k) _ c
          (fun o => service_first_daughter_delta seed (x i) k o j))
        (FunctionalCapacity.cf3_rd_nonneg (p := literalSourcePar seed) (x i) k))
    rw [←Finset.sum_mul] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (hnu (x i)) hc)
  have hin_each (l : SiteId) : (∑ k : Option SpeciesId, m.rd (x l) k *
      ∑ o, m.ps (m.td (x l) k) o * ((1/((4 : ℝ)-1))*
        (serviceSitePotential (m.merge (x i) (m.d2 (m.td (x l) k) o)) j-
          serviceSitePotential (x i) j))) ≤ (1/((4 : ℝ)-1))*(4*c) := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left
        (service_split_average_le seed (m.td (x l) k) _ ((1/((4 : ℝ)-1))*c)
          (fun o => mul_le_mul_of_nonneg_left
            (service_victim_daughter_delta seed (x l) (x i) k o j) (by norm_num)))
        (FunctionalCapacity.cf3_rd_nonneg (p := literalSourcePar seed) (x l) k))
    rw [←Finset.sum_mul] at h
    have hn := mul_le_mul_of_nonneg_right (hnu (x l))
      (show 0 ≤ (1/((4 : ℝ)-1))*c by positivity)
    nlinarith
  have hin : (∑ l : SiteId, if l = i then 0 else
      ∑ k : Option SpeciesId, m.rd (x l) k *
        ∑ o, m.ps (m.td (x l) k) o * ((1/((4 : ℝ)-1))*
          (serviceSitePotential (m.merge (x i) (m.d2 (m.td (x l) k) o)) j-
            serviceSitePotential (x i) j))) ≤ 4*c := by
    calc
      _ ≤ ∑ l : SiteId, if l = i then 0 else (1/((4 : ℝ)-1))*(4*c) := by
        apply Finset.sum_le_sum
        intro l _
        split_ifs
        · exact le_rfl
        · exact hin_each l
      _ = 4*c := FunctionalCapacity.sum_victim_const (M := 4) (by norm_num) i (4*c)
  have hchem := source_service_chemical_and_division_allowance seed (x i) j hfloor
  unfold sourceServiceSiteChemical at hchem
  change FunctionalCapacity.popGen m 4 (fun z => serviceSitePotential (z i) j) x ≤
    -serviceTheta*serviceSitePotential (x i) j
  rw [FunctionalCapacity.popGen_single m 4 (by norm_num) i (fun s => serviceSitePotential s j) x]
  dsimp only [c,serviceGapPotential,m] at hout hin
  nlinarith

end
end P161Formal
