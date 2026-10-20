module

public import P161Formal.SourceFeedDivision

/-! A uniform actual-source feed tilt. Chemical feed/drain terms retain the
fuel occupation dependence. Complete divisions add one proved rate allowance;
the exact800000000 stock exponent still stays below-20. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019 CF3Marked
open scoped BigOperators Classical
noncomputable section

def sourceFeedRechargePart (seed : ℝ) (x : SourceState (literalSourcePar seed)) : ℝ :=
  ∑ i : SiteId, (if (x i).R then 0 else 4000000)*
    sourceFuelWitness (Function.update x i {x i with R := true})

def sourceFeedTiltedGenerator (seed : ℝ) (x : SourceState (literalSourcePar seed)) : ℝ :=
  FunctionalCapacity.cf3Gen (literalSourcePar seed) sourceFuelWitness x+
    (Real.exp stockEta-1)*sourceFeedRechargePart seed x

theorem source_fuel_generator_parts (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    FunctionalCapacity.cf3Gen (literalSourcePar seed) sourceFuelWitness x =
      (∑ i : SiteId, sourceSiteChemicalFuelDrift seed x i)+sourceFuelDivisionDrift seed x := by
  rw [←source_generator sourceFuelWitness x]
  unfold sourceSiteChemicalFuelDrift sourceFuelDivisionDrift
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourceIntensity,sourceNext]

theorem source_feed_tilted_generator_parts (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    sourceFeedTiltedGenerator seed x = sourceFeedChemicalTilt seed x+sourceFuelDivisionDrift seed x := by
  have he : (Real.exp stockEta-1)*sourceFeedRechargePart seed x =
      ∑ i : SiteId, (if (x i).R then 0 else 4000000)*(Real.exp stockEta-1)*
        sourceFuelWitness (Function.update x i {x i with R := true}) := by
    rw [sourceFeedRechargePart,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [sourceFeedTiltedGenerator,source_fuel_generator_parts,he]
  unfold sourceFeedChemicalTilt sourceSiteFeedChemicalTilt
  rw [Finset.sum_add_distrib]
  ring

theorem source_feed_chemical_four_kappa (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    sourceFeedChemicalTilt seed x ≤ sourceFuelWitness x*(4*stockFeedK1) := by
  have hd : 0 ≤ Real.exp stockS-1 := by
    have h := Real.add_one_le_exp stockS
    have hs := stock_tilt_parameters.1
    linarith
  have hchem : (18457600 : ℝ)*(Real.exp stockS-1) ≤ stockFeedK1 := by
    have hcoef : (18457600 : ℝ) ≤ 18457604+3*Real.exp stockS := by
      have he := Real.exp_nonneg stockS
      linarith
    exact (mul_le_mul_of_nonneg_right hcoef hd).trans stock_feed_tilt_entries.2
  have hfeed := stock_feed_tilt_entries.1
  have hF0 : (0 : ℝ) ≤ sourceFuelCount x := Nat.cast_nonneg _
  have hF4 : (sourceFuelCount x : ℝ) ≤ 4 := by
    exact_mod_cast total_fuel_at_most_four (fun i => (x i).R)
  have h1 := mul_le_mul_of_nonneg_left hfeed (show (0 : ℝ) ≤ 4-(sourceFuelCount x : ℝ) by linarith)
  have h2 := mul_le_mul_of_nonneg_left hchem hF0
  have hsum : 18457600*(sourceFuelCount x : ℝ)*(Real.exp stockS-1)+
      4000000*(4-(sourceFuelCount x : ℝ))*(Real.exp (stockEta-stockS)-1) ≤ 4*stockFeedK1 := by
    nlinarith
  exact (source_feed_chemical_bound seed x).trans
    (mul_le_mul_of_nonneg_left hsum (fuel_occupation_positive _).le)

theorem source_feed_tilted_generator_bound (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) :
    sourceFeedTiltedGenerator seed x ≤ (4*stockFeedK1+1)*sourceFuelWitness x := by
  rw [source_feed_tilted_generator_parts]
  nlinarith [source_feed_chemical_four_kappa seed x,source_division_fuel_drift_bound seed hseed x]

end
end P161Formal
