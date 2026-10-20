module

public import P161Formal.SourceFeedChemical

/-! A uniform complete-division contribution to the fuel tilt. Each actual
operation changes at most two binary fuel slots, including both daughters and
the victim. This bound needs no independent-sister or split-support assumption.
The exact stock arithmetic has ample room for the resulting unit rate allowance. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019 CF3Marked
open scoped BigOperators Classical
noncomputable section

theorem source_fuel_update_upper (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (i : SiteId) (s : FunctionalCapacity.Site 3 2048) :
    sourceFuelWitness (Function.update x i s) ≤ sourceFuelWitness x*Real.exp stockS := by
  rw [source_fuel_witness_update]
  apply mul_le_mul_of_nonneg_left _ (fuel_occupation_positive _).le
  apply Real.exp_le_exp.mpr
  have hs := stock_tilt_parameters.1
  have h1 : (bitFuel (x i).R : ℝ) ≤ 1 := by cases (x i).R <;> norm_num [bitFuel]
  have h0 : (0 : ℝ) ≤ (bitFuel s.R : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem source_fuel_two_updates_upper (seed : ℝ) (x : SourceState (literalSourcePar seed))
    (i v : SiteId) (s t : FunctionalCapacity.Site 3 2048) :
    sourceFuelWitness (Function.update (Function.update x i s) v t) ≤
      sourceFuelWitness x*Real.exp (2*stockS) := by
  calc
    _ ≤ sourceFuelWitness (Function.update x i s)*Real.exp stockS :=
      source_fuel_update_upper seed _ v t
    _ ≤ (sourceFuelWitness x*Real.exp stockS)*Real.exp stockS :=
      mul_le_mul_of_nonneg_right (source_fuel_update_upper seed x i s) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_assoc,←Real.exp_add]
      congr 1
      congr 1
      ring

theorem source_complete_division_fuel_upper (seed : ℝ)
    (x : SourceState (literalSourcePar seed)) (i v : SiteId) (k : Option SpeciesId)
    (o : FunctionalCapacity.Split 3 2048) :
    sourceFuelWitness (divisionNext (literalSourcePar seed) x i k o v) ≤
      sourceFuelWitness x*Real.exp (2*stockS) :=
  source_fuel_two_updates_upper seed x i v
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).d1
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o)
    ((FunctionalCapacity.cf3 (literalSourcePar seed)).merge (x v)
      ((FunctionalCapacity.cf3 (literalSourcePar seed)).d2
        ((FunctionalCapacity.cf3 (literalSourcePar seed)).td (x i) k) o))

def sourceFuelDivisionDrift (seed : ℝ) (x : SourceState (literalSourcePar seed)) : ℝ :=
  ∑ i : SiteId, ∑ k : Option SpeciesId, ∑ z : FunctionalCapacity.Split 3 2048 × SiteId,
    sourceIntensity (literalSourcePar seed) x (Sum.inr (i,(k,z)))*
      (sourceFuelWitness (divisionNext (literalSourcePar seed) x i k z.1 z.2)-sourceFuelWitness x)

theorem stock_division_occupation_allowance : (16 : ℝ)*(Real.exp (2*stockS)-1) ≤ 1 := by
  have he := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 2*stockS by norm_num [stockS])
    (show (2 : ℝ)*stockS < 1 by norm_num [stockS])
  have hr : (16 : ℝ)*(1/(1-2*stockS)-1) ≤ 1 := by norm_num [stockS]
  nlinarith

theorem source_division_fuel_drift_bound (seed : ℝ) (hseed : 0 ≤ seed)
    (x : SourceState (literalSourcePar seed)) : sourceFuelDivisionDrift seed x ≤ sourceFuelWitness x := by
  let C : ℝ := sourceFuelWitness x*(Real.exp (2*stockS)-1)
  have hC : 0 ≤ C := by
    have hW := (fuel_occupation_positive (fun i => (x i).R)).le
    have he : 0 ≤ Real.exp (2*stockS)-1 := by
      have h := Real.add_one_le_exp (2*stockS)
      have hs := stock_tilt_parameters.1
      linarith
    exact mul_nonneg hW he
  have hrate : (∑ i : SiteId, ∑ k : Option SpeciesId,
      ∑ z : FunctionalCapacity.Split 3 2048 × SiteId,
        sourceIntensity (literalSourcePar seed) x (Sum.inr (i,(k,z)))) ≤ 16 := by
    simp_rw [divisionIntensity_sum (literal_source_valid seed hseed) x]
    have h := Finset.sum_le_sum (fun (i : SiteId) (_ : i ∈ Finset.univ) =>
      FunctionalCapacity.cf3_rd_sum_le (x i))
    norm_num [literalSourcePar] at h
    exact h
  calc
    _ ≤ ∑ i : SiteId, ∑ k : Option SpeciesId, ∑ z : FunctionalCapacity.Split 3 2048 × SiteId,
        sourceIntensity (literalSourcePar seed) x (Sum.inr (i,(k,z)))*C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (sourceIntensity_nonneg (literal_source_valid seed hseed) x _)
      dsimp [C]
      linarith [source_complete_division_fuel_upper seed x i z.2 k z.1]
    _ = (∑ i : SiteId, ∑ k : Option SpeciesId, ∑ z : FunctionalCapacity.Split 3 2048 × SiteId,
        sourceIntensity (literalSourcePar seed) x (Sum.inr (i,(k,z))))*C := by
      simp only [Finset.sum_mul]
    _ ≤ 16*C := mul_le_mul_of_nonneg_right hrate hC
    _ = sourceFuelWitness x*((16 : ℝ)*(Real.exp (2*stockS)-1)) := by dsimp [C]; ring
    _ ≤ sourceFuelWitness x*1 :=
      mul_le_mul_of_nonneg_left stock_division_occupation_allowance (fuel_occupation_positive _).le
    _ = sourceFuelWitness x := mul_one _

theorem stock_feed_coarse_division_exponent :
    4*stockS+60*(4*stockFeedK1+1)-stockEta*800000000 ≤ (-20 : ℝ) := by
  have h := stock_feed_rational_comparisons.2.2
  linarith

end
end P161Formal
