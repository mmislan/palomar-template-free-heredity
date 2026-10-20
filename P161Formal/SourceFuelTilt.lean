module

public import P161Formal.FuelAccounting
public import P161Formal.StockArithmetic
public import P161Formal.SourceContractBridge

/-! The occupation witness for one global fuel inventory. Its exact update
ratios retain the current fuel bit and support the joint feed/fuel tilt. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019
open scoped BigOperators Classical
noncomputable section

def fuelOccupationWitness (F : SiteId → Bool) : ℝ :=
  Real.exp (-stockS*(totalFuel F : ℝ))

theorem fuel_occupation_positive (F : SiteId → Bool) : 0 < fuelOccupationWitness F :=
  Real.exp_pos _

theorem fuel_occupation_upper (F : SiteId → Bool) : fuelOccupationWitness F ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hs := stock_tilt_parameters.1
  have hF : (0 : ℝ) ≤ totalFuel F := Nat.cast_nonneg _
  nlinarith

theorem fuel_occupation_lower (F : SiteId → Bool) :
    Real.exp (-4*stockS) ≤ fuelOccupationWitness F := by
  apply Real.exp_le_exp.mpr
  have hs := stock_tilt_parameters.1
  have hF : (totalFuel F : ℝ) ≤ 4 := by exact_mod_cast total_fuel_at_most_four F
  nlinarith

theorem fuel_occupation_update (F : SiteId → Bool) (i : SiteId) (b : Bool) :
    fuelOccupationWitness (Function.update F i b) = fuelOccupationWitness F*
      Real.exp (stockS*((bitFuel (F i) : ℝ)-(bitFuel b : ℝ))) := by
  have hb := fuel_update_balance F i b
  have hcast : (totalFuel (Function.update F i b) : ℝ)+(bitFuel (F i) : ℝ) =
      (totalFuel F : ℝ)+(bitFuel b : ℝ) := by exact_mod_cast hb
  have he : -stockS*(totalFuel (Function.update F i b) : ℝ) =
      -stockS*(totalFuel F : ℝ)+stockS*((bitFuel (F i) : ℝ)-(bitFuel b : ℝ)) := by
    have hm := congrArg (fun z : ℝ => stockS*z) hcast
    nlinarith only [hm]
  unfold fuelOccupationWitness
  rw [he,Real.exp_add]

theorem fuel_occupation_balance (F G : SiteId → Bool) (debit : ℕ)
    (hbalance : totalFuel G+debit = totalFuel F) :
    fuelOccupationWitness G = fuelOccupationWitness F*Real.exp (stockS*(debit : ℝ)) := by
  have hcast : (totalFuel G : ℝ)+(debit : ℝ) = (totalFuel F : ℝ) := by exact_mod_cast hbalance
  have he : -stockS*(totalFuel G : ℝ) = -stockS*(totalFuel F : ℝ)+stockS*(debit : ℝ) := by
    have hm := congrArg (fun z : ℝ => stockS*z) hcast
    nlinarith only [hm]
  unfold fuelOccupationWitness
  rw [he,Real.exp_add]

theorem fuel_occupation_drain (F : SiteId → Bool) (i : SiteId) :
    fuelOccupationWitness (Function.update F i false)-fuelOccupationWitness F =
      if F i then fuelOccupationWitness F*(Real.exp stockS-1) else 0 := by
  rw [fuel_occupation_update]
  cases hf : F i <;> norm_num [bitFuel,hf]
  ring

theorem fuel_occupation_feed_weighted (F : SiteId → Bool) (i : SiteId) :
    (if F i then (0 : ℝ) else 4000000)*
      (Real.exp stockEta*fuelOccupationWitness (Function.update F i true)-fuelOccupationWitness F) =
    (if F i then (0 : ℝ) else 4000000)*fuelOccupationWitness F*
      (Real.exp (stockEta-stockS)-1) := by
  cases hf : F i
  · rw [fuel_occupation_update]
    norm_num only [hf,Bool.false_eq_true,ite_false,bitFuel,ite_true,Nat.cast_zero,Nat.cast_one,
      zero_sub,mul_neg,mul_one]
    have he : Real.exp stockEta*Real.exp (-stockS) = Real.exp (stockEta-stockS) := by
      rw [←Real.exp_add,sub_eq_add_neg]
    calc
      _ = 4000000*fuelOccupationWitness F*(Real.exp stockEta*Real.exp (-stockS)-1) := by ring
      _ = _ := by rw [he]
  · simp only [ite_true,zero_mul]

def sourceFuelCount {seed : ℝ} (x : SourceState (literalSourcePar seed)) : ℕ :=
  totalFuel (fun i => (x i).R)

def sourceFuelWitness {seed : ℝ} (x : SourceState (literalSourcePar seed)) : ℝ :=
  fuelOccupationWitness (fun i => (x i).R)

def coreFuelWitness (seed : ℝ) (x : CoreState (literalSourcePar seed)) : ℝ :=
  fuelOccupationWitness (fun i => (x i).2)

theorem core_fuel_witness_project (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    coreFuelWitness seed (coreProject x) = sourceFuelWitness x := rfl

theorem source_fuel_witness_bounds (seed : ℝ) (x : SourceState (literalSourcePar seed)) :
    Real.exp (-4*stockS) ≤ sourceFuelWitness x ∧ sourceFuelWitness x ≤ 1 :=
  ⟨fuel_occupation_lower _,fuel_occupation_upper _⟩

end
end P161Formal
