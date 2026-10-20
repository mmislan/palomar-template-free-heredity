module

public import P161Formal.Contract
public import P161Formal.Conservation
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Pointwise fuel conservation for the specified physical channel projections and
complete complementary division marks. Consumption includes births, active
deaths, ordinary jobs, discharge and triggered division. Basal division's
parental fuel is partitioned; victim fuel is separately discarded.
The final telescoping lemma charges one global history without episode resets.
The stochastic path adapter and resource-tail estimates remain separate.
-/

@[expose] public section
namespace P161Formal
noncomputable section
open scoped BigOperators

def bitFuel (b : Bool) : ℕ := if b then 1 else 0
def totalFuel (F : SiteId → Bool) : ℕ := ∑ i, bitFuel (F i)

theorem total_fuel_at_most_four (F : SiteId → Bool) : totalFuel F ≤ 4 := by
  have h : ∀ i, bitFuel (F i) ≤ 1 := by
    intro i
    cases F i <;> norm_num [bitFuel]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset SiteId)) => h i)
  norm_num at hs
  exact hs

theorem fuel_update_balance (F : SiteId → Bool) (i : SiteId) (b : Bool) :
    totalFuel (Function.update F i b) + bitFuel (F i) = totalFuel F + bitFuel b := by
  have hfun : (fun j => bitFuel (Function.update F i b j)) =
      Function.update (fun j => bitFuel (F j)) i (bitFuel b) := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  unfold totalFuel
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add (Finset.univ : Finset SiteId)
    (fun j => bitFuel (F j)) (Finset.mem_univ i)
  omega

def chemicalFuelAfter (x : Population) : ChemicalChannel → (SiteId → Bool)
  | .seed _ _ => x.fuel
  | .passive _ _ => x.fuel
  | .birth i _ => Function.update x.fuel i false
  | .activeDeath i _ => Function.update x.fuel i false
  | .ordinary i _ => Function.update x.fuel i false
  | .recharge i => Function.update x.fuel i true
  | .discharge i => Function.update x.fuel i false

def chemicalFeed : ChemicalChannel → ℕ
  | .recharge _ => 1
  | _ => 0

def chemicalConsumed : ChemicalChannel → ℕ
  | .birth _ _ | .activeDeath _ _ | .ordinary _ _ | .discharge _ => 1
  | _ => 0

theorem positive_chemical_fuel_balance (t : ℝ) (x : Population) (k : ChemicalChannel)
    (hpositive : 0 < chemicalRate t x k) :
    totalFuel (chemicalFuelAfter x k) + chemicalConsumed k =
      totalFuel x.fuel + chemicalFeed k := by
  cases k with
  | seed i j => rfl
  | passive i j => rfl
  | birth i j =>
      have hf : x.fuel i = true := by
        cases he : x.fuel i <;> simp [chemicalRate, fueled, he] at hpositive ⊢
      have h := fuel_update_balance x.fuel i false
      simpa [chemicalFuelAfter, chemicalConsumed, chemicalFeed, bitFuel, hf] using h
  | activeDeath i j =>
      have hf : x.fuel i = true := by
        cases he : x.fuel i <;> simp [chemicalRate, fueled, he] at hpositive ⊢
      have h := fuel_update_balance x.fuel i false
      simpa [chemicalFuelAfter, chemicalConsumed, chemicalFeed, bitFuel, hf] using h
  | ordinary i j =>
      have hf : x.fuel i = true := by
        cases he : x.fuel i <;> simp [chemicalRate, fueled, he] at hpositive ⊢
      have h := fuel_update_balance x.fuel i false
      simpa [chemicalFuelAfter, chemicalConsumed, chemicalFeed, bitFuel, hf] using h
  | recharge i =>
      have hf : x.fuel i = false := by
        cases he : x.fuel i <;> simp [chemicalRate, fueled, he] at hpositive ⊢
      have h := fuel_update_balance x.fuel i true
      simpa [chemicalFuelAfter, chemicalConsumed, chemicalFeed, bitFuel, hf] using h
  | discharge i =>
      have hf : x.fuel i = true := by
        cases he : x.fuel i <;> simp [chemicalRate, fueled, he] at hpositive ⊢
      have h := fuel_update_balance x.fuel i false
      simpa [chemicalFuelAfter, chemicalConsumed, chemicalFeed, bitFuel, hf] using h

def triggeredFuelDebit {x : Population} (m : DivisionMark x) : ℕ :=
  if m.trigger.isSome then 1 else 0

theorem daughter_fuel_balance (x : Population) (m : DivisionMark x)
    (hpositive : 0 < divisionRate x m.parent m.trigger) :
    bitFuel (divisionFuel x m).1 + bitFuel (divisionFuel x m).2 +
      triggeredFuelDebit m = bitFuel (x.fuel m.parent) := by
  cases ht : m.trigger with
  | none =>
      cases hf : x.fuel m.parent <;> cases hb : m.fuelBit <;>
        norm_num [divisionFuel, bitFuel, triggeredFuelDebit, ht, hf, hb]
  | some j =>
      have hf : x.fuel m.parent = true := by
        cases he : x.fuel m.parent <;> simp [divisionRate, fueled, ht, he] at hpositive ⊢
      simp [divisionFuel, bitFuel, triggeredFuelDebit, ht, hf]

theorem positive_division_fuel_balance (x : Population) (m : DivisionMark x)
    (hpositive : 0 < divisionRate x m.parent m.trigger) :
    totalFuel (afterDivision x m).fuel + triggeredFuelDebit m +
      bitFuel (x.fuel m.victim) = totalFuel x.fuel := by
  have hp := fuel_update_balance x.fuel m.parent (divisionFuel x m).1
  have hv := fuel_update_balance
    (Function.update x.fuel m.parent (divisionFuel x m).1) m.victim (divisionFuel x m).2
  simp only [Function.update_of_ne m.distinct] at hv
  have hd := daughter_fuel_balance x m hpositive
  change totalFuel (Function.update
    (Function.update x.fuel m.parent (divisionFuel x m).1)
    m.victim (divisionFuel x m).2) + _ + _ = _
  omega

/-- Pointwise prefix conservation with all consuming channels and victim losses
charged once across the entire event history. -/
theorem fuel_history_balance (F A C W : ℕ → ℕ)
    (hstep : ∀ k, F (k + 1) + C k + W k = F k + A k) (n : ℕ) :
    F 0 + ∑ k ∈ Finset.range n, A k = F n +
      (∑ k ∈ Finset.range n, C k) + ∑ k ∈ Finset.range n, W k := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      have hs := hstep n
      omega

end
end P161Formal
