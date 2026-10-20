module

public import P161Formal.SourceContractBridge
public import P161Formal.ServiceArithmetic

/-! The bounded ordinary-credit service witness and the literal beta4m
uncredited fuel load. These estimates use actual counts/fuel/natural q;
source drift and stopped block probability are subsequent obligations. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators
noncomputable section

def serviceFuelWeight (fuel : Bool) : ℝ := if fuel then serviceRho else 1

def sourceServicePotential (i : SiteId) (j : SpeciesId)
    (x : CTMCHeredity20261019.SourceState (literalSourcePar 0)) : ℝ :=
  serviceFuelWeight (x i).R*serviceZ^((x i).q j)

theorem service_fuel_weight_bounds (fuel : Bool) :
    0 < serviceFuelWeight fuel ∧ serviceFuelWeight fuel ≤ 1 ∧
      serviceRho ≤ serviceFuelWeight fuel := by
  cases fuel <;> norm_num [serviceFuelWeight,serviceRho]

theorem service_power_bounds (q : ℕ) : 0 < serviceZ^q ∧ serviceZ^q ≤ 1 := by
  constructor
  · exact pow_pos (by norm_num [serviceZ]) q
  · exact pow_le_one₀ (by norm_num [serviceZ]) (by norm_num [serviceZ])

theorem service_power_succ_le (q : ℕ) : serviceZ^(q+1) ≤ serviceZ^q := by
  rw [pow_succ]
  have hp := (service_power_bounds q).1
  norm_num [serviceZ] at *

theorem source_service_potential_bounds (i : SiteId) (j : SpeciesId)
    (x : CTMCHeredity20261019.SourceState (literalSourcePar 0)) :
    0 < sourceServicePotential i j x ∧ sourceServicePotential i j x ≤ 1 ∧
      serviceRho*serviceZ^((x i).q j) ≤ sourceServicePotential i j x := by
  obtain ⟨hv0,hv1,hvr⟩ := service_fuel_weight_bounds (x i).R
  obtain ⟨hp0,hp1⟩ := service_power_bounds ((x i).q j)
  unfold sourceServicePotential
  refine ⟨mul_pos hv0 hp0,?_,?_⟩
  · simpa only [mul_one] using mul_le_mul hv1 hp1 hp0.le (show (0 : ℝ) ≤ 1 by norm_num)
  · exact mul_le_mul_of_nonneg_right hvr hp0.le

def serviceActiveConsumption (a : Fin 2049) : ℝ :=
  800*(a.val : ℝ)*(1-(a.val : ℝ)/2048)+400*a.val

theorem service_active_consumption_bound (a : Fin 2049) :
    0 ≤ serviceActiveConsumption a ∧ serviceActiveConsumption a ≤ 921600 := by
  have ha0 : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
  have ha1 : (a.val : ℝ) ≤ 2048 := by
    have hn : a.val ≤ 2048 := by have h := a.isLt; omega
    exact_mod_cast hn
  unfold serviceActiveConsumption
  constructor
  · have hroom : 0 ≤ 1-(a.val : ℝ)/2048 := by linarith
    have hfirst : 0 ≤ 800*(a.val : ℝ)*(1-(a.val : ℝ)/2048) := by positivity
    nlinarith
  · nlinarith [sq_nonneg ((a.val : ℝ)-1536)]

def serviceUncreditedChemicalLoad (s : FunctionalCapacity.Site 3 2048) (j : SpeciesId) : ℝ :=
  4000000+(∑ k : SpeciesId, serviceActiveConsumption (s.a k))+
    ∑ k ∈ Finset.univ.erase j, 4000000*((s.a k).val : ℝ)/2048

theorem service_uncredited_chemical_load_bound (s : FunctionalCapacity.Site 3 2048)
    (j : SpeciesId) : serviceUncreditedChemicalLoad s j ≤ serviceLoad-8 := by
  have hactive := Finset.sum_le_sum (fun (k : SpeciesId) (_ : k ∈ Finset.univ) =>
    (service_active_consumption_bound (s.a k)).2)
  norm_num at hactive
  have hother := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun k _ => show 4000000*((s.a k).val : ℝ)/2048 ≤ 4000000 by
      have hn : (s.a k).val ≤ 2048 := by have h := (s.a k).isLt; omega
      have hr : ((s.a k).val : ℝ) ≤ 2048 := by exact_mod_cast hn
      linarith)
  have hcard : (Finset.univ.erase j).card = 2 := by simp
  norm_num only [Finset.sum_const,hcard,nsmul_eq_mul,Nat.cast_ofNat] at hother
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)] at hother
  unfold serviceUncreditedChemicalLoad
  norm_num [serviceLoad]
  linarith

end
end P161Formal
