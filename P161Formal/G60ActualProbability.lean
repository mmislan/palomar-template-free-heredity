module

public import P161Formal.G60SwitchedSourceBridge
public import proofs.CTMCHeredity20261019.V4.TwoPhaseEvent

/-! Quantitative G60 on the actual global two-envelope switched source law:
all-time applicable floors, all600 service windows and the post30 spatial
division quotas. Renewal and shared finite-stock transfer remain separate. -/

@[expose] public section
namespace P161Formal
open MeasureTheory CTMCHeredity20261019
open V4.TwoPhaseEvent
noncomputable section

theorem g60_actual_success_probability (x : V2.SeedSwitch.Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    ENNReal.ofReal (1-(9545923/9062500000 : ℝ)) ≤
      pathLaw x {w | continuousEvent w} := by
  rw [pathLaw_continuous_event_probability]
  exact ENNReal.ofReal_le_ofReal (owner_switched_value_numeric_lower x hx)

theorem g60_actual_failure_probability (x : V2.SeedSwitch.Raw)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a (0 : SpeciesId)).val ∧
      512 ≤ ((x i).a (1 : SpeciesId)).val) :
    pathLaw x {w | ¬continuousEvent w} ≤ ENNReal.ofReal (9545923/9062500000 : ℝ) := by
  have h := owner_switched_value_numeric_lower x hx
  have hp : 0 ≤ V2.SeedSwitch.switchedSourceValue x := by linarith
  change pathLaw x ({w | continuousEvent w}ᶜ) ≤ _
  rw [prob_compl_eq_one_sub₀ (pathLaw_nullMeasurableSet_continuousEvent x),
    pathLaw_continuous_event_probability,←ENNReal.ofReal_one,←ENNReal.ofReal_sub 1 hp]
  apply ENNReal.ofReal_le_ofReal
  linarith

end
end P161Formal
