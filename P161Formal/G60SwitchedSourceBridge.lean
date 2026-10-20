module

public import P161Formal.SourcePrePhase
public import proofs.CTMCHeredity20261019.V2.SeedSwitch

/-! Exact identification of the proved beta4m source value with the sealed
owner's switched value. Both phases retain their literal generator and all
600 grid checks; the actual global path-event identity is a later import. -/

@[expose] public section
namespace P161Formal
open CTMCHeredity20261019
noncomputable section

theorem literal_seed_on_parameter :
    literalSourcePar 6 = V2.SeedSwitch.canonicalSeedOnCF3 := rfl

theorem literal_seed_off_parameter : literalSourcePar 0 = canonicalSeedFreeCF3 := rfl

theorem literal_post_value_eq_owner (x : BranchingSource) :
    literalPostSourceValue x = V2.SeedSwitch.offSourceValue x := rfl

theorem literal_switched_value_eq_owner (x : BranchingSource) :
    literalSwitchedSourceValue x = V2.SeedSwitch.switchedSourceValue x := rfl

theorem owner_switched_value_numeric_lower (x : BranchingSource)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a 0).val ∧ 512 ≤ ((x i).a 1).val) :
    1-(9545923/9062500000 : ℝ) ≤ V2.SeedSwitch.switchedSourceValue x := by
  rw [←literal_switched_value_eq_owner]
  exact source_switched_value_numeric_lower x hx

end
end P161Formal
