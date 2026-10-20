module

public import P161Formal.SourceServiceDrift
public import P161Formal.BranchingSourceGuards
public import proofs.FunctionalCapacity.Tick

/-! The generic block calculus applied to the owner's literal killed source
operator. The two constructors have the same tick; only proof fields differ. -/

@[expose] public section
namespace P161Formal
open FunctionalCapacity CTMCHeredity20261019
open scoped Classical
noncomputable section

theorem literal_source_clock_large (seed : ℝ) (hs : 0 ≤ seed) :
    serviceTheta ≤ cf3Rate (literalSourcePar seed) := by
  norm_num [cf3Rate,literalSourcePar,serviceTheta]
  linarith

theorem literal_source_clock_positive (seed : ℝ) (hs : 0 ≤ seed) :
    0 < cf3Rate (literalSourcePar seed) := by
  have h := literal_source_clock_large seed hs
  norm_num [serviceTheta] at h
  linarith

abbrev literalSourceKilled (seed : ℝ) (hs : 0 ≤ seed) (dead : BranchingSource → Prop) :=
  cf3SourceKilled (p := literalSourcePar seed) (literal_source_valid seed hs)
    (literal_source_clock_positive seed hs) le_rfl dead

theorem literal_source_killed_eq_generic (seed : ℝ) (hs : 0 ≤ seed)
    (dead : BranchingSource → Prop) :
    literalSourceKilled seed hs dead =
      killed (cf3_isGen (literal_source_valid seed hs))
        (literal_source_clock_positive seed hs) le_rfl dead := rfl

theorem source_killed_tick_super (seed : ℝ) (hs : 0 ≤ seed)
    (dead : BranchingSource → Prop) (V : BranchingSource → ℝ) (theta b : ℝ)
    (hV : ∀ y, 0 ≤ V y) (htheta : theta ≤ cf3Rate (literalSourcePar seed)) (hb : 0 ≤ b)
    (hgen : ∀ x, ¬dead x → cf3Gen (literalSourcePar seed) V x ≤ -theta*V x+b)
    (x : BranchingSource) :
    (literalSourceKilled seed hs dead).P V x ≤
      (1-theta/cf3Rate (literalSourcePar seed))*V x+b/cf3Rate (literalSourcePar seed) := by
  rw [literal_source_killed_eq_generic]
  exact tick_super (cf3_isGen (literal_source_valid seed hs))
    (literal_source_clock_positive seed hs) le_rfl dead hV htheta hb hgen x

theorem source_killed_tick_guard (seed : ℝ) (hs : 0 ≤ seed)
    (dead : BranchingSource → Prop) (Phi : BranchingSource → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hbarrier : ∀ x, dead x → 1 ≤ Phi x)
    (hgen : ∀ x, ¬dead x → cf3Gen (literalSourcePar seed) Phi x ≤ b)
    (x : BranchingSource) :
    (1-Phi x)-b/cf3Rate (literalSourcePar seed) ≤
      (literalSourceKilled seed hs dead).P (fun y => 1-Phi y) x := by
  rw [literal_source_killed_eq_generic]
  exact tick_sub (cf3_isGen (literal_source_valid seed hs))
    (literal_source_clock_positive seed hs) le_rfl dead hb hbarrier hgen x

theorem source_killed_service_tick (seed : ℝ) (hs : 0 ≤ seed) (req : Finset SpeciesId)
    (i : SiteId) (j : SpeciesId) (hj : j ∈ req) (x : BranchingSource) :
    (literalSourceKilled seed hs (sourceDead 16 req)).P (sourceServicePotential i j) x ≤
      (1-serviceTheta/cf3Rate (literalSourcePar seed))*sourceServicePotential i j x := by
  have h := source_killed_tick_super seed hs (sourceDead 16 req)
    (sourceServicePotential i j) serviceTheta 0
    (fun y => (source_service_potential_bounds i j y).1.le)
    (literal_source_clock_large seed hs) le_rfl
    (by
      intro y hy
      have hg := source_service_generator_bound seed y i j
        (branching_source_required_floor req y hy i j hj)
      simpa only [add_zero] using hg) x
  simpa only [zero_div,add_zero] using h

end
end P161Formal
