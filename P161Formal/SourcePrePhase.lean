module

public import P161Formal.SourcePostPhase
public import P161Formal.MissionArithmetic

/-! Literal seed6 acquisition followed by seed0 retention, including the
shared600-block service allocation. The resulting source value is later
identified with the owner's actual switched joint event. -/

@[expose] public section
namespace P161Formal
open FunctionalCapacity CTMCHeredity20261019
open scoped BigOperators Classical
noncomputable section

def literalBlockError : ℝ := (6/5)*(13/10000000)+1/100000000
def literalPostPhaseError : ℝ := 5184*Real.exp (-25)+300*literalBlockError

def literalSwitchedSourceValue (x : BranchingSource) : ℝ :=
  blocks (literalSourceKilled 6 (by norm_num) (sourceDead 16 branchingOldRequired))
    (cf3Rate (literalSourcePar 6)*(1/10)) (sourceOkS 500 branchingOldRequired)
    (sourceResetQ (p := literalSourcePar 6)) 300 literalPostSourceValue
    (sourceResetAll (p := literalSourcePar 6) x)

theorem source_pre_phase_lower (x : BranchingSource) :
    1-branchingOldPotential x-Real.exp (-15)*branchingSpeciesPotential 2 x-
      literalPostPhaseError-300*literalBlockError ≤ literalSwitchedSourceValue x := by
  let L : ℝ := cf3Rate (literalSourcePar 6)
  let K := literalSourceKilled 6 (by norm_num) (sourceDead 16 branchingOldRequired)
  let s : Finset (SiteId × SpeciesId) := Finset.univ ×ˢ branchingOldRequired
  have hL : 0 < L := literal_source_clock_positive 6 (by norm_num)
  have hmu : 0 ≤ L*(1/10) := mul_nonneg hL.le (by norm_num)
  have hND : (1/2 : ℝ) ≤ L := by norm_num [L,cf3Rate,literalSourcePar]
  have hS : serviceTheta ≤ L := literal_source_clock_large 6 (by norm_num)
  have hErr : 0 ≤ literalPostPhaseError := by
    unfold literalPostPhaseError literalBlockError
    positivity
  have hterminal (y : BranchingSource) :
      1-branchingOldPotential y-1*branchingSpeciesPotential 2 y-literalPostPhaseError ≤
        literalPostSourceValue y := by
    have hp := source_post_phase_lower y
    rw [branching_all_split] at hp
    unfold literalPostPhaseError literalBlockError
    linarith
  have h := blocks_lower K hmu (sourceOkS 500 branchingOldRequired)
    (sourceResetQ (p := literalSourcePar 6)) s
    (fun k => sourceServicePotential k.1 k.2)
    (Φ := branchingOldPotential) (V := branchingSpeciesPotential 2)
    (F := literalPostSourceValue) (BΦ := 640) (BV := 320)
    (bΦ := 8*(13/10000000)/L) (bV := 4*(13/10000000)/L)
    (θV := (1/2)/L) (θs := serviceTheta/L) (cV := 1)
    (A := serviceBarrierScale) (E0 := literalPostPhaseError)
    branching_old_nonnegative branching_old_max (branching_old_reset_q 6)
    (div_nonneg (by norm_num) hL.le) source_pre_guard_tick
    (fun y => branching_species_nonnegative y 2) (fun y => branching_species_max y 2)
    (fun y => branching_species_reset_q 6 y 2)
    (div_nonneg (by norm_num) hL.le) ((div_le_one hL).mpr hND)
    (div_nonneg (by norm_num) hL.le) source_candidate_tick
    (fun k _hk y => (source_service_potential_bounds k.1 k.2 y).1.le)
    (fun k _hk y => (source_service_potential_bounds k.1 k.2 y).2.1)
    (div_nonneg (by norm_num [serviceTheta]) hL.le) ((div_le_one hL).mpr hS)
    (fun k hk y => source_killed_service_tick 6 (by norm_num) branchingOldRequired k.1 k.2
      (Finset.mem_product.mp hk).2 y)
    service_barrier_scale_nonnegative (source_service_quota_detector branchingOldRequired)
    zero_le_one hErr literal_post_value_bdd hterminal
    300 (sourceResetAll (p := literalSourcePar 6) x)
  have hc : s.card = 8 := by simp [s,branchingOldRequired]
  have hV : (1/2 : ℝ)/L*(L*(1/10))*300 = 15 := by
    norm_num [L,cf3Rate,literalSourcePar]
  have hY : serviceTheta/L*(L*(1/10)) = 165 := by
    norm_num [L,cf3Rate,literalSourcePar,serviceTheta]
  have hb : (8*(13/10000000) : ℝ)/L*(L*(1/10))+
      4*(13/10000000)/L*(L*(1/10)) = (6/5)*(13/10000000) := by
    norm_num [L,cf3Rate,literalSourcePar]
  simp only [Nat.cast_ofNat,branching_old_reset_all,branching_species_reset_all,
    one_mul,hc,hV,hY,hb] at h
  have h12 : serviceBarrierScale*(12*Real.exp (-165)) ≤ 1/100000000 := by
    have ht := service_block_error_twelve
    rw [show serviceTheta*(1/10) = (165 : ℝ) by norm_num [serviceTheta]] at ht
    exact ht
  have hpos := mul_nonneg service_barrier_scale_nonnegative (Real.exp_nonneg (-165))
  have h8 : serviceBarrierScale*(8*Real.exp (-165)) ≤ 1/100000000 := by nlinarith
  change 1-branchingOldPotential x-Real.exp (-15)*branchingSpeciesPotential 2 x-
    literalPostPhaseError-300*((6/5 : ℝ)*(13/10000000)+
      serviceBarrierScale*(8*Real.exp (-165))) ≤ literalSwitchedSourceValue x at h
  unfold literalBlockError
  linarith

theorem source_switched_value_lower (x : BranchingSource)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a 0).val ∧ 512 ≤ ((x i).a 1).val) :
    1-((48/100000000 : ℝ)+320*Real.exp (-15)+5184*Real.exp (-25)+
      600*literalBlockError) ≤ literalSwitchedSourceValue x := by
  have h := source_pre_phase_lower x
  have hOld := branching_initial_old_bound x hx
  have hCand := mul_le_mul_of_nonneg_left (branching_species_max x 2) (Real.exp_nonneg (-15))
  unfold literalPostPhaseError at h
  linarith

theorem source_switched_value_numeric_lower (x : BranchingSource)
    (hx : ∀ i : SiteId, 512 ≤ ((x i).a 0).val ∧ 512 ≤ ((x i).a 1).val) :
    1-(9545923/9062500000 : ℝ) ≤ literalSwitchedSourceValue x := by
  have h := source_switched_value_lower x hx
  have h15 := mission_exp_fifteen
  have h25 := mission_exp_twenty_five
  norm_num [literalBlockError] at *
  linarith

end
end P161Formal
