module

public import P161Formal.ServiceSourceParameters
public import proofs.CTMCHeredity20261019.MissionQuotient

/-! A missed500-credit spatial quota is detected by the actual service
witness. The scale matches the selected three-quarter tilt, including fuel. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators Classical
noncomputable section
set_option exponentiation.threshold 1024

def serviceBarrierScale : ℝ := (4/3 : ℝ)^500/serviceRho

theorem service_barrier_scale_nonnegative : 0 ≤ serviceBarrierScale := by
  unfold serviceBarrierScale serviceRho
  positivity

theorem service_barrier_scale_normalization :
    serviceBarrierScale*(serviceRho*serviceZ^500) = 1 := by
  have hr : serviceRho ≠ 0 := by norm_num [serviceRho]
  have he : (4/3 : ℝ)^500*serviceZ^500 = 1 := by
    rw [←mul_pow]
    norm_num [serviceZ]
  calc
    _ = ((4/3 : ℝ)^500*serviceZ^500)*(serviceRho/serviceRho) := by
      unfold serviceBarrierScale
      ring
    _ = 1 := by rw [he,div_self hr,mul_one]

theorem source_service_quota_detector (req : Finset SpeciesId)
    (x : CTMCHeredity20261019.SourceState (literalSourcePar 0))
    (hx : ¬CTMCHeredity20261019.sourceOkS 500 req x) :
    ∃ k ∈ (Finset.univ : Finset SiteId) ×ˢ req,
      1 ≤ serviceBarrierScale*sourceServicePotential k.1 k.2 x := by
  unfold CTMCHeredity20261019.sourceOkS at hx
  push Not at hx
  obtain ⟨i,j,hj,hq⟩ := hx
  refine ⟨(i,j),Finset.mem_product.mpr ⟨Finset.mem_univ i,hj⟩,?_⟩
  have hpow : serviceZ^500 ≤ serviceZ^((x i).q j) :=
    pow_le_pow_of_le_one (by norm_num [serviceZ]) (by norm_num [serviceZ]) (by omega)
  have hr : 0 ≤ serviceRho := by norm_num [serviceRho]
  have hw := (source_service_potential_bounds i j x).2.2
  calc
    1 = serviceBarrierScale*(serviceRho*serviceZ^500) :=
      service_barrier_scale_normalization.symm
    _ ≤ serviceBarrierScale*sourceServicePotential i j x :=
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hpow hr).trans hw) service_barrier_scale_nonnegative

theorem service_block_error_twelve :
    serviceBarrierScale*(12*Real.exp (-(serviceTheta*(1/10)))) ≤ 1/100000000 := by
  have he : serviceBarrierScale*(12*Real.exp (-(serviceTheta*(1/10)))) =
      (12/serviceRho)*(4/3 : ℝ)^500/Real.exp 165 := by
    rw [show serviceTheta*(1/10) = (165 : ℝ) by norm_num [serviceTheta]]
    rw [Real.exp_neg]
    unfold serviceBarrierScale
    ring
  rw [he]
  exact service_block_scalar_allowance

end
end P161Formal
