module

public import proofs.CTMCHeredity20261019.ExponentialResidual
public import proofs.HybridCTMCInfrastructure.ClockStep
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Joint residual holding time and next state at a physical cut

The constructed `HybridCTMC.Kernel.clockStep` is the product of the actual
exponential holding law and the actual next-state law. Restricting to survival
past a real elapsed time, then subtracting that time from the holding coordinate,
preserves this entire joint law up to the scalar survival probability.

No independent residual clock or future-path law is assumed. This identifies
one conditional transition at a physical cut; the random clock-index slices
and the conditional infinite suffix remain separate obligations.
-/

namespace CTMCHeredity20261019

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Joint memorylessness for an arbitrary independent mark measure. This lemma
does not require the mark space to be finite. -/
theorem expMeasure_prod_residual_map {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] {Lam s : ℝ} (hLam : 0 < Lam) (hs : 0 ≤ s) :
    (((expMeasure Lam).prod ν).restrict {z : ℝ × S | s < z.1}).map
        (fun z : ℝ × S => (z.1 - s, z.2)) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) • (expMeasure Lam).prod ν := by
  let := isProbabilityMeasure_expMeasure hLam
  have hset : {z : ℝ × S | s < z.1} = Ioi s ×ˢ (univ : Set S) := by
    ext z
    simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  calc
    (((expMeasure Lam).restrict (Ioi s)).prod ν).map
        (fun z : ℝ × S => (z.1 - s, z.2)) =
        (((expMeasure Lam).restrict (Ioi s)).map (fun h : ℝ => h - s)).prod ν := by
      simpa only [Measure.map_id, Prod.map_def, id_eq] using
        (Measure.map_prod_map ((expMeasure Lam).restrict (Ioi s)) ν
          (f := fun h : ℝ => h - s) (g := id) (by fun_prop) measurable_id).symm
    _ = ENNReal.ofReal (Real.exp (-(Lam * s))) • (expMeasure Lam).prod ν := by
      rw [expMeasure_residual_map hLam hs, Measure.prod_smul_left]

variable {S : Type*} [Fintype S] [MeasurableSpace S]

/-- The actual clock-step measure, including its sampled next state, has the
same residual law multiplied by survival past s. -/
theorem clockStep_residual_map (K : HybridCTMC.Kernel S) {Lam s : ℝ}
    (hLam : 0 < Lam) (hs : 0 ≤ s) (x : S) :
    ((K.clockStep Lam x).restrict {z : ℝ × S | s < z.1}).map
        (fun z : ℝ × S => (z.1 - s, z.2)) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) • K.clockStep Lam x := by
  simpa only [HybridCTMC.Kernel.clockStep] using
    expMeasure_prod_residual_map (K.pmf x).toMeasure hLam hs

/-- Nonnegative rewards of the joint residual hold and next state factor by
the exact survival probability under the actual clock-step measure. -/
theorem clockStep_residual_lintegral (K : HybridCTMC.Kernel S) {Lam s : ℝ}
    (hLam : 0 < Lam) (hs : 0 ≤ s) (x : S)
    (F : ℝ × S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in {z : ℝ × S | s < z.1}, F (z.1 - s, z.2) ∂K.clockStep Lam x) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) * ∫⁻ z, F z ∂K.clockStep Lam x := by
  rw [← lintegral_map hF (by fun_prop), clockStep_residual_map K hLam hs x,
    lintegral_smul_measure, smul_eq_mul]

/-- Indicator form for insertion in a finite-prefix disintegration. -/
theorem clockStep_residual_indicator (K : HybridCTMC.Kernel S) {Lam s : ℝ}
    (hLam : 0 < Lam) (hs : 0 ≤ s) (x : S)
    (F : ℝ × S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, if s < z.1 then F (z.1 - s, z.2) else 0 ∂K.clockStep Lam x) =
      ENNReal.ofReal (Real.exp (-(Lam * s))) * ∫⁻ z, F z ∂K.clockStep Lam x := by
  have hm : MeasurableSet {z : ℝ × S | s < z.1} :=
    measurableSet_lt measurable_const measurable_fst
  have he : (fun z : ℝ × S => if s < z.1 then F (z.1 - s, z.2) else 0) =
      {z : ℝ × S | s < z.1}.indicator (fun z => F (z.1 - s, z.2)) := rfl
  rw [he, lintegral_indicator hm]
  exact clockStep_residual_lintegral K hLam hs x F hF

/-- Physical-time notation: r is the last arrival, T is the deterministic cut,
and the next arrival is r plus the newly sampled hold. This does not yet sum
over the random last-arrival index or assert a conditional future-path law. -/
theorem clockStep_residual_at_cut (K : HybridCTMC.Kernel S) {Lam r T : ℝ}
    (hLam : 0 < Lam) (hrT : r ≤ T) (x : S)
    (F : ℝ × S → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, if T < r + z.1 then F (r + z.1 - T, z.2) else 0
      ∂K.clockStep Lam x) =
      ENNReal.ofReal (Real.exp (-(Lam * (T - r)))) *
        ∫⁻ z, F z ∂K.clockStep Lam x := by
  have he : (fun z : ℝ × S =>
      if T < r + z.1 then F (r + z.1 - T, z.2) else 0) =
      (fun z : ℝ × S => if T - r < z.1 then F (z.1 - (T - r), z.2) else 0) := by
    funext z
    have hp : T < r + z.1 ↔ T - r < z.1 := by constructor <;> intro h <;> linarith
    have ha : r + z.1 - T = z.1 - (T - r) := by ring
    simp only [hp, ha]
  rw [he]
  exact clockStep_residual_indicator K hLam (sub_nonneg.mpr hrT) x F hF

end
end CTMCHeredity20261019
