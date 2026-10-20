module

public import P161Formal.SourceStockCounts
public import proofs.CTMCHeredity20261019.CF3RawPathLift
public import proofs.CTMCHeredity20261019.V2.RawOperated

/-! Positive source intensities for every actually sampled nonidle mark.
These are support facts for the constructed kernel/law, not assumptions about
successful paths. The sentinel at0 is excluded by the n+1 index. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2
open scoped BigOperators ENNReal Classical
noncomputable section

local instance stockSupportRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stockSupportRawMeasurableSingleton (p : FunctionalCapacity.Par) : MeasurableSingletonClass (SourceState p) :=
  ⟨fun _ => trivial⟩
local instance stockSupportMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stockSupportMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance stockSupportOptionMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance stockSupportOptionMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩

theorem source_kernel_positive_mark {p : FunctionalCapacity.Par} (hp : p.Valid)
    (z y : CF3MarkedKernel.State p)
    (hy : 0 < (CF3MarkedKernel.kernel hp).weight z y) :
    ∀ m : Mark p, y.2 = some m → 0 < sourceIntensity p (coreRepresent z.1) m := by
  have hu := MarkedKernel.positive_weight_update (coreChannels hp)
    (CF3MarkedKernel.rate_positive hp) (CF3MarkedKernel.core_channel_bound hp) z y hy
  rw [CF3MarkedKernel.kernel] at hy
  simp only [MarkedKernel.kernel,ite_eq_left hu] at hy
  intro m hm
  rw [hm] at hy
  change 0 < sourceIntensity p (coreRepresent z.1) m/FunctionalCapacity.cf3Rate p at hy
  exact (div_pos_iff_of_pos_right (CF3MarkedKernel.rate_positive hp)).mp hy

theorem ae_raw_source_positive {p : FunctionalCapacity.Par} (hp : p.Valid)
    (x : SourceState p) (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ∀ n : ℕ, ∀ m : Mark p, (w (n+1)).2.2 = some m →
        0 < sourceIntensity p (rawAt p x w n) m := by
  have hpos := (CF3MarkedKernel.kernel hp).ae_event_relation
    (CF3MarkedKernel.rate_positive hp) (coreProject x,old)
    (fun a b => ∀ m : Mark p, b.2 = some m → 0 < sourceIntensity p (coreRepresent a.1) m)
    (fun a b h => source_kernel_positive_mark hp a b h)
  filter_upwards [hpos,ae_rawAt_project hp x old] with w hw hc
  intro n m hm
  rw [CF3MarkedKernel.sourceIntensity_lump p (rawAt p x w n) m,hc n]
  exact hw n m hm

def sourceSupportedSegment (p : FunctionalCapacity.Par) (s : RawOperated.Segment p) : Prop :=
  ∀ n : ℕ, ∀ m : Mark p, (s.1 (n+1)).2.2 = some m →
    0 < sourceIntensity p (s.2 n).2 m

theorem measurableSet_sourceSupportedSegment (p : FunctionalCapacity.Par) :
    MeasurableSet {s | sourceSupportedSegment p s} := by
  have he : {s | sourceSupportedSegment p s} = ⋂ n : ℕ, ⋂ m : Mark p,
      {s : RawOperated.Segment p | (s.1 (n+1)).2.2 = some m →
        0 < sourceIntensity p (s.2 n).2 m} := by
    ext s
    simp only [sourceSupportedSegment,Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro m
  have hm : Measurable (fun s : RawOperated.Segment p => (s.1 (n+1)).2.2) :=
    (measurable_of_countable (fun z : CF3MarkedKernel.State p => z.2)).comp
      (measurable_snd.comp ((measurable_pi_apply (n+1)).comp measurable_fst))
  have hx : Measurable (fun s : RawOperated.Segment p => sourceIntensity p (s.2 n).2 m) :=
    (measurable_of_countable (fun x : SourceState p => sourceIntensity p x m)).comp
      (measurable_snd.comp ((measurable_pi_apply n).comp measurable_snd))
  have h : MeasurableSet ({s : RawOperated.Segment p | (s.1 (n+1)).2.2 = some m}ᶜ ∪
      {s | (0 : ℝ) < sourceIntensity p (s.2 n).2 m}) :=
    (measurableSet_eq_fun hm measurable_const).compl.union
      (measurableSet_lt measurable_const hx)
  convert h using 1
  ext s
  simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_ofPred_eq,imp_iff_not_or]

theorem source_segmentKernel_ae_supported {p : FunctionalCapacity.Par} (hp : p.Valid)
    (x : SourceState p) :
    ∀ᵐ s ∂RawOperated.segmentKernel hp x, sourceSupportedSegment p s := by
  change ∀ᵐ s ∂(CF3MarkedKernel.eventLaw hp (coreProject x) none).map (RawOperated.rawPair p x), _
  apply (ae_map_iff (RawOperated.measurable_rawPair p x).aemeasurable
    (measurableSet_sourceSupportedSegment p)).mpr
  filter_upwards [ae_raw_source_positive hp x none] with w hw
  exact hw

theorem source_rawLaw_ae_supported {p : FunctionalCapacity.Par} (hp : p.Valid)
    (T : ℝ) (n : ℕ) (x : SourceState p) :
    ∀ᵐ h ∂RawOperated.rawLaw hp T n x, RawOperated.allSegments (sourceSupportedSegment p) h :=
  RawOperated.rawLaw_ae_allSegments hp T (sourceSupportedSegment p)
    (measurableSet_sourceSupportedSegment p) (source_segmentKernel_ae_supported hp) n x

end
end P161Formal
