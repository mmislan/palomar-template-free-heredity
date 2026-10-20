module

public import proofs.CTMCHeredity20261019.V2.RawStoppedFuture

@[expose] public section

/-!
# V2: first current-population Ready512 and actual-division event stops

Ready512 requires every species count in every currently occupied source site
to be at least 512. Its index-zero hit is included. The complete marked-prefix
slices are measurable and disjoint by construction, and actual sampled core
coherence identifies them with the literal raw source first-hit predicate.

The stopped future keeps natural q/nd ledgers through `rawLiftLaw`. No caller
adaptedness, eventual hitting, recovery probability bound, physical-time
first-hit correspondence, stock estimate, or mission success is assumed.
Definitions are aligned with the owner's read-only `Contract.ready512` and
strict post-start division convention; its moving closure is not imported.
-/

namespace CTMCHeredity20261019.V2.RecoveryStops

noncomputable section
open FunctionalCapacity MeasureTheory ProbabilityTheory Preorder Set HybridCTMC.Kernel
open CF3Marked CF3RawPathLift RawStoppedFuture
open scoped BigOperators ENNReal Classical

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance (p : Par) : MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

/-- The first occurrence of an explicit event-index/state predicate. Every
test is on the complete available prefix, rather than a future event. -/
def firstSlices (p : Par) (P : ℕ → CF3MarkedKernel.State p → Prop) (n : ℕ) : Set (Prefix p n) :=
  {u | P n (lastMarked p n u) ∧
    ∀ i : Fin n, ¬ P i.val (u ⟨i.val, Finset.mem_Iic.mpr i.isLt.le⟩).2}

theorem firstSlices_pullback (p : Par) (P : ℕ → CF3MarkedKernel.State p → Prop)
    (w : MarkedPath p) (n : ℕ) :
    frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ firstSlices p P n ↔
      P n (w n).2 ∧ ∀ m : ℕ, m < n → ¬ P m (w m).2 := by
  constructor
  · rintro ⟨hn, hprev⟩
    refine ⟨hn, ?_⟩
    intro m hm
    exact hprev ⟨m, hm⟩
  · rintro ⟨hn, hprev⟩
    refine ⟨hn, ?_⟩
    intro i
    exact hprev i.val i.isLt

/-- All prefix tests are measurable because each tested marked state is on
the existing finite discrete carrier. No adaptedness premise is supplied. -/
theorem measurableSet_firstSlices (p : Par) (P : ℕ → CF3MarkedKernel.State p → Prop) (n : ℕ) :
    MeasurableSet (firstSlices p P n) := by
  have hc : MeasurableSet {u : Prefix p n | P n (lastMarked p n u)} :=
    (Set.to_countable {z : CF3MarkedKernel.State p | P n z}).measurableSet.preimage
      (measurable_lastMarked p n)
  have hp (i : Fin n) : MeasurableSet
      {u : Prefix p n | ¬ P i.val (u ⟨i.val, Finset.mem_Iic.mpr i.isLt.le⟩).2} :=
    ((Set.to_countable {z : CF3MarkedKernel.State p | P i.val z}).measurableSet.preimage
      (measurable_pi_apply (X := fun _ : Finset.Iic n => ℝ × CF3MarkedKernel.State p)
        ⟨i.val, Finset.mem_Iic.mpr i.isLt.le⟩).snd).compl
  convert hc.inter (MeasurableSet.iInter hp) using 1
  ext u
  simp only [firstSlices, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]

theorem firstSlices_disjoint (p : Par) (P : ℕ → CF3MarkedKernel.State p → Prop) :
    Pairwise (fun n m => Disjoint (eventIndexStopSlice (firstSlices p P) n)
      (eventIndexStopSlice (firstSlices p P) m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro w hn hm
  have hn' := (firstSlices_pullback p P w n).mp hn
  have hm' := (firstSlices_pullback p P w m).mp hm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hm'.2 n hlt hn'.1
  · exact hn'.2 m hgt hm'.1

/-- Current-population Ready512, matching the owner's all-site/all-species
count predicate. Fuel and the external natural ledgers are not restricted. -/
def coreReady512 {p : Par} (z : CoreState p) : Prop :=
  ∀ i : Fin p.M, ∀ j : Fin p.c, 512 ≤ ((z i).1 j).val

def rawReady512 {p : Par} (x : SourceState p) : Prop :=
  ∀ i : Fin p.M, ∀ j : Fin p.c, 512 ≤ ((x i).a j).val

theorem ready512_coreProject {p : Par} (x : SourceState p) :
    coreReady512 (coreProject x) ↔ rawReady512 x := Iff.rfl

def firstReady512Slices (p : Par) : ∀ n : ℕ, Set (Prefix p n) :=
  firstSlices p (fun _ z => coreReady512 z.1)

def firstReady512Raw (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) : Prop :=
  rawReady512 (rawAt p x w n) ∧ ∀ m : ℕ, m < n → ¬ rawReady512 (rawAt p x w m)

theorem measurableSet_firstReady512Slices (p : Par) (n : ℕ) :
    MeasurableSet (firstReady512Slices p n) :=
  measurableSet_firstSlices p (fun _ z => coreReady512 z.1) n

theorem firstReady512Slices_disjoint (p : Par) :
    Pairwise (fun n m => Disjoint (eventIndexStopSlice (firstReady512Slices p) n)
      (eventIndexStopSlice (firstReady512Slices p) m)) :=
  firstSlices_disjoint p (fun _ z => coreReady512 z.1)

/-- The observed first-hit slices equal the literal raw-state first hits on
one full-measure set supplied by actual marked/raw core coherence. -/
theorem ae_firstReady512_raw {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old, ∀ n : ℕ,
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ firstReady512Slices p n ↔
        firstReady512Raw p x w n) := by
  filter_upwards [ae_rawAt_project hp x old] with w hw
  have he (m : ℕ) : coreReady512 (w m).2.1 ↔ rawReady512 (rawAt p x w m) := by
    rw [← hw m]
    exact ready512_coreProject _
  intro n
  rw [show firstReady512Slices p n = firstSlices p (fun _ z => coreReady512 z.1) n from rfl,
    firstSlices_pullback]
  constructor
  · rintro ⟨hn, hprev⟩
    refine ⟨(he n).mp hn, ?_⟩
    intro m hm hr
    exact hprev m hm ((he m).mpr hr)
  · rintro ⟨hn, hprev⟩
    refine ⟨(he n).mpr hn, ?_⟩
    intro m hm hc
    exact hprev m hm ((he m).mp hc)

/-- An already Ready initial source state is an immediate index-zero hit. -/
theorem firstReady512Raw_zero (p : Par) (x : SourceState p) (w : MarkedPath p) :
    firstReady512Raw p x w 0 ↔ rawReady512 x := by
  simp [firstReady512Raw]

theorem ae_firstReady512_zero {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      (frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) 0 w ∈ firstReady512Slices p 0 ↔
        rawReady512 x) := by
  filter_upwards [ae_firstReady512_raw hp x old] with w hw
  exact (hw 0).trans (firstReady512Raw_zero p x w)

theorem ae_firstReady512_hit {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      (w ∈ eventIndexHitEvent (firstReady512Slices p) ↔ ∃ n : ℕ, firstReady512Raw p x w n) := by
  filter_upwards [ae_firstReady512_raw hp x old] with w hw
  simp only [eventIndexHitEvent, Set.mem_iUnion, eventIndexStopSlice, Set.mem_preimage]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (hw n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (hw n).mpr hn⟩

/-- Whole natural-ledger future law at the first current-population Ready512
slice, with measurability and disjointness established internally. -/
theorem firstReady512_raw_stopped_law {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    rawStoppedSource hp x old (firstReady512Slices p) =
      rawStoppedMixture hp x old (firstReady512Slices p) :=
  raw_stopped_law hp x old (firstReady512Slices p) (measurableSet_firstReady512Slices p)

/-- The selected complete marked past and whole raw future may be observed
jointly at the first Ready hit. The raw future retains original q/nd values. -/
theorem firstReady512_joint_reward {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (F : ∀ n : ℕ, Prefix p n × RawPath p → ℝ≥0∞)
    (hF : ∀ n, Measurable (F n)) :
    (∫⁻ w, ∑' n : ℕ,
      if frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ firstReady512Slices p n then
        F n (frestrictLe n w, normalizedEventSuffix n (rawSequence p x w)) else 0
      ∂CF3MarkedKernel.eventLaw hp (coreProject x) old) =
      ∑' n : ℕ, ∫⁻ u in firstReady512Slices p n, ∫⁻ r, F n (u, r)
        ∂rawLiftLaw hp (prefixRaw p x n u) (lastMarked p n u).2
        ∂markedPrefixLaw hp x old n :=
  raw_stop_family_joint_reward hp x old (firstReady512Slices p)
    (measurableSet_firstReady512Slices p) F hF

/-- Missing mass is exactly literal raw-state nonhitting. In particular no
almost-sure recovery or finite Ready index is assumed. -/
theorem firstReady512_nonhit_mass {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    rawStoppedSource hp x old (firstReady512Slices p) Set.univ +
      CF3MarkedKernel.eventLaw hp (coreProject x) old
        {w | ¬ ∃ n : ℕ, firstReady512Raw p x w n} = 1 := by
  have he : CF3MarkedKernel.eventLaw hp (coreProject x) old
      (eventIndexHitEvent (firstReady512Slices p))ᶜ =
        CF3MarkedKernel.eventLaw hp (coreProject x) old
          {w | ¬ ∃ n : ℕ, firstReady512Raw p x w n} := by
    apply measure_congr
    filter_upwards [ae_firstReady512_hit hp x old] with w hw
    exact propext (not_congr hw)
  rw [← he]
  exact raw_stopped_nonhit_mass hp x old (firstReady512Slices p)
    (measurableSet_firstReady512Slices p) (firstReady512Slices_disjoint p)

/-- Actual division labels include basal and triggered divisions and permit
state-null complete operations. Explicit idle and chemical marks are excluded. -/
def actualDivisionMark {p : Par} : Option (Mark p) → Prop
  | none => False
  | some (.inl _) => False
  | some (.inr _) => True

/-- The fresh coordinate-zero sentinel is never an executed division. -/
def firstDivisionSlices (p : Par) : ∀ n : ℕ, Set (Prefix p n) :=
  firstSlices p (fun n z => 0 < n ∧ actualDivisionMark z.2)

theorem measurableSet_firstDivisionSlices (p : Par) (n : ℕ) :
    MeasurableSet (firstDivisionSlices p n) :=
  measurableSet_firstSlices p (fun n z => 0 < n ∧ actualDivisionMark z.2) n

theorem firstDivisionSlices_disjoint (p : Par) :
    Pairwise (fun n m => Disjoint (eventIndexStopSlice (firstDivisionSlices p) n)
      (eventIndexStopSlice (firstDivisionSlices p) m)) :=
  firstSlices_disjoint p (fun n z => 0 < n ∧ actualDivisionMark z.2)

theorem firstDivision_positive (p : Par) (w : MarkedPath p) (n : ℕ)
    (hn : frestrictLe (π := fun _ : ℕ => ℝ × CF3MarkedKernel.State p) n w ∈ firstDivisionSlices p n) :
    0 < n ∧ actualDivisionMark (w n).2.2 :=
  ((firstSlices_pullback p (fun n z => 0 < n ∧ actualDivisionMark z.2) w n).mp hn).1

theorem firstDivision_zero_empty (p : Par) : firstDivisionSlices p 0 = ∅ := by
  ext u
  constructor
  · intro h
    exact (Nat.lt_irrefl 0 h.1.1).elim
  · intro h
    exact h.elim

theorem firstDivision_raw_stopped_law {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    rawStoppedSource hp x old (firstDivisionSlices p) =
      rawStoppedMixture hp x old (firstDivisionSlices p) :=
  raw_stopped_law hp x old (firstDivisionSlices p) (measurableSet_firstDivisionSlices p)

theorem firstDivision_nonhit_mass {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) :
    rawStoppedSource hp x old (firstDivisionSlices p) Set.univ +
      CF3MarkedKernel.eventLaw hp (coreProject x) old (eventIndexHitEvent (firstDivisionSlices p))ᶜ = 1 :=
  raw_stopped_nonhit_mass hp x old (firstDivisionSlices p)
    (measurableSet_firstDivisionSlices p) (firstDivisionSlices_disjoint p)

end
end CTMCHeredity20261019.V2.RecoveryStops
