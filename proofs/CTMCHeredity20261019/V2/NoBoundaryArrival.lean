module

public import proofs.HybridCTMCInfrastructure.ClockHistoryFactorization
public import proofs.CTMCHeredity20261019.CF3RawPathLift

@[expose] public section

/-!
# Version 2: actual proposal arrivals avoid deterministic time boundaries

The existing `clock_history_step` theorem exposes the complete actual prefix
before the last holding time is sampled.  Its inner exponential integral is
zero at every deterministic target, including when the target minus the prefix
arrival is nonpositive.  This is proved using the actual exponential measure's
atomlessness and its nonnegative support; clipped `max 0` holds are unchanged.

The arrival at coordinate zero is the deterministic time-zero sentinel and is
deliberately excluded.  Every positive proposal index is covered, including
idle proposals and actual state-null operations.  A fixed countable grid can
be excluded on one full-measure set.  The raw source lift retains exactly the
same holds, so these statements also hold under its actual pushforward law.

This removes the deterministic endpoint equality ambiguity.  It does not
identify two different proposal envelopes or a common-clock seed-erasure law.
-/

namespace CTMCHeredity20261019.V2.NoBoundaryArrival

open MeasureTheory ProbabilityTheory HybridCTMC.Kernel Set
open scoped ENNReal Classical
noncomputable section

/-- Full clock support for a fixed boundary set: positive actual holds,
unbounded arrivals, and no positive-index arrival in the boundary set.
The coordinate-zero time/mark is a sentinel, not an executed operation. -/
def ClockBoundarySupport {S : Type*} (B : Set ℝ) (w : ℕ → ℝ × S) : Prop :=
  (∀ n : ℕ, 0 < (w (n + 1)).1) ∧
  (∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n w) ∧
  (∀ n : ℕ, arrivalTime (n + 1) w ∉ B)

/-- Clock support is unchanged by any reconstruction retaining every sampled
hold.  In particular, this does not require finite or countable state spaces. -/
theorem clockBoundarySupport_congr_holds {A C : Type*} (B : Set ℝ)
    (v : ℕ → ℝ × A) (w : ℕ → ℝ × C) (hholds : ∀ n : ℕ, (v n).1 = (w n).1) :
    ClockBoundarySupport B v ↔ ClockBoundarySupport B w := by
  have harr (n : ℕ) : arrivalTime n v = arrivalTime n w := by
    unfold arrivalTime
    apply Finset.sum_congr rfl
    intro i _
    rw [hholds (i + 1)]
  simp only [ClockBoundarySupport, hholds, harr]

private def boundaryValue (T t : ℝ) : ℝ≥0∞ := if t = T then 1 else 0

private theorem measurable_boundaryValue (T : ℝ) : Measurable (boundaryValue T) :=
  Measurable.ite (show MeasurableSet {t : ℝ | t = T} from measurableSet_singleton T)
    measurable_const measurable_const

/-- Atomlessness is used after a complete past has fixed `a`.  Clipping is
removed only on the actual exponential law's proved nonnegative support. -/
theorem ae_shifted_clipped_hold_ne (Lam a T : ℝ) :
    ∀ᵐ h ∂expMeasure Lam, a + max 0 h ≠ T := by
  let : NullSingletonClass (expMeasure Lam) := by
    unfold expMeasure gammaMeasure
    infer_instance
  filter_upwards [HybridCTMC.HoldingTime.ae_nonneg Lam,
    (expMeasure Lam).ae_ne (T - a)] with h hnonneg hne
  rw [max_eq_right hnonneg]
  intro he
  apply hne
  linarith

private theorem lintegral_shifted_clipped_boundary (Lam a T : ℝ) :
    (∫⁻ h, boundaryValue T (a + max 0 h) ∂expMeasure Lam) = 0 := by
  calc
    _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂expMeasure Lam := by
      apply lintegral_congr_ae
      filter_upwards [ae_shifted_clipped_hold_ne Lam a T] with h hne
      exact ite_eq_right hne
    _ = 0 := lintegral_zero

section Measurable

variable {S : Type*} [MeasurableSpace S]

theorem measurable_arrival (n : ℕ) :
    Measurable (arrivalTime (S := S) n) :=
  (measurable_arrivalTime n).mono (Filtration.piLE.le n) le_rfl

theorem measurableSet_arrival_eq (n : ℕ) (T : ℝ) :
    MeasurableSet {w : ℕ → ℝ × S | arrivalTime n w = T} :=
  (measurable_arrival n) (measurableSet_singleton T)

theorem measurableSet_no_boundary (T : ℝ) :
    MeasurableSet {w : ℕ → ℝ × S | ∀ n : ℕ, arrivalTime (n + 1) w ≠ T} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n => (measurableSet_arrival_eq (n + 1) T).compl

omit [MeasurableSpace S] in
/-- Real-horizon unboundedness has a countable natural-horizon test. -/
theorem arrivals_unbounded_iff_nat (w : ℕ → ℝ × S) :
    (∀ T : ℝ, ∃ n : ℕ, T < arrivalTime n w) ↔
      (∀ m : ℕ, ∃ n : ℕ, (m : ℝ) < arrivalTime n w) := by
  constructor
  · intro h m
    exact h (m : ℝ)
  · intro h T
    obtain ⟨m, hm⟩ := exists_nat_gt T
    obtain ⟨n, hn⟩ := h m
    exact ⟨n, hm.trans hn⟩

/-- The full clock/boundary predicate is measurable even for an infinite raw
state carrier.  Only the deterministic boundary set must be countable. -/
theorem measurableSet_clockBoundarySupport (B : Set ℝ) (hB : B.Countable) :
    MeasurableSet {w : ℕ → ℝ × S | ClockBoundarySupport B w} := by
  have hpos : MeasurableSet {w : ℕ → ℝ × S | ∀ n : ℕ, 0 < (w (n + 1)).1} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_lt measurable_const (measurable_pi_apply (n + 1)).fst
  have hunbounded : MeasurableSet {w : ℕ → ℝ × S |
      ∀ m : ℕ, ∃ n : ℕ, (m : ℝ) < arrivalTime n w} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_arrival n)
  have hboundaries : MeasurableSet {w : ℕ → ℝ × S |
      ∀ n : ℕ, arrivalTime (n + 1) w ∉ B} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      ((measurable_arrival (n + 1)) hB.measurableSet).compl
  have he : {w : ℕ → ℝ × S | ClockBoundarySupport B w} =
      {w : ℕ → ℝ × S | (∀ n : ℕ, 0 < (w (n + 1)).1) ∧
        (∀ m : ℕ, ∃ n : ℕ, (m : ℝ) < arrivalTime n w) ∧
        (∀ n : ℕ, arrivalTime (n + 1) w ∉ B)} := by
    ext w
    simp only [mem_ofPred_eq, ClockBoundarySupport, arrivals_unbounded_iff_nat]
  rw [he]
  exact hpos.inter (hunbounded.inter hboundaries)

end Measurable

section ActualEventLaw

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Each positive arrival under the constructed event law has zero mass at
every deterministic real target.  The proof uses the source's full-prefix
clock disintegration; no conditional clock or restart law is hypothesized. -/
theorem arrivalTime_atom_eq_zero (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (n : ℕ) (T : ℝ) :
    K.eventLaw Lam hLam x {w | arrivalTime (n + 1) w = T} = 0 := by
  have hstep := K.clock_history_step hLam x n (boundaryValue T)
    (measurable_boundaryValue T) (fun _ => 1)
  have hzero : (∫⁻ w, boundaryValue T (arrivalTime (n + 1) w)
      ∂K.eventLaw Lam hLam x) = 0 := by
    simpa only [mul_one, lintegral_shifted_clipped_boundary, zero_mul,
      lintegral_zero] using hstep
  have he : (fun w : ℕ → ℝ × S => boundaryValue T (arrivalTime (n + 1) w)) =
      {w : ℕ → ℝ × S | arrivalTime (n + 1) w = T}.indicator
        (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    rfl
  rw [he, lintegral_indicator_const (measurableSet_arrival_eq (n + 1) T),
    one_mul] at hzero
  exact hzero

/-- All positive proposal arrivals avoid the fixed deterministic boundary on
one full-measure set.  This includes `T = 0`, but never asserts that the
coordinate-zero sentinel avoids zero. -/
theorem ae_no_boundary_arrival (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, ∀ n : ℕ, arrivalTime (n + 1) w ≠ T := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  simpa only [not_not] using arrivalTime_atom_eq_zero K hLam x n T

/-- The same statement with an arbitrary positive natural arrival index. -/
theorem ae_no_boundary_positive_index (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, ∀ n : ℕ, 0 < n → arrivalTime n w ≠ T := by
  filter_upwards [ae_no_boundary_arrival K hLam x T] with w hw
  intro n hn
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ n => exact hw n

/-- Every fixed countable family of deterministic boundaries is avoided
simultaneously.  The family need not be injective, ordered, or nonnegative. -/
theorem ae_no_countable_boundaries {I : Type*} [Countable I]
    (K : HybridCTMC.Kernel S) {Lam : ℝ} (hLam : 0 < Lam) (x : S) (grid : I → ℝ) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x,
      ∀ i : I, ∀ n : ℕ, arrivalTime (n + 1) w ≠ grid i := by
  rw [ae_all_iff]
  intro i
  exact ae_no_boundary_arrival K hLam x (grid i)

theorem ae_no_finite_boundaries (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (m : ℕ) (grid : Fin m → ℝ) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x,
      ∀ i : Fin m, ∀ n : ℕ, arrivalTime (n + 1) w ≠ grid i :=
  ae_no_countable_boundaries K hLam x grid

/-- Set-indexed version, convenient for the union of several deterministic
service grids and the withdrawal boundary. -/
theorem ae_no_countable_boundary_set (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, ∀ n : ℕ, arrivalTime (n + 1) w ∉ B := by
  let := hB.to_subtype
  filter_upwards [ae_no_countable_boundaries K hLam x (fun i : B => (i : ℝ))] with w hw
  intro n hn
  exact hw ⟨arrivalTime (n + 1) w, hn⟩ n rfl

/-- Full measurable clock/boundary support under the actual constructed event
law.  Consumers may propagate this property through each actual conditional
segment kernel and hence the joint operated history law. -/
theorem ae_clockBoundarySupport [StandardBorelSpace S] (K : HybridCTMC.Kernel S)
    {Lam : ℝ} (hLam : 0 < Lam) (x : S) (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, ClockBoundarySupport B w := by
  filter_upwards [K.ae_holding_pos hLam x,
    CTMCHeredity20261019.ae_arrivals_unbounded K hLam x,
    ae_no_countable_boundary_set K hLam x B hB] with w hp hu hb
  exact ⟨hp, hu, hb⟩

/-- The exact strict/non-strict endpoint distinction disappears almost surely
for actual proposals at a deterministic boundary. -/
theorem ae_arrival_lt_iff_le (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) (T : ℝ) :
    ∀ᵐ w ∂K.eventLaw Lam hLam x, ∀ n : ℕ,
      (arrivalTime (n + 1) w < T ↔ arrivalTime (n + 1) w ≤ T) := by
  filter_upwards [ae_no_boundary_arrival K hLam x T] with w hw
  intro n
  exact ⟨le_of_lt, fun hle => lt_of_le_of_ne hle (hw n)⟩

/-- Deterministic sentinel boundary retained explicitly: the time-zero arrival
has full mass at zero, so extending the atomlessness claim to index zero
would be false. -/
theorem arrivalTime_zero_mass (K : HybridCTMC.Kernel S) {Lam : ℝ}
    (hLam : 0 < Lam) (x : S) :
    K.eventLaw Lam hLam x {w | arrivalTime 0 w = 0} = 1 := by
  simp [arrivalTime]

end ActualEventLaw

section ConcreteSource

open FunctionalCapacity CF3Marked CF3RawPathLift

local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩

/-- Actual marked source law, with its own literal rate envelope.  This applies
separately to either valid source phase and every initial state/old sentinel. -/
theorem cf3_marked_ae_no_boundary {p : Par} (hp : p.Valid) (x : CoreState p)
    (old : Option (Mark p)) (T : ℝ) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp x old,
      ∀ n : ℕ, arrivalTime (n + 1) w ≠ T :=
  ae_no_boundary_arrival (CF3MarkedKernel.kernel hp) (CF3MarkedKernel.rate_positive hp)
    (x, old) T

theorem cf3_marked_ae_no_countable_boundaries {I : Type*} [Countable I]
    {p : Par} (hp : p.Valid) (x : CoreState p) (old : Option (Mark p)) (grid : I → ℝ) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp x old,
      ∀ i : I, ∀ n : ℕ, arrivalTime (n + 1) w ≠ grid i :=
  ae_no_countable_boundaries (CF3MarkedKernel.kernel hp)
    (CF3MarkedKernel.rate_positive hp) (x, old) grid

/-- Concrete source support, ready to feed the operated law's joint
all-segments support theorem for every initial source state. -/
theorem cf3_marked_ae_clockBoundarySupport {p : Par} (hp : p.Valid) (x : CoreState p)
    (old : Option (Mark p)) (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp x old, ClockBoundarySupport B w :=
  ae_clockBoundarySupport (CF3MarkedKernel.kernel hp)
    (CF3MarkedKernel.rate_positive hp) (x, old) B hB

/-- Raw reconstruction keeps the same holds verbatim, with arbitrary natural
initial q/nd ledgers.  No raw-clock independence premise is needed. -/
theorem cf3_rawSequence_ae_no_boundary {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (T : ℝ) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ∀ n : ℕ, arrivalTime (n + 1) (rawSequence p x w) ≠ T := by
  simpa only [rawSequence_arrivalTime] using
    cf3_marked_ae_no_boundary hp (coreProject x) old T

/-- The no-boundary property holds under the constructed raw pushforward law,
not only after evaluating a raw fold on the marked probability space. -/
theorem cf3_rawLiftLaw_ae_no_boundary {p : Par} (hp : p.Valid) (x : SourceState p)
    (old : Option (Mark p)) (T : ℝ) :
    ∀ᵐ w ∂rawLiftLaw hp x old, ∀ n : ℕ, arrivalTime (n + 1) w ≠ T := by
  unfold rawLiftLaw
  exact (MeasureTheory.ae_map_iff (measurable_rawSequence p x).aemeasurable
    (measurableSet_no_boundary T)).mpr
    (cf3_rawSequence_ae_no_boundary hp x old T)

theorem cf3_rawLiftLaw_ae_no_countable_boundaries {I : Type*} [Countable I]
    {p : Par} (hp : p.Valid) (x : SourceState p) (old : Option (Mark p)) (grid : I → ℝ) :
    ∀ᵐ w ∂rawLiftLaw hp x old,
      ∀ i : I, ∀ n : ℕ, arrivalTime (n + 1) w ≠ grid i := by
  rw [ae_all_iff]
  intro i
  exact cf3_rawLiftLaw_ae_no_boundary hp x old (grid i)

theorem cf3_rawSequence_ae_clockBoundarySupport {p : Par} (hp : p.Valid)
    (x : SourceState p) (old : Option (Mark p)) (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ w ∂CF3MarkedKernel.eventLaw hp (coreProject x) old,
      ClockBoundarySupport B (rawSequence p x w) := by
  filter_upwards [cf3_marked_ae_clockBoundarySupport hp (coreProject x) old B hB]
    with w hw
  exact (clockBoundarySupport_congr_holds B (rawSequence p x w) w
    (fun _ => rfl)).mpr hw

theorem cf3_rawLiftLaw_ae_clockBoundarySupport {p : Par} (hp : p.Valid)
    (x : SourceState p) (old : Option (Mark p)) (B : Set ℝ) (hB : B.Countable) :
    ∀ᵐ w ∂rawLiftLaw hp x old, ClockBoundarySupport B w := by
  unfold rawLiftLaw
  exact (MeasureTheory.ae_map_iff (measurable_rawSequence p x).aemeasurable
    (measurableSet_clockBoundarySupport B hB)).mpr
      (cf3_rawSequence_ae_clockBoundarySupport hp x old B hB)

end ConcreteSource

end
end CTMCHeredity20261019.V2.NoBoundaryArrival
