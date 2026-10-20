module

public import proofs.CTMCHeredity20261019.V3.ActualWindows

@[expose] public section

/-! # Floor, service and division observations

All statements concern the actual recorded history and its stitched raw fold.
No success probability is asserted. Service is a within-window credit increase;
the reset initialization needed to read local endpoint q as that increase is
proved explicitly. Stored phase offsets include both q and nd.
-/

namespace CTMCHeredity20261019.V3.Observations

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift V2 V2.LedgerOffsets V2.NoBoundaryArrival
open WindowIdentity ActualWindows
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

/-- Explicit zero initial q propagates through actual q-only reset starts. -/
theorem compatible_start_q_zero (p : Par) (T : ℝ) (n : ℕ) (x : SourceState p)
    (h : RawOperated.History p n) (hc : RawOperated.compatible p T n x h)
    (hq : ∀ i j, (x i).q j = 0) :
    ∀ b : Fin n, ∀ i j, (((h.1 b).2 0).2 i).q j = 0 := by
  induction n generalizing x with
  | zero => exact fun b => Fin.elim0 b
  | succ n ih =>
      intro b
      refine Fin.cases ?_ (fun k => ?_) b
      · intro i j
        rw [hc.1]
        exact hq i j
      · exact ih (RawOperated.nextState p T (h.1 0)) (Operated.tail h) hc.2
          (fun _ _ => rfl) k

theorem faithful_timed_zero (p : Par) (s : RawOperated.Segment p)
    (hf : RawOperated.faithful p s) (hk : ClockBoundarySupport ∅ s.1) :
    timedState 0 s.2 = (s.2 0).2 := by
  obtain ⟨y, _, hr⟩ := hf
  have ha : 0 < arrivalTime 1 s.1 := by
    simpa [arrivalTime, max_eq_right (hk.1 0).le] using hk.1 0
  have hi := clockIndex_eq_of_between s.1 0 (by simp [arrivalTime]) ha
  rw [hr]
  change rawAt p y s.1 (clockIndex 0 s.1) = rawAt p y s.1 0
  rw [hi]

/-- Physical counts and fuel, natural credits and cumulative nd agree at every
local time on one full-measure set. -/
theorem completedLaw_ae_coordinates {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      ∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ i : Fin p.M,
        (globalState p T n x z ((b.val : ℝ)*T+t) i).a = (localState p z.1 b t i).a ∧
        (globalState p T n x z ((b.val : ℝ)*T+t) i).R = (localState p z.1 b t i).R ∧
        (∀ j, (globalState p T n x z ((b.val : ℝ)*T+t) i).q j =
          (localState p z.1 b t i).q j + qOffset p T n z.1 b.val i j) ∧
        (globalState p T n x z ((b.val : ℝ)*T+t) i).nd = (localState p z.1 b t i).nd := by
  filter_upwards [completedLaw_ae_windows_and_terminal hp T hT n x] with z hz
  intro b t ht htT i
  rw [hz.1 b t ht htT]
  exact ⟨rfl, rfl, fun _ => rfl, Nat.add_zero _⟩

/-- Arbitrary species/slot floor requirements transfer jointly over all windows. -/
theorem completedLaw_ae_floors_iff {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p)
    (floor : Fin n → Fin p.M → Fin p.c → ℕ) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ i j,
        floor b i j ≤ ((localState p z.1 b t i).a j).val) ↔
      (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ i j,
        floor b i j ≤ ((globalState p T n x z ((b.val : ℝ)*T+t) i).a j).val) := by
  filter_upwards [completedLaw_ae_coordinates hp T hT n x] with z hz
  constructor <;> intro h b t ht htT i j
  · rw [(hz b t ht htT i).1]
    exact h b t ht htT i j
  · rw [← (hz b t ht htT i).1]
    exact h b t ht htT i j

/-- The terminal nd observation already includes all earlier blocks. -/
theorem completedLaw_ae_terminal_divisions_iff {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      ∀ i : Fin p.M, ∀ D : ℕ,
        D ≤ (z.1.2 i).nd ↔ D ≤ (globalState p T n x z ((n : ℝ)*T) i).nd := by
  filter_upwards [completedLaw_ae_windows_and_terminal hp T hT n x] with z hz
  intro i D
  rw [hz.2, addLedgers_nd, Nat.add_zero]

/-- With zero initial q, each local endpoint is exactly its window's newly
earned credit. An absolute cumulative threshold is not substituted for this. -/
theorem completedLaw_ae_service_iff {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p)
    (hq : ∀ i j, (x i).q j = 0) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      ∀ b : Fin n, ∀ i j m,
        m ≤ (localState p z.1 b T i).q j ↔
          (globalState p T n x z ((b.val : ℝ)*T) i).q j + m ≤
            (globalState p T n x z ((b.val : ℝ)*T+T) i).q j := by
  filter_upwards [Support.completedLaw_ae_support hp T n x,
    completedLaw_ae_windows_and_terminal hp T hT n x] with z hs hz
  intro b i j m
  have hzero : (localState p z.1 b 0 i).q j = 0 := by
    unfold localState
    rw [faithful_timed_zero p _ (hs.2.1 b) (hs.2.2.1 b)]
    exact compatible_start_q_zero p T n x z.1 hs.1 hq b i j
  have he := congrArg (fun y : SourceState p => (y i).q j) (hz.1 b T hT le_rfl)
  have hb := congrArg (fun y : SourceState p => (y i).q j) (hz.1 b 0 le_rfl hT)
  simp only [addLedgers_q, add_zero, hzero, zero_add] at he hb
  rw [he, hb]
  omega

/-- The canonical resetAll initialization discharges the service hypothesis;
it clears observations only and does not change counts or fuel. -/
theorem completedLaw_resetAll_ae_service_iff {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n (sourceResetAll x),
      ∀ b : Fin n, ∀ i j m,
        m ≤ (localState p z.1 b T i).q j ↔
          (globalState p T n (sourceResetAll x) z ((b.val : ℝ)*T) i).q j + m ≤
            (globalState p T n (sourceResetAll x) z ((b.val : ℝ)*T+T) i).q j :=
  completedLaw_ae_service_iff hp T hT n (sourceResetAll x) (fun _ _ => rfl)

/-- A phase whose observational reset cleared q and nd can be reconstructed
with its actual stored pre-phase ledgers. nd adds the stored prefix once. -/
theorem completedLaw_resetAll_ae_stored_offsets {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n (sourceResetAll x),
      (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
        globalState p T n x z ((b.val : ℝ)*T+t) =
          addLedgers p (localState p z.1 b t)
            (fun i j => qOffset p T n z.1 b.val i j + qLedger x i j) (dLedger x)) ∧
      globalState p T n x z ((n : ℝ)*T) =
        addLedgers p z.1.2
          (fun i j => qOffset p T n z.1 n i j + qLedger x i j) (dLedger x) := by
  simpa only [resetAll_restore] using
    completedLaw_ae_windows_and_terminal_addLedgers hp T hT n (sourceResetAll x)
      (qLedger x) (dLedger x)

end
end CTMCHeredity20261019.V3.Observations
