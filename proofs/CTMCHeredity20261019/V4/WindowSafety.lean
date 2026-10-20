module

public import proofs.CTMCHeredity20261019.V2.PhysicalRecoveryStops

@[expose] public section

/-!
# A measurable closed-window safety event

The state at the left endpoint is tested separately. Later tests range over
the countable actual proposal arrivals in `(a,b]`, including idle proposals
and state-null marked operations. On the actual positive, unbounded clock
support this is exactly safety at every physical time in `[a,b]`.

No finite-state restriction, stochastic restart hypothesis, quantitative
recovery estimate, or mission-success assertion is used.
-/

namespace CTMCHeredity20261019.V4.WindowSafety

open MeasureTheory Set HybridCTMC.Kernel
open CTMCHeredity20261019.V2
open NoBoundaryArrival PhysicalRecoveryStops
open scoped Classical
noncomputable section

abbrev Path (S : Type*) := ℕ → ℝ × S

/-- Countable tests for safety throughout a closed physical window. An
arrival at `a` is already included in `timedState a`; an arrival at `b` is
included among the later completed arrivals. -/
def windowSafe {S : Type*} (safe : S → Prop) (a b : ℝ) (w : Path S) : Prop :=
  safe (timedState a w) ∧ ∀ k : ℕ,
    a < arrivalTime (k + 1) w → arrivalTime (k + 1) w ≤ b → safe (w (k + 1)).2

theorem measurableSet_windowSafe {S : Type*} [MeasurableSpace S]
    (safe : S → Prop) (hsafe : MeasurableSet {x | safe x}) (a b : ℝ) :
    MeasurableSet {w : Path S | windowSafe safe a b w} := by
  have hstart : MeasurableSet {w : Path S | safe (timedState a w)} :=
    hsafe.preimage (measurable_timedState a)
  have hstep (k : ℕ) : MeasurableSet {w : Path S |
      a < arrivalTime (k + 1) w → arrivalTime (k + 1) w ≤ b → safe (w (k + 1)).2} := by
    have harr : Measurable (arrivalTime (S := S) (k + 1)) := measurable_arrival (k + 1)
    have hleft : MeasurableSet {w : Path S | a < arrivalTime (k + 1) w} :=
      measurableSet_lt measurable_const harr
    have hright : MeasurableSet {w : Path S | arrivalTime (k + 1) w ≤ b} :=
      measurableSet_le harr measurable_const
    have hstate : MeasurableSet {w : Path S | safe (w (k + 1)).2} :=
      hsafe.preimage (measurable_pi_apply (X := fun _ : ℕ => ℝ × S) (k + 1)).snd
    exact hleft.imp (hright.imp hstate)
  convert hstart.inter (MeasurableSet.iInter hstep) using 1
  ext w
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, windowSafe]

/-- Exact pointwise meaning of the measurable event. The support is the
existing genuine clock support; its boundary set is empty, so no endpoint
avoidance assumption is needed. -/
theorem windowSafe_iff_forall {S : Type*} (safe : S → Prop) (a b : ℝ)
    (w : Path S) (ha : 0 ≤ a) (hab : a ≤ b) (hw : ClockBoundarySupport ∅ w) :
    windowSafe safe a b w ↔ ∀ t : ℝ, a ≤ t → t ≤ b → safe (timedState t w) := by
  constructor
  · intro hs t hat htb
    have haseg := clockIndex_segment ha w (hw.2.1 a)
    have htseg := clockIndex_segment (ha.trans hat) w (hw.2.1 t)
    have hmono : clockIndex a w ≤ clockIndex t w := by
      by_contra h
      have hlt : clockIndex t w < clockIndex a w := Nat.lt_of_not_ge h
      have harr := (arrivalTime_mono w) (Nat.succ_le_of_lt hlt)
      linarith [haseg.1, htseg.2]
    by_cases hle : clockIndex t w ≤ clockIndex a w
    · have he : clockIndex t w = clockIndex a w := Nat.le_antisymm hle hmono
      change safe (w (clockIndex t w)).2
      rw [he]
      exact hs.1
    · have hlt : clockIndex a w < clockIndex t w := Nat.lt_of_not_ge hle
      have harr : a < arrivalTime (clockIndex t w) w :=
        haseg.2.trans_le ((arrivalTime_mono w) (Nat.succ_le_of_lt hlt))
      have hpos : 0 < clockIndex t w := (Nat.zero_le (clockIndex a w)).trans_lt hlt
      have he : clockIndex t w - 1 + 1 = clockIndex t w :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      have hsafe := hs.2 (clockIndex t w - 1)
        (by rw [he]; exact harr) (by rw [he]; exact htseg.1.trans htb)
      change safe (w (clockIndex t w)).2
      rw [he] at hsafe
      exact hsafe
  · intro hs
    refine ⟨hs a le_rfl hab, ?_⟩
    intro k hleft hright
    have hsafe := hs (arrivalTime (k + 1) w) hleft.le hright
    rw [timedState_at_arrival w hw.1 (k + 1)] at hsafe
    exact hsafe

/-- The same exact event with local elapsed time, for a window beginning at
`a` and lasting `d`. Both local endpoints remain included. -/
theorem windowSafe_iff_local {S : Type*} (safe : S → Prop) (a d : ℝ)
    (w : Path S) (ha : 0 ≤ a) (hd : 0 ≤ d) (hw : ClockBoundarySupport ∅ w) :
    windowSafe safe a (a + d) w ↔
      ∀ u : ℝ, 0 ≤ u → u ≤ d → safe (timedState (a + u) w) := by
  rw [windowSafe_iff_forall safe a (a + d) w ha (le_add_of_nonneg_right hd) hw]
  constructor
  · intro hs u hu hud
    exact hs (a + u) (le_add_of_nonneg_right hu) (by linarith)
  · intro hs t hat htb
    have hlo : 0 ≤ t - a := sub_nonneg.mpr hat
    have hhi : t - a ≤ d := by linarith
    have hsafe := hs (t - a) hlo hhi
    have he : a + (t - a) = t := by ring
    rw [he] at hsafe
    exact hsafe

end
end CTMCHeredity20261019.V4.WindowSafety
