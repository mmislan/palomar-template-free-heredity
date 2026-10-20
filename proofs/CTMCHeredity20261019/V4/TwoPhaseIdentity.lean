module

public import proofs.CTMCHeredity20261019.V3.WindowIdentity
public import proofs.CTMCHeredity20261019.V2.SeedSwitch

@[expose] public section

/-!
# Version 4: joint executed-window identities through seed withdrawal

The complete source updates are equal for the two canonical phases; their
rates and sampled laws remain distinct. Backward stitching keeps only the
executed prefixes. After the seeded phase, its entire accumulated q offset
and one constant spatial nd ledger are restored to the resetAll off phase.
No local cumulative nd endpoints are summed and no resource is replenished.

These are deterministic source-fold identities on the already constructed
compatible, faithful, regular history support. No desired path-law equality,
mission event or probability estimate is a premise. The actual joint-law
support and simultaneous event transfer are separate consumers.
-/

namespace CTMCHeredity20261019.V4.TwoPhaseIdentity

open FunctionalCapacity HybridCTMC.Kernel
open CTMCHeredity20261019.CF3Marked CTMCHeredity20261019.CF3RawPathLift
open CTMCHeredity20261019.V2
open NoBoundaryArrival LedgerOffsets ExecutedWindows SeedSwitch
open CTMCHeredity20261019.V3.WindowIdentity
open scoped BigOperators Classical
noncomputable section

/-- After all recorded windows, the actual positive terminal marks are folded
from the returned state, carrying exactly the prior fixed-slot q offset. -/
theorem stitch_raw_after (p : Par) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (x : SourceState p) (h : RawOperated.History p n) (v : MarkedPath p)
    (hc : RawOperated.compatible p T n x h)
    (hf : RawOperated.allSegments (RawOperated.faithful p) h)
    (hh : ∀ b : Fin n, ClockBoundarySupport ∅ (h.1 b).1)
    (hv : ClockBoundarySupport ∅ v) (u : ℝ) (hu : 0 ≤ u) :
    timedState ((n : ℝ) * T + u)
        (rawSequence p x (PhysicalOperated.stitch p T n (h, v))) =
      addLedgers p (timedState u (rawSequence p h.2 v)) (qOffset p T n h n) (fun _ => 0) := by
  induction n generalizing x with
  | zero =>
      have hx : h.2 = x := hc
      simp only [Nat.cast_zero, zero_mul, zero_add, PhysicalOperated.stitch,
        qOffset_zero, addLedgers_zero, hx]
  | succ n ih =>
      let s : RawOperated.Segment p := h.1 0
      let r : MarkedPath p := PhysicalOperated.stitch p T n (Operated.tail h, v)
      have hraw : s.2 = rawSequence p x s.1 :=
        faithful_raw_eq_of_start p s x (hf 0) hc.1
      have hend : timedState T (rawSequence p x s.1) = timedState T s.2 :=
        congrArg (timedState T) hraw.symm
      have hft : RawOperated.allSegments (RawOperated.faithful p) (Operated.tail h) :=
        fun b => hf b.succ
      have hht : ∀ b : Fin n, ClockBoundarySupport ∅ ((Operated.tail h).1 b).1 :=
        fun b => hh b.succ
      have hr : ClockBoundarySupport ∅ r :=
        OperatedObservations.stitch_clockSupport p T hT n (Operated.tail h) v hht hv
      have hit := ih (RawOperated.nextState p T s) (Operated.tail h) hc.2 hft hht
      change timedState ((n : ℝ) * T + u)
          (rawSequence p (sourceResetQ (timedState T s.2)) r) =
        addLedgers p (timedState u (rawSequence p h.2 v))
          (qOffset p T n (Operated.tail h) n) (fun _ => 0) at hit
      have hnu : 0 ≤ (n : ℝ) * T + u :=
        add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT) hu
      have he := splice_raw_resetQ_restore p x T ((n : ℝ) * T + u) s.1 r hT
        ((hh 0).2.1 T) (hr.1 0).le hnu (hr.2.1 _)
      rw [hend] at he
      have htime : ((n + 1 : ℕ) : ℝ) * T + u = T + ((n : ℝ) * T + u) := by
        push_cast
        ring
      change timedState (((n + 1 : ℕ) : ℝ) * T + u)
          (rawSequence p x (PhysicalSplice.splice T (s.1, r))) =
        addLedgers p (timedState u (rawSequence p h.2 v))
          (qOffset p T (n + 1) h (n + 1)) (fun _ => 0)
      rw [htime, he, hit, addLedgers_add]
      simp only [qOffset_succ_tail, Operated.tail, Nat.add_zero, s]

/-- Every physical update, including idle and null-state labels, agrees.
This statement compares deterministic folds, not the two proposal laws. -/
theorem rawAt_on_eq_off (x : Raw) (w : MarkedPath seedOff) (n : ℕ) :
    rawAt canonicalSeedOnCF3 x w n = rawAt seedOff x w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change sourceProposalNext canonicalSeedOnCF3 (rawAt canonicalSeedOnCF3 x w n)
          (w (n + 1)).2.2 =
        sourceProposalNext seedOff (rawAt seedOff x w n) (w (n + 1)).2.2
      have h₁ : (sourceProposalNext canonicalSeedOnCF3 (rawAt canonicalSeedOnCF3 x w n)
            (w (n + 1)).2.2 : Raw) =
          (sourceProposalNext canonicalSeedOnCF3 (rawAt seedOff x w n) (w (n + 1)).2.2 : Raw) :=
        congrArg (fun y : Raw =>
          (sourceProposalNext canonicalSeedOnCF3 y (w (n + 1)).2.2 : Raw)) ih
      have h₂ : (sourceProposalNext canonicalSeedOnCF3 (rawAt seedOff x w n)
            (w (n + 1)).2.2 : Raw) =
          (sourceProposalNext seedOff (rawAt seedOff x w n) (w (n + 1)).2.2 : Raw) :=
        sourceProposalNext_same (rawAt seedOff x w n) (w (n + 1)).2.2
      exact h₁.trans h₂

theorem rawSequence_on_eq_off (x : Raw) (w : MarkedPath seedOff) :
    rawSequence canonicalSeedOnCF3 x w = rawSequence seedOff x w := by
  funext n
  exact Prod.ext rfl (rawAt_on_eq_off x w n)

abbrev Completion := TwoPhaseHistory × MarkedPath seedOff

def offPath (z : Completion) : MarkedPath seedOff :=
  PhysicalOperated.stitch seedOff blockDuration 300 (z.1.2, z.2)

def wholePath (z : Completion) : MarkedPath canonicalSeedOnCF3 :=
  PhysicalOperated.stitch canonicalSeedOnCF3 blockDuration 300 (z.1.1, offPath z)

/-- Initial resetAll is explicit. Using the on update in this fold also on
off-phase labels is justified by rawSequence_on_eq_off, not by equal rates. -/
def globalRaw (x : Raw) (z : Completion) : ℕ → ℝ × Raw :=
  rawSequence canonicalSeedOnCF3 (sourceResetAll x) (wholePath z)

def globalState (x : Raw) (z : Completion) (t : ℝ) : Raw := timedState t (globalRaw x z)

def onOffset (h : TwoPhaseHistory) (b : ℕ) : Fin 4 → Fin 3 → ℕ :=
  qOffset canonicalSeedOnCF3 blockDuration 300 h.1 b

def offOffset (h : TwoPhaseHistory) (b : ℕ) : Fin 4 → Fin 3 → ℕ := fun i j =>
  qOffset seedOff blockDuration 300 h.2 b i j + onOffset h 300 i j

def switchDivisions (h : TwoPhaseHistory) : Fin 4 → ℕ := dLedger h.1.2

def switchState (h : TwoPhaseHistory) : Raw :=
  addLedgers seedOff h.1.2 (onOffset h 300) (fun _ => 0)

theorem blockDuration_nonneg : 0 ≤ blockDuration := by norm_num [blockDuration]

theorem phaseDuration : (300 : ℝ) * blockDuration = 30 := by norm_num [blockDuration]

/-- The returned seeded phase state has already had its last q reset.
Its division ledger remains the cumulative seeded-phase division ledger. -/
theorem on_return_q_zero (x : Raw) (h : TwoPhaseHistory) (hc : jointCompatible x h) :
    qLedger h.1.2 = (fun _ _ => 0) := by
  have hl := RawOperated.compatible_final_last canonicalSeedOnCF3 blockDuration 299
    (sourceResetAll x) h.1 hc.1
  funext i j
  change (h.1.2 i).q j = 0
  rw [hl]
  exact RawOperated.nextState_output canonicalSeedOnCF3 blockDuration
    (h.1.1 (Fin.last 299)) i j

/-- The real switch state restores all seeded-phase credits and divisions.
It is not the bookkeeping resetAll state used for local off observations. -/
theorem switchState_restore (x : Raw) (h : TwoPhaseHistory) (hc : jointCompatible x h) :
    switchState h = addLedgers seedOff (sourceResetAll h.1.2)
      (onOffset h 300) (switchDivisions h) := by
  have hq := on_return_q_zero x h hc
  have ha : addLedgers seedOff (sourceResetAll h.1.2) (fun _ _ => 0) (dLedger h.1.2) =
      h.1.2 := by
    rw [← hq, resetAll_restore]
  change addLedgers seedOff h.1.2 (onOffset h 300) (fun _ => 0) = _
  calc
    _ = addLedgers seedOff
        (addLedgers seedOff (sourceResetAll h.1.2) (fun _ _ => 0) (dLedger h.1.2))
        (onOffset h 300) (fun _ => 0) :=
      congrArg (fun y : Raw => addLedgers seedOff y (onOffset h 300) (fun _ => 0)) ha.symm
    _ = addLedgers seedOff (sourceResetAll h.1.2)
        (fun i j => 0 + onOffset h 300 i j) (fun i => dLedger h.1.2 i + 0) :=
      addLedgers_add seedOff (sourceResetAll h.1.2) (fun _ _ => 0) (dLedger h.1.2)
        (onOffset h 300) (fun _ => 0)
    _ = _ := by simp only [Nat.zero_add, Nat.add_zero, switchDivisions]

theorem offPath_clockSupport (z : Completion)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2) : ClockBoundarySupport ∅ (offPath z) :=
  OperatedObservations.stitch_clockSupport seedOff blockDuration blockDuration_nonneg
    300 z.1.2 z.2 hoff hv

/-- All on windows and the exact carried state at time30 are obtained from
the same on-phase stitch with the actual off path as its terminal tail. -/
theorem on_windows_and_switch (x : Raw) (z : Completion)
    (hc : jointCompatible x z.1) (hf : jointFaithful z.1)
    (hon : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2) :
    (∀ b : Fin 300, ∀ t : ℝ, 0 ≤ t → t ≤ blockDuration →
      globalState x z ((b.val : ℝ) * blockDuration + t) =
        addLedgers seedOff (timedState t (z.1.1.1 b).2)
          (onOffset z.1 b.val) (fun _ => 0)) ∧
      globalState x z 30 = switchState z.1 := by
  have he := stitch_raw_windows_and_terminal canonicalSeedOnCF3 blockDuration
    blockDuration_nonneg 300 (sourceResetAll x) z.1.1 (offPath z)
    hc.1 hf.1 hon (offPath_clockSupport z hoff hv)
  constructor
  · exact he.1
  · have ht : ((300 : ℕ) : ℝ) * blockDuration = 30 := by norm_num [blockDuration]
    have hg : globalState x z (((300 : ℕ) : ℝ) * blockDuration) = switchState z.1 := he.2
    rw [ht] at hg
    exact hg

/-- The post30 raw fold begins at the restored cumulative switch state.
It folds the actual off positive marks; no unused on tail is borrowed. -/
theorem globalRaw_after_switch (x : Raw) (z : Completion)
    (hc : jointCompatible x z.1) (hf : jointFaithful z.1)
    (hon : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2) (u : ℝ) (hu : 0 ≤ u) :
    globalState x z (30 + u) =
      timedState u (rawSequence seedOff (switchState z.1) (offPath z)) := by
  have he := stitch_raw_after canonicalSeedOnCF3 blockDuration blockDuration_nonneg 300
    (sourceResetAll x) z.1.1 (offPath z) hc.1 hf.1 hon
    (offPath_clockSupport z hoff hv) u hu
  rw [rawSequence_on_eq_off z.1.1.2 (offPath z)] at he
  have hr := rawSequence_timed_addLedgers seedOff z.1.1.2 (onOffset z.1 300)
    (fun _ => 0) (offPath z) u
  have ht : ((300 : ℕ) : ℝ) * blockDuration = 30 := by norm_num [blockDuration]
  have hg : globalState x z (((300 : ℕ) : ℝ) * blockDuration + u) =
      timedState u (rawSequence seedOff (switchState z.1) (offPath z)) := he.trans hr.symm
  rw [ht] at hg
  exact hg

/-- One simultaneous deterministic correspondence covers all closed windows
of both phases and the terminal state. The off division offset is one stored
on-phase ledger, never a sum of local cumulative nd endpoints. -/
theorem two_phase_windows_and_terminal (x : Raw) (z : Completion)
    (hc : jointCompatible x z.1) (hf : jointFaithful z.1)
    (hon : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.1.1 b).1)
    (hoff : ∀ b : Fin 300, ClockBoundarySupport ∅ (z.1.2.1 b).1)
    (hv : ClockBoundarySupport ∅ z.2) :
    (∀ b : Fin 300, ∀ t : ℝ, 0 ≤ t → t ≤ blockDuration →
      globalState x z ((b.val : ℝ) * blockDuration + t) =
        addLedgers seedOff (timedState t (z.1.1.1 b).2)
          (onOffset z.1 b.val) (fun _ => 0)) ∧
    (∀ b : Fin 300, ∀ t : ℝ, 0 ≤ t → t ≤ blockDuration →
      globalState x z (30 + ((b.val : ℝ) * blockDuration + t)) =
        addLedgers seedOff (timedState t (z.1.2.1 b).2)
          (offOffset z.1 b.val) (switchDivisions z.1)) ∧
      globalState x z 60 = addLedgers seedOff z.1.2.2
        (offOffset z.1 300) (switchDivisions z.1) := by
  have he := stitch_raw_windows_and_terminal_addLedgers seedOff blockDuration
    blockDuration_nonneg 300 (sourceResetAll z.1.1.2) z.1.2 z.2 hc.2 hf.2 hoff hv
    (onOffset z.1 300) (switchDivisions z.1)
  have hy := switchState_restore x z.1 hc
  refine ⟨(on_windows_and_switch x z hc hf hon hoff hv).1, ?_, ?_⟩
  · intro b t ht htT
    have hu : 0 ≤ (b.val : ℝ) * blockDuration + t :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg b.val) blockDuration_nonneg) ht
    have ha := globalRaw_after_switch x z hc hf hon hoff hv
      ((b.val : ℝ) * blockDuration + t) hu
    rw [hy] at ha
    exact ha.trans (he.1 b t ht htT)
  · have ha := globalRaw_after_switch x z hc hf hon hoff hv
      ((300 : ℝ) * blockDuration) (mul_nonneg (by norm_num) blockDuration_nonneg)
    rw [hy] at ha
    have ht : 30 + (300 : ℝ) * blockDuration = 60 := by norm_num [blockDuration]
    change globalState x z 60 = addLedgers seedOff z.1.2.2
      (fun i j => qOffset seedOff blockDuration 300 z.1.2 300 i j + onOffset z.1 300 i j)
      (switchDivisions z.1)
    have hg := ha.trans he.2
    rw [ht] at hg
    exact hg

end
end CTMCHeredity20261019.V4.TwoPhaseIdentity
