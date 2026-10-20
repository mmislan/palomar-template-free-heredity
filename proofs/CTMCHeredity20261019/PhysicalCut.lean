module

public import proofs.HybridCTMCInfrastructure.EventArrival

@[expose] public section

/-!
# Deterministic cutting of the actual holding-time/state sequence

The source API is `HybridCTMC.Kernel.arrivalTime` from EventArrival. Its clock
uses `max 0` on holding times. The source `clockIndex`/`timedState` definitions
live in TimedProcess; their segment characterization is in GeneratorIntegral.
ClockRegularity already proves constancy inside a segment, but none of these
modules constructs the residual holding-time suffix or its arrival identities.

This minimal deterministic ingredient imports only EventArrival. At a cut T
inside the n-th clock interval, coordinate zero records the current state,
coordinate one retains the unused hold until the next arrival, and all later
coordinates retain the source holds and states. No law, independence, Markov,
or memorylessness assertion is assumed here.
-/

namespace CTMCHeredity20261019

noncomputable section
open HybridCTMC.Kernel
open scoped BigOperators

variable {S : Type*}

/-- Cut the actual event sequence inside its n-th holding interval.
The future first hold is residual, while all subsequent coordinates are exact
source suffix coordinates. Coordinate zero has the source's conventional zero
holding time and the current state. -/
def physicalCut (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ) : ℕ → ℝ × S
  | 0 => (0, (w n).2)
  | 1 => (arrivalTime (n + 1) w - T, (w (n + 1)).2)
  | k + 2 => w (n + k + 2)

@[simp] theorem physicalCut_zero (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ) :
    physicalCut w n T 0 = (0, (w n).2) := rfl

@[simp] theorem physicalCut_one (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ) :
    physicalCut w n T 1 = (arrivalTime (n + 1) w - T, (w (n + 1)).2) := rfl

@[simp] theorem physicalCut_later (w : ℕ → ℝ × S) (n k : ℕ) (T : ℝ) :
    physicalCut w n T (k + 2) = w (n + k + 2) := rfl

/-- The suffix keeps every state exactly, including the state at the cut. -/
@[simp] theorem physicalCut_state (w : ℕ → ℝ × S) (n k : ℕ) (T : ℝ) :
    (physicalCut w n T k).2 = (w (n + k)).2 := by
  cases k with
  | zero => simp [physicalCut]
  | succ k =>
      cases k <;> simp [physicalCut, Nat.add_assoc]

/-- The source arrival recursion, exposed locally without importing the wider
martingale/interpolation stack merely for this finite-sum identity. -/
theorem physicalCut_arrival_next (w : ℕ → ℝ × S) (n : ℕ) :
    arrivalTime (n + 1) w = arrivalTime n w + max 0 (w (n + 1)).1 := by
  simp only [arrivalTime, Finset.sum_range_succ]

/-- The unused first hold is exactly the original clipped hold minus its age. -/
theorem physicalCut_residual (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ) :
    (physicalCut w n T 1).1 = max 0 (w (n + 1)).1 - (T - arrivalTime n w) := by
  rw [physicalCut_one, physicalCut_arrival_next]
  ring

theorem physicalCut_residual_pos (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ)
    (hhi : T < arrivalTime (n + 1) w) :
    0 < (physicalCut w n T 1).1 := by
  exact sub_pos.mpr hhi

theorem physicalCut_residual_le_hold (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ)
    (hlo : arrivalTime n w ≤ T) :
    (physicalCut w n T 1).1 ≤ max 0 (w (n + 1)).1 := by
  rw [physicalCut_residual]
  linarith

/-- Every strictly future arrival is translated by exactly T. This also
handles a cut exactly at the n-th arrival and the source's clipped holds. -/
theorem physicalCut_arrival (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ)
    (hhi : T < arrivalTime (n + 1) w) (k : ℕ) :
    arrivalTime (k + 1) (physicalCut w n T) = arrivalTime (n + k + 1) w - T := by
  induction k with
  | zero =>
      have hr : 0 ≤ arrivalTime (n + 1) w - T := (sub_pos.mpr hhi).le
      change arrivalTime 1 (physicalCut w n T) = arrivalTime (n + 1) w - T
      rw [physicalCut_arrival_next (physicalCut w n T) 0,
        show arrivalTime 0 (physicalCut w n T) = 0 by simp [arrivalTime],
        physicalCut_one, zero_add, max_eq_right hr]
  | succ k ih =>
      have hn : n + (k + 1) + 1 = (n + k + 1) + 1 := by simp [Nat.add_assoc]
      rw [physicalCut_arrival_next (physicalCut w n T) (k + 1), ih, hn,
        physicalCut_arrival_next w (n + k + 1)]
      have hc : (physicalCut w n T (k + 1 + 1)).1 = (w (n + k + 1 + 1)).1 := by
        simp [physicalCut, Nat.add_assoc]
      rw [hc]
      ring

/-- Positivity of all actual future holds is retained by the cut; only the
first hold changes, and its positivity follows from the strict upper endpoint. -/
theorem physicalCut_holding_pos (w : ℕ → ℝ × S) (n : ℕ) (T : ℝ)
    (hhi : T < arrivalTime (n + 1) w)
    (hpos : ∀ k : ℕ, 0 < (w (k + 1)).1) :
    ∀ k : ℕ, 0 < (physicalCut w n T (k + 1)).1 := by
  intro k
  cases k with
  | zero => exact physicalCut_residual_pos w n T hhi
  | succ k =>
      simpa [physicalCut, Nat.add_assoc] using hpos (n + k + 1)

/-- The initial residual interval is exactly the portion of the original
n-th interval at or after the cut. -/
theorem physicalCut_initial_between (w : ℕ → ℝ × S) (n : ℕ) (T u : ℝ)
    (hhi : T < arrivalTime (n + 1) w) :
    (0 ≤ u ∧ u < arrivalTime 1 (physicalCut w n T)) ↔
      (T ≤ T + u ∧ T + u < arrivalTime (n + 1) w) := by
  rw [physicalCut_arrival w n T hhi 0]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Every subsequent between-arrival test, and therefore the segment index,
is the original source test translated by T and shifted by n. -/
theorem physicalCut_between (w : ℕ → ℝ × S) (n : ℕ) (T u : ℝ)
    (hhi : T < arrivalTime (n + 1) w) (k : ℕ) :
    (arrivalTime (k + 1) (physicalCut w n T) ≤ u ∧
      u < arrivalTime (k + 1 + 1) (physicalCut w n T)) ↔
    (arrivalTime (n + k + 1) w ≤ T + u ∧
      T + u < arrivalTime (n + k + 1 + 1) w) := by
  rw [physicalCut_arrival w n T hhi k, physicalCut_arrival w n T hhi (k + 1)]
  have hn : n + (k + 1) + 1 = n + k + 1 + 1 := by simp [Nat.add_assoc]
  rw [hn]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Unified segment correspondence, including the residual initial segment.
For u ≥ 0 this supplies exactly the two premises of the source theorem
`clockIndex_eq_of_between`, with future index k and source index n+k. -/
theorem physicalCut_source_segment (w : ℕ → ℝ × S) (n : ℕ) (T u : ℝ)
    (hlo : arrivalTime n w ≤ T) (hhi : T < arrivalTime (n + 1) w)
    (hu : 0 ≤ u) (k : ℕ) :
    (arrivalTime k (physicalCut w n T) ≤ u ∧
      u < arrivalTime (k + 1) (physicalCut w n T)) ↔
    (arrivalTime (n + k) w ≤ T + u ∧ T + u < arrivalTime (n + k + 1) w) := by
  cases k with
  | zero =>
      rw [physicalCut_arrival w n T hhi 0]
      have hz : arrivalTime 0 (physicalCut w n T) = 0 := by simp [arrivalTime]
      rw [hz]
      simp only [Nat.add_zero]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  | succ k =>
      simpa only [Nat.add_assoc] using physicalCut_between w n T u hhi k

/-- Successive physical cuts compose exactly. When k is the segment index of
the second cut inside the first suffix, the result is the direct cut at T+u
and original index n+k. This is a deterministic identity of the full future
holding-time/state sequences, before any distributional factorization. -/
theorem physicalCut_compose (w : ℕ → ℝ × S) (n k : ℕ) (T u : ℝ)
    (hhi : T < arrivalTime (n + 1) w) :
    physicalCut (physicalCut w n T) k u = physicalCut w (n + k) (T + u) := by
  funext j
  cases j with
  | zero =>
      simp only [physicalCut_zero, physicalCut_state]
  | succ j =>
      cases j with
      | zero =>
          change (arrivalTime (k + 1) (physicalCut w n T) - u,
            (physicalCut w n T (k + 1)).2) =
              (arrivalTime (n + k + 1) w - (T + u), (w (n + k + 1)).2)
          rw [physicalCut_state]
          rw [physicalCut_arrival w n T hhi k]
          congr 1
          ring
      | succ j =>
          change physicalCut w n T (k + j + 2) = w (n + k + j + 2)
          rw [physicalCut_later]
          congr 1
          omega

end

end CTMCHeredity20261019
