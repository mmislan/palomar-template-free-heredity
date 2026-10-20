module

public import proofs.CTMCHeredity20261019.V2.ExecutedWindows
public import proofs.CTMCHeredity20261019.V2.OperatedObservations
public import proofs.CTMCHeredity20261019.V2.PhysicalOperated
public import proofs.CTMCHeredity20261019.V2.LedgerOffsets

@[expose] public section

/-!
# Version 3: all-window literal raw states of a completed operated history

The actual source fold of the stitched positive marks agrees, simultaneously
on every closed block window, with the recorded local raw state plus fixed
spatial-slot credit offsets. An ordinary service boundary clears local q and
preserves nd. Thus nd endpoints are never summed. Initial q is arbitrary:
the first recorded endpoint enters the prefix q offset exactly once.

These deterministic statements require only the already defined compatible,
faithful and clock support predicates. No law, expectation or observation
correspondence is a premise. Their actual-law AE specialization is separate.
Optional fixed initial q/nd offsets use the compiled source covariance theorem.
Counts and fuel are unchanged; a fresh sentinel is never an operation.
-/

namespace CTMCHeredity20261019.V3.WindowIdentity

open FunctionalCapacity HybridCTMC.Kernel
open CTMCHeredity20261019.CF3Marked CTMCHeredity20261019.CF3RawPathLift
open CTMCHeredity20261019.V2
open NoBoundaryArrival LedgerOffsets ExecutedWindows
open scoped BigOperators Classical
noncomputable section

/-- The sum of prior executed local endpoint q ledgers, at fixed population
slots. For b=0 the offset is zero, even when the initial q ledger is nonzero. -/
def qOffset (p : Par) (T : ℝ) (n : ℕ) (h : RawOperated.History p n) (b : ℕ) :
    Fin p.M → Fin p.c → ℕ := fun i j =>
  ∑ k : Fin n, if k.val < b then ((timedState T (h.1 k).2) i).q j else 0

@[simp] theorem qOffset_zero (p : Par) (T : ℝ) (n : ℕ) (h : RawOperated.History p n) :
    qOffset p T n h 0 = (fun _ _ => 0) := by
  funext i j
  simp [qOffset]

/-- Prefix offsets split into the tail's prefix offset and the first executed
endpoint. The order is convenient for the source's additive covariance. -/
theorem qOffset_succ_tail (p : Par) (T : ℝ) (n : ℕ)
    (h : RawOperated.History p (n + 1)) (b : ℕ) :
    qOffset p T (n + 1) h (b + 1) = fun i j =>
      qOffset p T n (Operated.tail h) b i j + qLedger (timedState T (h.1 0).2) i j := by
  funext i j
  unfold qOffset
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true]
  have hsum :
      (∑ k : Fin n, if k.succ.val < b + 1 then
        ((timedState T (h.1 k.succ).2) i).q j else 0) =
      ∑ k : Fin n, if k.val < b then
        ((timedState T ((Operated.tail h).1 k).2) i).q j else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    have hk : (k.succ.val < b + 1) ↔ k.val < b := by
      simp only [Fin.val_succ]
      omega
    simp only [hk, Operated.tail]
  rw [hsum]
  exact Nat.add_comm _ _

/-- Faithfulness and the actual recorded starting state identify the complete
source fold. No physical-core correspondence is assumed for arbitrary pairs. -/
theorem faithful_raw_eq_of_start (p : Par) (s : RawOperated.Segment p)
    (x : SourceState p) (hf : RawOperated.faithful p s) (hs : s.2 0 = (0, x)) :
    s.2 = rawSequence p x s.1 := by
  obtain ⟨y, hy, he⟩ := hf
  have hyx : y = x := congrArg Prod.snd (hy.symm.trans hs)
  subst y
  exact he

/-- A single deterministic support statement gives every closed-window state
identity and the returned terminal-state identity together. nd is preserved
through ordinary q resets and has no prefix-sum offset. -/
theorem stitch_raw_windows_and_terminal (p : Par) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (x : SourceState p) (h : RawOperated.History p n) (v : MarkedPath p)
    (hc : RawOperated.compatible p T n x h)
    (hf : RawOperated.allSegments (RawOperated.faithful p) h)
    (hh : ∀ b : Fin n, ClockBoundarySupport ∅ (h.1 b).1)
    (hv : ClockBoundarySupport ∅ v) :
    (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      timedState ((b.val : ℝ) * T + t)
          (rawSequence p x (PhysicalOperated.stitch p T n (h, v))) =
        addLedgers p (timedState t (h.1 b).2) (qOffset p T n h b.val) (fun _ => 0)) ∧
      timedState ((n : ℝ) * T)
          (rawSequence p x (PhysicalOperated.stitch p T n (h, v))) =
        addLedgers p h.2 (qOffset p T n h n) (fun _ => 0) := by
  induction n generalizing x with
  | zero =>
      constructor
      · intro b
        exact Fin.elim0 b
      · have hfirst : 0 < arrivalTime 1 v := by
          simpa [arrivalTime, max_eq_right (hv.1 0).le] using hv.1 0
        have hi := clockIndex_eq_of_between v 0 (by simp [arrivalTime]) hfirst
        have he : timedState 0 (rawSequence p x v) = x := by
          change rawAt p x v (clockIndex 0 v) = x
          rw [hi, rawAt_zero]
        have hx : h.2 = x := hc
        simpa only [Nat.cast_zero, zero_mul, PhysicalOperated.stitch,
          qOffset_zero, addLedgers_zero, hx] using he
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
      have hcut (u : ℝ) (hu : 0 ≤ u) :
          timedState (T + u) (rawSequence p x (PhysicalSplice.splice T (s.1, r))) =
            addLedgers p
              (timedState u (rawSequence p (RawOperated.nextState p T s) r))
              (qLedger (timedState T s.2)) (fun _ => 0) := by
        have he := splice_raw_resetQ_restore p x T u s.1 r hT ((hh 0).2.1 T)
          (hr.1 0).le hu (hr.2.1 u)
        rw [hend] at he
        exact he
      constructor
      · intro b t ht htT
        refine Fin.cases ?_ (fun b => ?_) b
        · simp only [Fin.val_zero, Nat.cast_zero]
          change timedState ((0 : ℝ) * T + t)
              (rawSequence p x (PhysicalSplice.splice T (s.1, r))) =
            addLedgers p (timedState t s.2) (qOffset p T (n + 1) h 0) (fun _ => 0)
          rw [zero_mul, zero_add, qOffset_zero, addLedgers_zero]
          calc
            _ = timedState t (rawSequence p x s.1) :=
              splice_raw_timedState_before p x T t s.1 r hT ((hh 0).2.1 T)
                (hr.1 0) ht htT
            _ = _ := congrArg (timedState t) hraw.symm
        · have hu : 0 ≤ (b.val : ℝ) * T + t :=
            add_nonneg (mul_nonneg (Nat.cast_nonneg b.val) hT) ht
          have htime : (b.succ.val : ℝ) * T + t = T + ((b.val : ℝ) * T + t) := by
            simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
            ring
          change timedState ((b.succ.val : ℝ) * T + t)
              (rawSequence p x (PhysicalSplice.splice T (s.1, r))) =
            addLedgers p (timedState t (h.1 b.succ).2)
              (qOffset p T (n + 1) h b.succ.val) (fun _ => 0)
          rw [htime, hcut _ hu, hit.1 b t ht htT, addLedgers_add]
          simp only [Fin.val_succ, qOffset_succ_tail, Operated.tail, Nat.add_zero, s]
      · have htime : ((n + 1 : ℕ) : ℝ) * T = T + (n : ℝ) * T := by
          push_cast
          ring
        change timedState (((n + 1 : ℕ) : ℝ) * T)
            (rawSequence p x (PhysicalSplice.splice T (s.1, r))) =
          addLedgers p h.2 (qOffset p T (n + 1) h (n + 1)) (fun _ => 0)
        rw [htime, hcut _ (mul_nonneg (Nat.cast_nonneg n) hT), hit.2, addLedgers_add]
        simp only [qOffset_succ_tail, Operated.tail, Nat.add_zero, s]

theorem stitch_raw_window (p : Par) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (x : SourceState p) (h : RawOperated.History p n) (v : MarkedPath p)
    (hc : RawOperated.compatible p T n x h)
    (hf : RawOperated.allSegments (RawOperated.faithful p) h)
    (hh : ∀ b : Fin n, ClockBoundarySupport ∅ (h.1 b).1)
    (hv : ClockBoundarySupport ∅ v) (b : Fin n) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    timedState ((b.val : ℝ) * T + t)
        (rawSequence p x (PhysicalOperated.stitch p T n (h, v))) =
      addLedgers p (timedState t (h.1 b).2) (qOffset p T n h b.val) (fun _ => 0) :=
  (stitch_raw_windows_and_terminal p T hT n x h v hc hf hh hv).1 b t ht htT

theorem stitch_raw_terminal (p : Par) (T : ℝ) (hT : 0 ≤ T) (n : ℕ)
    (x : SourceState p) (h : RawOperated.History p n) (v : MarkedPath p)
    (hc : RawOperated.compatible p T n x h)
    (hf : RawOperated.allSegments (RawOperated.faithful p) h)
    (hh : ∀ b : Fin n, ClockBoundarySupport ∅ (h.1 b).1)
    (hv : ClockBoundarySupport ∅ v) :
    timedState ((n : ℝ) * T)
        (rawSequence p x (PhysicalOperated.stitch p T n (h, v))) =
      addLedgers p h.2 (qOffset p T n h n) (fun _ => 0) :=
  (stitch_raw_windows_and_terminal p T hT n x h v hc hf hh hv).2

/-- Fixed initial external ledger offsets are carried through the same
sampled complete marks. The division offset stays constant, including when
it records divisions from a prior phase; it is never an endpoint sum. -/
theorem stitch_raw_windows_and_terminal_addLedgers (p : Par) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (x : SourceState p) (h : RawOperated.History p n) (v : MarkedPath p)
    (hc : RawOperated.compatible p T n x h)
    (hf : RawOperated.allSegments (RawOperated.faithful p) h)
    (hh : ∀ b : Fin n, ClockBoundarySupport ∅ (h.1 b).1)
    (hv : ClockBoundarySupport ∅ v)
    (oq : Fin p.M → Fin p.c → ℕ) (ond : Fin p.M → ℕ) :
    (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      timedState ((b.val : ℝ) * T + t)
          (rawSequence p (addLedgers p x oq ond) (PhysicalOperated.stitch p T n (h, v))) =
        addLedgers p (timedState t (h.1 b).2)
          (fun i j => qOffset p T n h b.val i j + oq i j) ond) ∧
      timedState ((n : ℝ) * T)
          (rawSequence p (addLedgers p x oq ond) (PhysicalOperated.stitch p T n (h, v))) =
        addLedgers p h.2 (fun i j => qOffset p T n h n i j + oq i j) ond := by
  have he := stitch_raw_windows_and_terminal p T hT n x h v hc hf hh hv
  constructor
  · intro b t ht htT
    rw [rawSequence_timed_addLedgers, he.1 b t ht htT, addLedgers_add]
    simp only [Nat.zero_add]
  · rw [rawSequence_timed_addLedgers, he.2, addLedgers_add]
    simp only [Nat.zero_add]

end
end CTMCHeredity20261019.V3.WindowIdentity
