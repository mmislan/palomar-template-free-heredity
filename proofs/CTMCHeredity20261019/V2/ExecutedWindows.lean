module

public import proofs.CTMCHeredity20261019.V2.PhysicalSplice
public import proofs.CTMCHeredity20261019.V2.LedgerOffsets
public import proofs.HybridCTMCInfrastructure.TimedHistoryLaw

@[expose] public section

/-!
# Version 2: the observations actually executed by a physical splice

The source clockIndex and timedHistory are used throughout. A splice keeps
the left prefix through the cut, then executes exactly the positive right
coordinates. The right coordinate-zero sentinel is never executed. Thus a
generic marked state after the cut is piecewise: before the first new right
proposal, its old-mark component is still the left last mark.

The raw source fold has a stronger statement: it starts the right positive
marks at the actual left raw endpoint. Reusing LedgerOffsets then restores
the literal slotwise q/nd ledgers after either sourceResetQ or sourceResetAll.
These are deterministic single-splice identities. A joint all-block mission
observation theorem still requires induction on the actual operated-history
support; no such correspondence or stochastic premise is assumed here.
-/

namespace CTMCHeredity20261019.V2.ExecutedWindows

open HybridCTMC.Kernel Preorder PhysicalSplice
open scoped Classical
noncomputable section

variable {S : Type*}

/-- Every retained prefix arrival is the original arrival, including zero. -/
theorem prefixSplice_arrival_prefix (n : ℕ) (T : ℝ) (w v : Path S)
    (k : ℕ) (hk : k ≤ n) :
    arrivalTime k (prefixSplice n T (frestrictLe n w, v)) = arrivalTime k w := by
  unfold arrivalTime
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i < k := Finset.mem_range.mp hi
  have hin : i + 1 ≤ n := by omega
  rw [prefixSplice_prefix n T _ v (i + 1) hin]
  rfl

/-- Every positive right state is retained exactly. Only its first incoming
holding time may be changed by the elapsed left age. -/
theorem prefixSplice_state_positive (n : ℕ) (T : ℝ) (w v : Path S) (k : ℕ) :
    (prefixSplice n T (frestrictLe n w, v) (n + k + 1)).2 = (v (k + 1)).2 := by
  cases k with
  | zero => rw [Nat.add_zero, prefixSplice_first]
  | succ k =>
      rw [prefixSplice_later n T _ v (n + (k + 1) + 1) (by omega)]
      congr 2
      omega

/-- The post-cut arrivals are precisely the translated positive right
arrivals. The cut has no synthetic proposal at time T. -/
theorem prefixSplice_arrival_positive (n : ℕ) (T : ℝ) (w v : Path S)
    (hlo : arrivalTime n w ≤ T) (hv : 0 ≤ (v 1).1) (k : ℕ) :
    arrivalTime (n + k + 1) (prefixSplice n T (frestrictLe n w, v)) =
      T + arrivalTime (k + 1) v := by
  induction k with
  | zero =>
      rw [Nat.add_zero, physicalCut_arrival_next,
        prefixSplice_arrival_prefix n T w v n le_rfl,
        prefixSplice_first, cutPrefixArrival_frestrict]
      have hfirst : 0 ≤ T - arrivalTime n w + (v 1).1 := by linarith
      rw [max_eq_right hfirst]
      have hright : arrivalTime 1 v = (v 1).1 := by
        simp [arrivalTime, max_eq_right hv]
      rw [hright]
      ring
  | succ k ih =>
      have hindex : n + (k + 1) + 1 = (n + k + 1) + 1 := by omega
      rw [hindex, physicalCut_arrival_next, ih,
        prefixSplice_later n T _ v ((n + k + 1) + 1) (by omega)]
      have hsub : (n + k + 1) + 1 - n = (k + 1) + 1 := by omega
      rw [hsub, physicalCut_arrival_next v (k + 1)]
      ring

/-- On a chosen actual left arrival slice, the clock before and at the cut
is the original left clock. The right first hold is strictly positive. -/
theorem prefixSplice_clockIndex_before (n : ℕ) (T t : ℝ) (w v : Path S)
    (hlo : arrivalTime n w ≤ T) (hhi : T < arrivalTime (n + 1) w)
    (hv : 0 < (v 1).1) (ht : 0 ≤ t) (htT : t ≤ T) :
    clockIndex t (prefixSplice n T (frestrictLe n w, v)) = clockIndex t w := by
  have hs := clockIndex_segment ht w ⟨n + 1, htT.trans_lt hhi⟩
  have hin : clockIndex t w ≤ n := by
    by_contra h
    have hn : n + 1 ≤ clockIndex t w := by omega
    have ha := (arrivalTime_mono w) hn
    linarith [hs.1]
  apply clockIndex_eq_of_between
  · rw [prefixSplice_arrival_prefix n T w v _ hin]
    exact hs.1
  · by_cases he : clockIndex t w = n
    · have hpost := prefixSplice_arrival_positive n T w v hlo hv.le 0
      simp only [Nat.add_zero] at hpost
      rw [he, hpost]
      have hright : arrivalTime 1 v = (v 1).1 := by
        simp [arrivalTime, max_eq_right hv.le]
      rw [hright]
      linarith
    · have hnext : clockIndex t w + 1 ≤ n := by omega
      rw [prefixSplice_arrival_prefix n T w v _ hnext]
      exact hs.2

/-- On a chosen actual left arrival slice, every post-cut physical index is
the left executed index plus the right executed index. -/
theorem prefixSplice_clockIndex_after (n : ℕ) (T u : ℝ) (w v : Path S)
    (hlo : arrivalTime n w ≤ T) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    clockIndex (T + u) (prefixSplice n T (frestrictLe n w, v)) =
      n + clockIndex u v := by
  have hs := clockIndex_segment hu v hex
  apply clockIndex_eq_of_between
  · cases hj : clockIndex u v with
    | zero =>
        rw [Nat.add_zero, prefixSplice_arrival_prefix n T w v n le_rfl]
        linarith
    | succ j =>
        rw [← Nat.add_assoc,
          prefixSplice_arrival_positive n T w v hlo hv j]
        rw [hj] at hs
        linarith [hs.1]
  · rw [prefixSplice_arrival_positive n T w v hlo hv (clockIndex u v)]
    linarith [hs.2]

theorem splice_clockIndex_before (T t : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 < (v 1).1)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    clockIndex t (splice T (w, v)) = clockIndex t w := by
  have hs := clockIndex_segment hT w hw
  exact prefixSplice_clockIndex_before (clockIndex T w) T t w v hs.1 hs.2 hv ht htT

theorem splice_clockIndex_after (T u : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    clockIndex (T + u) (splice T (w, v)) = clockIndex T w + clockIndex u v := by
  exact prefixSplice_clockIndex_after (clockIndex T w) T u w v
    (clockIndex_segment hT w hw).1 hv hu hex

theorem splice_timedState_before (T t : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 < (v 1).1)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    timedState t (splice T (w, v)) = timedState t w := by
  have hi := splice_clockIndex_before T t w v hT hw hv ht htT
  have hs := clockIndex_segment ht w (by
    obtain ⟨k, hk⟩ := hw
    exact ⟨k, htT.trans_lt hk⟩)
  have hcut := clockIndex_segment hT w hw
  have hin : clockIndex t w ≤ clockIndex T w := by
    by_contra h
    have hn : clockIndex T w + 1 ≤ clockIndex t w := by omega
    have ha := (arrivalTime_mono w) hn
    linarith [hs.1, hcut.2]
  change (splice T (w, v) (clockIndex t (splice T (w, v)))).2 = _
  rw [hi]
  exact congrArg Prod.snd (prefixSplice_prefix (clockIndex T w) T _ v _ hin)

/-- A generic last-mark state keeps the actual left last mark until the
first new right proposal. In particular, a fresh none sentinel is not
mistaken for an executed mark at the cut. -/
theorem splice_timedState_after (T u : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    timedState (T + u) (splice T (w, v)) =
      if clockIndex u v = 0 then timedState T w else timedState u v := by
  change (splice T (w, v) (clockIndex (T + u) (splice T (w, v)))).2 = _
  rw [splice_clockIndex_after T u w v hT hw hv hu hex]
  cases hj : clockIndex u v with
  | zero =>
      simp only [Nat.add_zero, ite_true, timedState]
      exact congrArg Prod.snd (prefixSplice_prefix (clockIndex T w) T _ v _ le_rfl)
  | succ j =>
      simp only [Nat.succ_ne_zero, ite_false, timedState, hj]
      exact prefixSplice_state_positive (clockIndex T w) T w v j

/-- Projected physical states agree throughout the right phase whenever
the incoming right coordinate-zero projected state is the actual endpoint. -/
theorem splice_timed_observable_after {A : Type*} (f : S → A)
    (T u : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v)
    (hzero : f (v 0).2 = f (timedState T w)) :
    f (timedState (T + u) (splice T (w, v))) = f (timedState u v) := by
  rw [splice_timedState_after T u w v hT hw hv hu hex]
  by_cases hj : clockIndex u v = 0
  · simp only [hj, ite_true, timedState]
    exact hzero.symm
  · simp only [hj, ite_false]

/-- The positive-coordinate visited list excludes the sentinel. -/
def positiveStates (k : ℕ) (w : Path S) : List S :=
  List.ofFn (fun i : Fin k => (w (i.val + 1)).2)

@[simp] theorem positiveStates_zero (w : Path S) : positiveStates 0 w = [] := by
  simp [positiveStates]

theorem positiveStates_succ (k : ℕ) (w : Path S) :
    positiveStates (k + 1) w = positiveStates k w ++ [(w (k + 1)).2] := by
  simpa only [positiveStates, List.concat_eq_append, Fin.val_castSucc, Fin.val_last] using
    (List.ofFn_succ' (fun i : Fin (k + 1) => (w (i.val + 1)).2))

/-- This is exactly the tail of the source's existing statePrefix list. -/
theorem positiveStates_eq_statePrefix_tail (k : ℕ) (w : Path S) :
    positiveStates k w = (statePrefix k w).tail := by
  rw [statePrefix, List.ofFn_succ]
  rfl

theorem prefixSplice_positiveStates_prefix (n : ℕ) (T : ℝ) (w v : Path S)
    (k : ℕ) (hk : k ≤ n) :
    positiveStates k (prefixSplice n T (frestrictLe n w, v)) = positiveStates k w := by
  unfold positiveStates
  congr 1
  funext i
  have hin : i.val + 1 ≤ n := by omega
  rw [prefixSplice_prefix n T _ v (i.val + 1) hin]
  rfl

/-- Exact concatenation of the executed positive-coordinate lists. -/
theorem prefixSplice_positiveStates_append (n : ℕ) (T : ℝ) (w v : Path S) (k : ℕ) :
    positiveStates (n + k) (prefixSplice n T (frestrictLe n w, v)) =
      positiveStates n w ++ positiveStates k v := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, positiveStates_zero, List.append_nil]
      exact prefixSplice_positiveStates_prefix n T w v n le_rfl
  | succ k ih =>
      rw [Nat.add_succ, positiveStates_succ, ih, positiveStates_succ,
        prefixSplice_state_positive]
      exact List.append_assoc _ _ _

/-- Source timedHistory tails are precisely the executed positive states. -/
theorem timedHistory_tail_eq (t : ℝ) (w : Path S) :
    (timedHistory t w).tail = positiveStates (clockIndex t w) w :=
  (positiveStates_eq_statePrefix_tail _ _).symm

theorem splice_timedHistory_tail_before (T t : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 < (v 1).1)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    (timedHistory t (splice T (w, v))).tail = (timedHistory t w).tail := by
  rw [timedHistory_tail_eq, timedHistory_tail_eq,
    splice_clockIndex_before T t w v hT hw hv ht htT]
  have hs := clockIndex_segment ht w (by
    obtain ⟨k, hk⟩ := hw
    exact ⟨k, htT.trans_lt hk⟩)
  have hcut := clockIndex_segment hT w hw
  have hin : clockIndex t w ≤ clockIndex T w := by
    by_contra h
    have hn : clockIndex T w + 1 ≤ clockIndex t w := by omega
    have ha := (arrivalTime_mono w) hn
    linarith [hs.1, hcut.2]
  exact prefixSplice_positiveStates_prefix (clockIndex T w) T w v _ hin

theorem splice_timedHistory_tail_after (T u : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    (timedHistory (T + u) (splice T (w, v))).tail =
      (timedHistory T w).tail ++ (timedHistory u v).tail := by
  rw [timedHistory_tail_eq, timedHistory_tail_eq, timedHistory_tail_eq,
    splice_clockIndex_after T u w v hT hw hv hu hex]
  exact prefixSplice_positiveStates_append (clockIndex T w) T w v (clockIndex u v)

/-- Every list-valued executed mark observation follows the same exact
concatenation, including idle and state-null proposal labels. -/
theorem splice_executed_marks {A : Type*} (mark : S → A)
    (T u : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    ((timedHistory (T + u) (splice T (w, v))).tail).map mark =
      ((timedHistory T w).tail).map mark ++ ((timedHistory u v).tail).map mark := by
  rw [splice_timedHistory_tail_after T u w v hT hw hv hu hex, List.map_append]

/-- Counting a selected proposal predicate is additive on the executed
windows, with no contribution from either coordinate-zero sentinel. -/
theorem splice_executed_countP (P : S → Bool)
    (T u : ℝ) (w v : Path S) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    ((timedHistory (T + u) (splice T (w, v))).tail).countP P =
      ((timedHistory T w).tail).countP P + ((timedHistory u v).tail).countP P := by
  rw [splice_timedHistory_tail_after T u w v hT hw hv hu hex, List.countP_append]

section RawSource

open FunctionalCapacity CF3Marked CF3RawPathLift LedgerOffsets

/-- The complete source fold through a retained prefix is literally unchanged. -/
theorem prefixSplice_rawAt_prefix (p : Par) (x : SourceState p)
    (n : ℕ) (T : ℝ) (w v : MarkedPath p) (k : ℕ) (hk : k ≤ n) :
    rawAt p x (prefixSplice n T (frestrictLe n w, v)) k = rawAt p x w k := by
  revert hk
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [rawAt_succ, rawAt_succ, ih (by omega),
        prefixSplice_prefix n T _ v (k + 1) hk]
      rfl

/-- Fold the right positive marks from the actual raw left endpoint, without
an operation at coordinate zero and without assuming finite ledger caps. -/
theorem prefixSplice_rawAt_after (p : Par) (x : SourceState p)
    (n : ℕ) (T : ℝ) (w v : MarkedPath p) (k : ℕ) :
    rawAt p x (prefixSplice n T (frestrictLe n w, v)) (n + k) =
      rawAt p (rawAt p x w n) v k := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, rawAt_zero]
      exact prefixSplice_rawAt_prefix p x n T w v n le_rfl
  | succ k ih =>
      rw [Nat.add_succ, rawAt_succ, rawAt_succ, ih,
        prefixSplice_state_positive]

theorem splice_raw_timedState_before (p : Par) (x : SourceState p)
    (T t : ℝ) (w v : MarkedPath p) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 < (v 1).1)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    timedState t (rawSequence p x (splice T (w, v))) =
      timedState t (rawSequence p x w) := by
  change rawAt p x (splice T (w, v)) (clockIndex t (splice T (w, v))) =
    rawAt p x w (clockIndex t w)
  rw [splice_clockIndex_before T t w v hT hw hv ht htT]
  have hs := clockIndex_segment ht w (by
    obtain ⟨k, hk⟩ := hw
    exact ⟨k, htT.trans_lt hk⟩)
  have hcut := clockIndex_segment hT w hw
  have hin : clockIndex t w ≤ clockIndex T w := by
    by_contra h
    have hn : clockIndex T w + 1 ≤ clockIndex t w := by omega
    have ha := (arrivalTime_mono w) hn
    linarith [hs.1, hcut.2]
  exact prefixSplice_rawAt_prefix p x (clockIndex T w) T w v _ hin

theorem splice_raw_timedState_after (p : Par) (x : SourceState p)
    (T u : ℝ) (w v : MarkedPath p) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    timedState (T + u) (rawSequence p x (splice T (w, v))) =
      timedState u (rawSequence p (timedState T (rawSequence p x w)) v) := by
  change rawAt p x (splice T (w, v)) (clockIndex (T + u) (splice T (w, v))) =
    rawAt p (rawAt p x w (clockIndex T w)) v (clockIndex u v)
  rw [splice_clockIndex_after T u w v hT hw hv hu hex]
  exact prefixSplice_rawAt_after p x (clockIndex T w) T w v (clockIndex u v)

/-- Reusing the proved external-ledger adapter restores precisely the
slotwise q credits discarded by a service reset. Division ledgers persist. -/
theorem splice_raw_resetQ_restore (p : Par) (x : SourceState p)
    (T u : ℝ) (w v : MarkedPath p) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    timedState (T + u) (rawSequence p x (splice T (w, v))) =
      addLedgers p
        (timedState u (rawSequence p (sourceResetQ (timedState T (rawSequence p x w))) v))
        (qLedger (timedState T (rawSequence p x w))) (fun _ => 0) := by
  rw [splice_raw_timedState_after p x T u w v hT hw hv hu hex,
    rawSequence_resetQ_restore, offsetSequence_timedState]

/-- A phase reset additionally discards local nd. Its exact external offset
is restored too; neither core counts nor fuel are replenished. -/
theorem splice_raw_resetAll_restore (p : Par) (x : SourceState p)
    (T u : ℝ) (w v : MarkedPath p) (hT : 0 ≤ T)
    (hw : ∃ k : ℕ, T < arrivalTime k w) (hv : 0 ≤ (v 1).1)
    (hu : 0 ≤ u) (hex : ∃ k : ℕ, u < arrivalTime k v) :
    timedState (T + u) (rawSequence p x (splice T (w, v))) =
      addLedgers p
        (timedState u (rawSequence p (sourceResetAll (timedState T (rawSequence p x w))) v))
        (qLedger (timedState T (rawSequence p x w)))
        (dLedger (timedState T (rawSequence p x w))) := by
  rw [splice_raw_timedState_after p x T u w v hT hw hv hu hex,
    rawSequence_resetAll_restore, offsetSequence_timedState]

end RawSource

end
end CTMCHeredity20261019.V2.ExecutedWindows
