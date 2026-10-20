module

public import proofs.CTMCHeredity20261019.CF3RawPathLift
public import proofs.CTMCHeredity20261019.MissionQuotient

@[expose] public section

/-!
# Slotwise external ledger offsets for the literal CF3 source

Every complete source operation commutes with fixed additive offsets in the
natural-valued q and nd ledgers. The offsets stay at population slots: a
division's victim retains its own external ledgers. The result covers every
label, including idle, state-null operations, and zero-weight self-victim
labels; it does not reinterpret these labels as positive-rate operations.

The deterministic raw fold consequently reconstructs cumulative q/nd from a
locally reset fold plus stored prefix offsets. Counts, fuel, holds, arrival
times, and physical indices are unchanged. These are external bookkeeping
identities, not a stock/fuel conservation theorem or a stochastic count tail.
No accepted-feed, seed, precursor, victim-cost or gross-stock ledger is added.
-/

namespace CTMCHeredity20261019.V2.LedgerOffsets

open FunctionalCapacity HybridCTMC.Kernel CF3Marked CF3RawPathLift
open scoped Classical
noncomputable section

private theorem site_ext {c N : ℕ} {s t : Site c N}
    (ha : s.a = t.a) (hR : s.R = t.R) (hq : s.q = t.q) (hd : s.nd = t.nd) : s = t := by
  cases s
  cases t
  cases ha
  cases hR
  cases hq
  cases hd
  rfl

def addSite {c N : ℕ} (s : Site c N) (oq : Fin c → ℕ) (ond : ℕ) : Site c N :=
  { s with q := fun j => s.q j + oq j, nd := s.nd + ond }

/-- Add fixed natural-valued external offsets at the actual population slots. -/
def addLedgers (p : Par) (x : SourceState p)
    (oq : Fin p.M → Fin p.c → ℕ) (ond : Fin p.M → ℕ) : SourceState p :=
  fun i => addSite (x i) (oq i) (ond i)

def qLedger {p : Par} (x : SourceState p) (i : Fin p.M) (j : Fin p.c) : ℕ := (x i).q j
def dLedger {p : Par} (x : SourceState p) (i : Fin p.M) : ℕ := (x i).nd

@[simp] theorem addLedgers_counts (p : Par) (x : SourceState p) (oq ond) (i : Fin p.M) :
    (addLedgers p x oq ond i).a = (x i).a := rfl

@[simp] theorem addLedgers_fuel (p : Par) (x : SourceState p) (oq ond) (i : Fin p.M) :
    (addLedgers p x oq ond i).R = (x i).R := rfl

@[simp] theorem addLedgers_q (p : Par) (x : SourceState p) (oq ond)
    (i : Fin p.M) (j : Fin p.c) :
    (addLedgers p x oq ond i).q j = (x i).q j + oq i j := rfl

@[simp] theorem addLedgers_nd (p : Par) (x : SourceState p) (oq ond) (i : Fin p.M) :
    (addLedgers p x oq ond i).nd = (x i).nd + ond i := rfl

@[simp] theorem addLedgers_core (p : Par) (x : SourceState p) (oq ond) :
    coreProject (addLedgers p x oq ond) = coreProject x := rfl

@[simp] theorem addLedgers_zero (p : Par) (x : SourceState p) :
    addLedgers p x (fun _ _ => 0) (fun _ => 0) = x := by
  funext i
  apply site_ext <;> simp [addLedgers, addSite]

theorem addLedgers_add (p : Par) (x : SourceState p) (oq₁ ond₁ oq₂ ond₂) :
    addLedgers p (addLedgers p x oq₁ ond₁) oq₂ ond₂ =
      addLedgers p x (fun i j => oq₁ i j + oq₂ i j) (fun i => ond₁ i + ond₂ i) := by
  funext i
  apply site_ext <;> simp [addLedgers, addSite, Nat.add_assoc]

theorem addLedgers_update (p : Par) (x : SourceState p) (oq ond)
    (i : Fin p.M) (s : Site p.c p.N) :
    addLedgers p (Function.update x i s) oq ond =
      Function.update (addLedgers p x oq ond) i (addSite s (oq i) (ond i)) := by
  funext v
  by_cases hv : v = i
  · subst v
    simp [addLedgers]
  · simp [addLedgers, hv]

private theorem q_update_offset {c : ℕ} (q o : Fin c → ℕ) (j : Fin c) :
    Function.update (fun l => q l + o l) j (q j + o j + 1) =
      fun l => Function.update q j (q j + 1) l + o l := by
  funext l
  by_cases hl : l = j
  · subst l
    simp only [Function.update_self]
    omega
  · simp [hl]

/-- Every chemistry update, including the credited ordinary job. -/
theorem chemical_addSite (p : Par) (s : Site p.c p.N) (oq ond) (k : Chem p.c) :
    (cf3 p).tc (addSite s oq ond) k = addSite ((cf3 p).tc s k) oq ond := by
  cases k with
  | inl a =>
      rcases a with ⟨t, j⟩
      simp only [cf3]
      split_ifs <;> apply site_ext <;> try rfl
      exact q_update_offset s.q oq j
  | inr b => cases b <;> rfl

/-- Both division initiator updates, with actual source credit and nd changes. -/
theorem trigger_addSite (p : Par) (s : Site p.c p.N) (oq ond)
    (k : Option (Fin p.c)) :
    (cf3 p).td (addSite s oq ond) k = addSite ((cf3 p).td s k) oq ond := by
  cases k with
  | none =>
      apply site_ext <;> try rfl
      change s.nd + ond + 1 = s.nd + 1 + ond
      omega
  | some j =>
      apply site_ext <;> try rfl
      · exact q_update_offset s.q oq j
      · change s.nd + ond + 1 = s.nd + 1 + ond
        omega

theorem first_daughter_addSite (p : Par) (s : Site p.c p.N) (oq ond)
    (o : Split p.c p.N) :
    (cf3 p).d1 (addSite s oq ond) o = addSite ((cf3 p).d1 s o) oq ond := rfl

theorem second_daughter_addSite (p : Par) (s : Site p.c p.N) (oq ond)
    (o : Split p.c p.N) :
    (cf3 p).d2 (addSite s oq ond) o = addSite ((cf3 p).d2 s o) oq ond := rfl

/-- The victim keeps its own offsets; parent/daughter offsets are not copied
into the victim's external ledgers. -/
theorem merge_addSite (p : Par) (v d : Site p.c p.N) (vq vnd dq dnd) :
    (cf3 p).merge (addSite v vq vnd) (addSite d dq dnd) =
      addSite ((cf3 p).merge v d) vq vnd := rfl

/-- This equality includes self-victim labels, even though they have zero
actual source weight. No distinct-victim premise hides a deterministic case. -/
theorem divisionNext_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (i : Fin p.M) (k : Option (Fin p.c)) (o : Split p.c p.N) (v : Fin p.M) :
    divisionNext p (addLedgers p x oq ond) i k o v =
      addLedgers p (divisionNext p x i k o v) oq ond := by
  funext z
  by_cases hzv : z = v
  · subst z
    simp only [divisionNext, addLedgers, Function.update_self]
    rw [trigger_addSite, second_daughter_addSite, merge_addSite]
  · by_cases hzi : z = i
    · subst z
      simp only [divisionNext, addLedgers, Function.update_of_ne hzv, Function.update_self]
      rw [trigger_addSite, first_daughter_addSite]
    · simp [divisionNext, addLedgers, hzv, hzi]

/-- Exact full source-operation covariance for every complete mark. -/
theorem sourceNext_addLedgers (p : Par) (x : SourceState p) (oq ond) (r : Mark p) :
    sourceNext p (addLedgers p x oq ond) r = addLedgers p (sourceNext p x r) oq ond := by
  cases r with
  | inl a =>
      rcases a with ⟨i, k⟩
      change Function.update (addLedgers p x oq ond) i
        ((cf3 p).tc (addSite (x i) (oq i) (ond i)) k) =
        addLedgers p (Function.update x i ((cf3 p).tc (x i) k)) oq ond
      rw [chemical_addSite, addLedgers_update]
  | inr a =>
      rcases a with ⟨i, k, o, v⟩
      exact divisionNext_addLedgers p x oq ond i k o v

theorem sourceProposalNext_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (r : Option (Mark p)) :
    sourceProposalNext p (addLedgers p x oq ond) r =
      addLedgers p (sourceProposalNext p x r) oq ond := by
  cases r with
  | none => rfl
  | some r => exact sourceNext_addLedgers p x oq ond r

/-- All complete physical intensities are independent of these bookkeeping
offsets. This is an identity of literal source formulas, not a law premise. -/
theorem sourceIntensity_addLedgers (p : Par) (x : SourceState p) (oq ond) (r : Mark p) :
    sourceIntensity p (addLedgers p x oq ond) r = sourceIntensity p x r := by
  rw [CF3MarkedKernel.sourceIntensity_lump p (addLedgers p x oq ond), addLedgers_core]
  exact (CF3MarkedKernel.sourceIntensity_lump p x r).symm

/-- Covariance of the actual natural-counter fold at every proposal index. -/
theorem rawAt_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (w : MarkedPath p) (n : ℕ) :
    rawAt p (addLedgers p x oq ond) w n = addLedgers p (rawAt p x w n) oq ond := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rawAt_succ, rawAt_succ, ih, sourceProposalNext_addLedgers]

theorem rawAt_q_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (w : MarkedPath p) (n : ℕ) (i : Fin p.M) (j : Fin p.c) :
    (rawAt p (addLedgers p x oq ond) w n i).q j =
      (rawAt p x w n i).q j + oq i j := by
  rw [rawAt_addLedgers]
  rfl

theorem rawAt_nd_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (w : MarkedPath p) (n : ℕ) (i : Fin p.M) :
    (rawAt p (addLedgers p x oq ond) w n i).nd = (rawAt p x w n i).nd + ond i := by
  rw [rawAt_addLedgers]
  rfl

theorem rawAt_core_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (w : MarkedPath p) (n : ℕ) :
    coreProject (rawAt p (addLedgers p x oq ond) w n) = coreProject (rawAt p x w n) := by
  rw [rawAt_addLedgers, addLedgers_core]

def offsetSequence (p : Par) (oq : Fin p.M → Fin p.c → ℕ) (ond : Fin p.M → ℕ)
    (w : ℕ → ℝ × SourceState p) : ℕ → ℝ × SourceState p :=
  fun n => ((w n).1, addLedgers p (w n).2 oq ond)

theorem rawSequence_addLedgers (p : Par) (x : SourceState p) (oq ond) (w : MarkedPath p) :
    rawSequence p (addLedgers p x oq ond) w = offsetSequence p oq ond (rawSequence p x w) := by
  funext n
  exact Prod.ext rfl (rawAt_addLedgers p x oq ond w n)

/-- Every positive-index actual hold, as well as the zero sentinel hold, is
the same sampled value before and after a ledger offset. -/
theorem rawSequence_offset_hold (p : Par) (x : SourceState p) (oq ond)
    (w : MarkedPath p) (n : ℕ) :
    (rawSequence p (addLedgers p x oq ond) w n).1 = (rawSequence p x w n).1 := rfl

@[simp] theorem offsetSequence_hold (p : Par) (oq ond) (w : ℕ → ℝ × SourceState p) (n : ℕ) :
    (offsetSequence p oq ond w n).1 = (w n).1 := rfl

@[simp] theorem offsetSequence_arrivalTime (p : Par) (oq ond)
    (w : ℕ → ℝ × SourceState p) (n : ℕ) :
    arrivalTime n (offsetSequence p oq ond w) = arrivalTime n w := rfl

@[simp] theorem offsetSequence_clockIndex (p : Par) (oq ond)
    (w : ℕ → ℝ × SourceState p) (T : ℝ) :
    clockIndex T (offsetSequence p oq ond w) = clockIndex T w := rfl

theorem offsetSequence_timedState (p : Par) (oq ond) (w : ℕ → ℝ × SourceState p) (T : ℝ) :
    timedState T (offsetSequence p oq ond w) = addLedgers p (timedState T w) oq ond := rfl

theorem rawSequence_timed_addLedgers (p : Par) (x : SourceState p) (oq ond)
    (w : MarkedPath p) (T : ℝ) :
    timedState T (rawSequence p (addLedgers p x oq ond) w) =
      addLedgers p (timedState T (rawSequence p x w)) oq ond := by
  rw [rawSequence_addLedgers, offsetSequence_timedState]

/-- Output reset strips q offsets while preserving division offsets. -/
theorem resetQ_addLedgers (p : Par) (x : SourceState p) (oq ond) :
    sourceResetQ (addLedgers p x oq ond) =
      addLedgers p (sourceResetQ x) (fun _ _ => 0) ond := by
  funext i
  apply site_ext <;> simp [sourceResetQ, addLedgers, addSite]

/-- The phase reset strips both external offsets, without changing the core. -/
theorem resetAll_addLedgers (p : Par) (x : SourceState p) (oq ond) :
    sourceResetAll (addLedgers p x oq ond) = sourceResetAll x := rfl

theorem resetQ_restore (p : Par) (x : SourceState p) :
    addLedgers p (sourceResetQ x) (qLedger x) (fun _ => 0) = x := by
  funext i
  apply site_ext <;> simp [sourceResetQ, addLedgers, addSite, qLedger]

theorem resetAll_restore (p : Par) (x : SourceState p) :
    addLedgers p (sourceResetAll x) (qLedger x) (dLedger x) = x := by
  funext i
  apply site_ext <;> simp [sourceResetAll, addLedgers, addSite, qLedger, dLedger]

/-- A complete raw continuation from stored cumulative counters is exactly the
same marked fold as its q-reset continuation plus the stored prefix credits. -/
theorem rawAt_resetQ_restore (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) :
    rawAt p x w n =
      addLedgers p (rawAt p (sourceResetQ x) w n) (qLedger x) (fun _ => 0) := by
  rw [← rawAt_addLedgers, resetQ_restore]

theorem rawAt_resetAll_restore (p : Par) (x : SourceState p) (w : MarkedPath p) (n : ℕ) :
    rawAt p x w n =
      addLedgers p (rawAt p (sourceResetAll x) w n) (qLedger x) (dLedger x) := by
  rw [← rawAt_addLedgers, resetAll_restore]

theorem rawSequence_resetQ_restore (p : Par) (x : SourceState p) (w : MarkedPath p) :
    rawSequence p x w =
      offsetSequence p (qLedger x) (fun _ => 0) (rawSequence p (sourceResetQ x) w) := by
  rw [← rawSequence_addLedgers, resetQ_restore]

theorem rawSequence_resetAll_restore (p : Par) (x : SourceState p) (w : MarkedPath p) :
    rawSequence p x w =
      offsetSequence p (qLedger x) (dLedger x) (rawSequence p (sourceResetAll x) w) := by
  rw [← rawSequence_addLedgers, resetAll_restore]

/-- The interface deliberately says prefix plus local; local reset q is not
silently identified with the cumulative source credit observation. -/
theorem raw_credit_resetQ (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) (i : Fin p.M) (j : Fin p.c) :
    (rawAt p x w n i).q j = (rawAt p (sourceResetQ x) w n i).q j + (x i).q j := by
  rw [rawAt_resetQ_restore]
  rfl

theorem raw_credit_resetAll (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) (i : Fin p.M) (j : Fin p.c) :
    (rawAt p x w n i).q j = (rawAt p (sourceResetAll x) w n i).q j + (x i).q j := by
  rw [rawAt_resetAll_restore]
  rfl

theorem raw_divisions_resetAll (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) (i : Fin p.M) :
    (rawAt p x w n i).nd = (rawAt p (sourceResetAll x) w n i).nd + (x i).nd := by
  rw [rawAt_resetAll_restore]
  rfl

theorem raw_divisions_resetQ (p : Par) (x : SourceState p) (w : MarkedPath p)
    (n : ℕ) (i : Fin p.M) :
    (rawAt p x w n i).nd = (rawAt p (sourceResetQ x) w n i).nd := by
  rw [rawAt_resetQ_restore]
  rfl

theorem timed_credit_resetQ (p : Par) (x : SourceState p) (w : MarkedPath p)
    (T : ℝ) (i : Fin p.M) (j : Fin p.c) :
    ((timedState T (rawSequence p x w)) i).q j =
      ((timedState T (rawSequence p (sourceResetQ x) w)) i).q j + (x i).q j := by
  rw [rawSequence_resetQ_restore, offsetSequence_timedState]
  rfl

theorem timed_divisions_resetQ (p : Par) (x : SourceState p) (w : MarkedPath p)
    (T : ℝ) (i : Fin p.M) :
    ((timedState T (rawSequence p x w)) i).nd =
      ((timedState T (rawSequence p (sourceResetQ x) w)) i).nd := by
  rw [rawSequence_resetQ_restore, offsetSequence_timedState]
  rfl

theorem timed_credit_resetAll (p : Par) (x : SourceState p) (w : MarkedPath p)
    (T : ℝ) (i : Fin p.M) (j : Fin p.c) :
    ((timedState T (rawSequence p x w)) i).q j =
      ((timedState T (rawSequence p (sourceResetAll x) w)) i).q j + (x i).q j := by
  rw [rawSequence_resetAll_restore, offsetSequence_timedState]
  rfl

theorem timed_divisions_resetAll (p : Par) (x : SourceState p) (w : MarkedPath p)
    (T : ℝ) (i : Fin p.M) :
    ((timedState T (rawSequence p x w)) i).nd =
      ((timedState T (rawSequence p (sourceResetAll x) w)) i).nd + (x i).nd := by
  rw [rawSequence_resetAll_restore, offsetSequence_timedState]
  rfl

end
end CTMCHeredity20261019.V2.LedgerOffsets
