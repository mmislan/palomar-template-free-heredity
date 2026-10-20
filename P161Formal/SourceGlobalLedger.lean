module

public import P161Formal.SourceGrossLedger
public import P161Formal.SourceStockObservations

/-! Actual positive support follows complete labels across physical splices.
Natural-ledger resets preserve the physical core and supply no stock. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch
open V2.PhysicalSplice V2.ExecutedWindows
open scoped BigOperators Classical
noncomputable section

theorem source_raw_supported_core_congr (seed : ℝ) (hseed : 0 ≤ seed)
    (x y : SourceState (literalSourcePar seed)) (hxy : coreProject x = coreProject y)
    (w : MarkedPath (literalSourcePar seed)) (hw : sourceRawSupported seed x w) :
    sourceRawSupported seed y w := by
  intro n m hm
  have hc := raw_at_core_congr (literal_source_valid seed hseed) x y hxy w n
  have hp := hw n m hm
  rw [CF3MarkedKernel.sourceIntensity_lump (literalSourcePar seed) (rawAt (literalSourcePar seed) x w n) m] at hp
  rw [CF3MarkedKernel.sourceIntensity_lump (literalSourcePar seed) (rawAt (literalSourcePar seed) y w n) m,
    ←hc]
  exact hp

theorem source_raw_supported_prefix_splice (seed : ℝ)
    (x : SourceState (literalSourcePar seed)) (n : ℕ) (T : ℝ)
    (w v : MarkedPath (literalSourcePar seed)) (hw : sourceRawSupported seed x w)
    (hv : sourceRawSupported seed (rawAt (literalSourcePar seed) x w n) v) :
    sourceRawSupported seed x (prefixSplice n T (Preorder.frestrictLe n w,v)) := by
  intro k m hm
  by_cases hk : k < n
  · have hraw := prefixSplice_rawAt_prefix (literalSourcePar seed) x n T w v k hk.le
    have hmark := congrArg (fun q : ℝ × CF3MarkedKernel.State (literalSourcePar seed) => q.2.2)
      (prefixSplice_prefix n T (Preorder.frestrictLe n w) v (k+1) (by omega))
    change (prefixSplice n T (Preorder.frestrictLe n w,v) (k+1)).2.2 = (w (k+1)).2.2 at hmark
    rw [hmark] at hm
    rw [hraw]
    exact hw k m hm
  · have he : k = n+(k-n) := by omega
    rw [he,prefixSplice_state_positive] at hm
    rw [he,prefixSplice_rawAt_after]
    exact hv (k-n) m hm

theorem source_raw_supported_splice (seed : ℝ)
    (x : SourceState (literalSourcePar seed)) (T : ℝ)
    (w v : MarkedPath (literalSourcePar seed)) (hw : sourceRawSupported seed x w)
    (hv : sourceRawSupported seed (timedState T (rawSequence (literalSourcePar seed) x w)) v) :
    sourceRawSupported seed x (splice T (w,v)) :=
  source_raw_supported_prefix_splice seed x (clockIndex T w) T w v hw hv

theorem source_zero_seed_intensity_le_six (x : SourceState (literalSourcePar 0))
    (m : Mark (literalSourcePar 0)) :
    sourceIntensity (literalSourcePar 0) x m ≤ sourceIntensity (literalSourcePar 6) x m := by
  cases m with
  | inl ik =>
      rcases ik with ⟨i,k⟩
      cases k with
      | inl tj =>
          rcases tj with ⟨t,j⟩
          by_cases ht : t = 0
          · subst t
            have ha : (((x i).a j : ℕ) : ℝ) ≤ 2048 := by
              exact_mod_cast (show ((x i).a j : ℕ) ≤ 2048 by
                have h := ((x i).a j).isLt
                change ((x i).a j : ℕ) < 2048+1 at h
                omega)
            simp only [sourceIntensity,FunctionalCapacity.cf3,literalSourcePar,ite_true,zero_mul]
            unfold FunctionalCapacity.Site.u
            linarith
          · simp only [sourceIntensity,FunctionalCapacity.cf3,ite_eq_right ht]
            exact le_refl _
      | inr b => cases b <;> exact le_refl _
  | inr d =>
      rcases d with ⟨i,k,o,v⟩
      cases k <;> exact le_refl _

theorem source_raw_supported_zero_to_six
    (x : SourceState (literalSourcePar 0)) (w : MarkedPath (literalSourcePar 0))
    (hw : sourceRawSupported 0 x w) : sourceRawSupported 6 x w := by
  intro n m hm
  have hp := hw n m hm
  have hi := source_zero_seed_intensity_le_six (rawAt (literalSourcePar 0) x w n) m
  have hr : rawAt (literalSourcePar 6) x w n = rawAt (literalSourcePar 0) x w n := by
    simpa only [literal_seed_on_parameter,literal_seed_off_parameter] using
      V4.TwoPhaseIdentity.rawAt_on_eq_off x w n
  rw [hr]
  exact hp.trans_le hi


theorem source_supported_faithful_segment (seed : ℝ)
    (s : RawOperated.Segment (literalSourcePar seed)) (x : SourceState (literalSourcePar seed))
    (hs : sourceSupportedSegment (literalSourcePar seed) s)
    (hf : RawOperated.faithful (literalSourcePar seed) s) (hx : s.2 0 = (0,x)) :
    sourceRawSupported seed x s.1 := by
  have hraw := V3.WindowIdentity.faithful_raw_eq_of_start (literalSourcePar seed) s x hf hx
  intro n m hm
  have hp := hs n m hm
  rw [hraw] at hp
  exact hp

theorem source_stitch_supported (seed : ℝ) (hseed : 0 ≤ seed) (T : ℝ) (n : ℕ)
    (x : SourceState (literalSourcePar seed)) (h : RawOperated.History (literalSourcePar seed) n)
    (v : MarkedPath (literalSourcePar seed))
    (hc : RawOperated.compatible (literalSourcePar seed) T n x h)
    (hf : RawOperated.allSegments (RawOperated.faithful (literalSourcePar seed)) h)
    (hs : RawOperated.allSegments (sourceSupportedSegment (literalSourcePar seed)) h)
    (hv : sourceRawSupported seed h.2 v) :
    sourceRawSupported seed x (PhysicalOperated.stitch (literalSourcePar seed) T n (h,v)) := by
  induction n generalizing x with
  | zero =>
      have he : h.2 = x := hc
      change sourceRawSupported seed x v
      exact he ▸ hv
  | succ n ih =>
      let s : RawOperated.Segment (literalSourcePar seed) := h.1 0
      let r : MarkedPath (literalSourcePar seed) :=
        PhysicalOperated.stitch (literalSourcePar seed) T n (Operated.tail h,v)
      have hraw := V3.WindowIdentity.faithful_raw_eq_of_start (literalSourcePar seed) s x (hf 0) hc.1
      have hleft := source_supported_faithful_segment seed s x (hs 0) (hf 0) hc.1
      have hft : RawOperated.allSegments (RawOperated.faithful (literalSourcePar seed)) (Operated.tail h) :=
        fun i => hf i.succ
      have hst : RawOperated.allSegments (sourceSupportedSegment (literalSourcePar seed)) (Operated.tail h) :=
        fun i => hs i.succ
      have htail := ih (RawOperated.nextState (literalSourcePar seed) T s) (Operated.tail h)
        hc.2 hft hst hv
      have hcore : coreProject (RawOperated.nextState (literalSourcePar seed) T s) =
          coreProject (timedState T (rawSequence (literalSourcePar seed) x s.1)) := by
        change coreProject (sourceResetQ (p := literalSourcePar seed) (timedState T s.2)) = _
        rw [source_reset_q_core,hraw]
      have hright := source_raw_supported_core_congr seed hseed
        (RawOperated.nextState (literalSourcePar seed) T s)
        (timedState T (rawSequence (literalSourcePar seed) x s.1)) hcore r htail
      exact source_raw_supported_splice seed x T s.1 r hleft hright

end
end P161Formal
