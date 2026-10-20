module

public import P161Formal.SourceMissionObservations
public import P161Formal.FiniteStockCoupling

/-! One global finite-stock process at complete physical marks. The first
attempted excess enters absorbing failure; equality at a ceiling is allowed.
The sampled waits, marks and complementary daughters come from the same
unconditional switched completion. No boundary replenishes these counters. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity
open scoped BigOperators Classical
noncomputable section

@[ext] structure SourceStockState where
  raw : SourceState (literalSourcePar 6)
  feed : ℕ
  seeds : ℕ
  consumed : ℕ
  births : ℕ
  divisions : ℕ
  victimFuel : ℕ

def SourceStockState.allowed (s : SourceStockState) : Prop :=
  s.feed ≤ 800000000 ∧ s.seeds ≤ 5000 ∧ s.consumed+s.victimFuel ≤ 800000004 ∧
    s.births+s.seeds ≤ 800005004 ∧ s.divisions ≤ 1200 ∧
      3*2048*s.divisions ≤ 7372800 ∧ s.victimFuel ≤ 1200

def sourceStockInitial (x : Raw) : SourceStockState :=
  ⟨sourceGlobalInitial x,0,0,0,0,0,0⟩

def sourceStockStep (s : SourceStockState) (m : Option (Mark (literalSourcePar 6))) : SourceStockState where
  raw := sourceProposalNext (literalSourcePar 6) s.raw m
  feed := s.feed+sourceMarkFeed m
  seeds := s.seeds+sourceMarkSeeds m
  consumed := s.consumed+sourceMarkConsumed m
  births := s.births+sourceMarkBirths m
  divisions := s.divisions+sourceMarkDivision m
  victimFuel := s.victimFuel+sourceMarkVictimFuel s.raw m

def sourceStockMarks (z : V4.TwoPhaseLaw.Completion) (k : ℕ) : Option (Mark (literalSourcePar 6)) :=
  (wholePath z (k+1)).2.2

def sourceStockAtPrefix (x : Raw) (z : V4.TwoPhaseLaw.Completion) (n : ℕ) : SourceStockState where
  raw := rawAt (literalSourcePar 6) (sourceGlobalInitial x) (wholePath z) n
  feed := sourcePrefixCount 6 sourceMarkFeed (wholePath z) n
  seeds := sourcePrefixCount 6 sourceMarkSeeds (wholePath z) n
  consumed := sourcePrefixCount 6 sourceMarkConsumed (wholePath z) n
  births := sourcePrefixCount 6 sourceMarkBirths (wholePath z) n
  divisions := sourcePrefixCount 6 sourceMarkDivision (wholePath z) n
  victimFuel := sourcePrefixVictimFuel 6 (sourceGlobalInitial x) (wholePath z) n

def sourceStockRun (x : Raw) (z : V4.TwoPhaseLaw.Completion) : ℕ → Option SourceStockState :=
  stockStoppedRun SourceStockState.allowed sourceStockStep (sourceStockInitial x) (sourceStockMarks z)

theorem source_unlimited_stock_eq_prefix (x : Raw) (z : V4.TwoPhaseLaw.Completion) (n : ℕ) :
    unlimitedRun sourceStockStep (sourceStockInitial x) (sourceStockMarks z) n = sourceStockAtPrefix x z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [unlimitedRun,ih]
      apply SourceStockState.ext
      · rfl
      all_goals simp only [sourceStockStep,sourceStockAtPrefix,sourceStockMarks,sourcePrefixCount,
        sourcePrefixVictimFuel,Finset.sum_range_succ]

theorem source_prefix_count_monotone (seed : ℝ)
    (f : Option (Mark (literalSourcePar seed)) → ℕ) (w : MarkedPath (literalSourcePar seed)) :
    Monotone (sourcePrefixCount seed f w) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold sourcePrefixCount
  rw [Finset.sum_range_succ]
  omega

theorem source_stock_prefix_allowed (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hs : sourceRawSupported 6 (sourceGlobalInitial x) (wholePath z)) (n : ℕ)
    (ha : sourcePrefixCount 6 sourceMarkFeed (wholePath z) n ≤ 800000000)
    (he : sourcePrefixCount 6 sourceMarkSeeds (wholePath z) n ≤ 5000)
    (hd : sourcePrefixCount 6 sourceMarkDivision (wholePath z) n ≤ 1200) :
    (sourceStockAtPrefix x z n).allowed := by
  have hb := source_prefix_gross_caps 6 (by norm_num) (sourceGlobalInitial x) (wholePath z) hs n ha he hd
  exact ⟨ha,he,hb.1,hb.2.1,hd,hb.2.2.2,hb.2.2.1⟩

theorem source_stock_identical_at_prefix (x : Raw) (z : V4.TwoPhaseLaw.Completion)
    (hs : sourceRawSupported 6 (sourceGlobalInitial x) (wholePath z)) (n : ℕ)
    (ha : sourcePrefixCount 6 sourceMarkFeed (wholePath z) n ≤ 800000000)
    (he : sourcePrefixCount 6 sourceMarkSeeds (wholePath z) n ≤ 5000)
    (hd : sourcePrefixCount 6 sourceMarkDivision (wholePath z) n ≤ 1200) :
    sourceStockRun x z n = some (sourceStockAtPrefix x z n) := by
  have hgood (k : ℕ) (hk : k ≤ n) :
      (unlimitedRun sourceStockStep (sourceStockInitial x) (sourceStockMarks z) k).allowed := by
    rw [source_unlimited_stock_eq_prefix]
    exact source_stock_prefix_allowed x z hs k
      ((source_prefix_count_monotone 6 sourceMarkFeed (wholePath z) hk).trans ha)
      ((source_prefix_count_monotone 6 sourceMarkSeeds (wholePath z) hk).trans he)
      ((source_prefix_count_monotone 6 sourceMarkDivision (wholePath z) hk).trans hd)
  exact (identical_marks_until_exhaustion SourceStockState.allowed sourceStockStep
    (sourceStockInitial x) (sourceStockMarks z) n hgood).trans
      (congrArg some (source_unlimited_stock_eq_prefix x z n))

theorem source_stock_never_exceeds (x : Raw) (z : V4.TwoPhaseLaw.Completion) (n : ℕ)
    (s : SourceStockState) (hs : sourceStockRun x z n = some s) : s.allowed :=
  stock_never_accepts_excess SourceStockState.allowed sourceStockStep
    (sourceStockInitial x) (sourceStockMarks z) n s hs

theorem source_stock_failure_absorbs (x : Raw) (z : V4.TwoPhaseLaw.Completion) (n : ℕ)
    (hn : sourceStockRun x z n = none) (k : ℕ) : sourceStockRun x z (n+k) = none :=
  stock_failure_absorbs SourceStockState.allowed sourceStockStep (sourceStockInitial x) (sourceStockMarks z) n hn k

end
end P161Formal
