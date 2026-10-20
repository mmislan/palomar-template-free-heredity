module

public import P161Formal.SourceFiniteStock

/-! A normalized measurable law of the concrete stopped process. It retains
actual holding times and complete proposal labels, plus the absorbing optional
stock state. Proposals after failure are unused; no failure mass is discarded. -/

set_option autoImplicit false
@[expose] public section
namespace P161Formal
open MeasureTheory ProbabilityTheory HybridCTMC HybridCTMC.Kernel CTMCHeredity20261019
open CF3Marked CF3RawPathLift V2 V2.SeedSwitch V4.TwoPhaseIdentity V4.TwoPhaseEvent
open scoped Classical
noncomputable section

instance sourceStockStateCountable : Countable SourceStockState := by
  let f : SourceStockState → SourceState (literalSourcePar 6) × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
    fun s => (s.raw,s.feed,s.seeds,s.consumed,s.births,s.divisions,s.victimFuel)
  have hf : Function.Injective f := by
    rintro ⟨ar,aa,ae,ac,ab,ad,aw⟩ ⟨br,ba,be,bc,bb,bd,bw⟩ h
    simp only [f,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    rfl
  exact hf.countable

instance sourceStockStateMeasurableSpace : MeasurableSpace SourceStockState := ⊤
instance sourceStockStateMeasurableSingleton : MeasurableSingletonClass SourceStockState := ⟨fun _ => trivial⟩
instance sourceOptionStockMeasurableSpace : MeasurableSpace (Option SourceStockState) := ⊤
instance sourceOptionStockMeasurableSingleton : MeasurableSingletonClass (Option SourceStockState) := ⟨fun _ => trivial⟩

local instance stockProcessGenericRawMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (SourceState p) := ⊤
local instance stockProcessGenericRawMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance stockProcessGenericMarkedMeasurableSpace (p : FunctionalCapacity.Par) :
    MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance stockProcessGenericMarkedMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (CF3MarkedKernel.State p) := ⟨fun _ => trivial⟩
local instance stockProcessGenericOptionMeasurableSpace (p : FunctionalCapacity.Par) : MeasurableSpace (Option (Mark p)) := ⊤
local instance stockProcessGenericOptionMeasurableSingleton (p : FunctionalCapacity.Par) :
    MeasurableSingletonClass (Option (Mark p)) := ⟨fun _ => trivial⟩

local instance stockProcessRawMeasurableSpace : MeasurableSpace (SourceState (literalSourcePar 0)) := ⊤
local instance stockProcessRawMeasurableSingleton :
    MeasurableSingletonClass (SourceState (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stockProcessMarkedMeasurableSpace :
    MeasurableSpace (CF3MarkedKernel.State (literalSourcePar 0)) := ⊤
local instance stockProcessMarkedMeasurableSingleton :
    MeasurableSingletonClass (CF3MarkedKernel.State (literalSourcePar 0)) := ⟨fun _ => trivial⟩
local instance stockProcessOptionMeasurableSpace : MeasurableSpace (Option (Mark (literalSourcePar 0))) := ⊤
local instance stockProcessOptionMeasurableSingleton :
    MeasurableSingletonClass (Option (Mark (literalSourcePar 0))) := ⟨fun _ => trivial⟩

abbrev SourceTimedMarks := ℕ → ℝ × Option (Mark (literalSourcePar 6))
abbrev SourceFiniteTrace := SourceTimedMarks × (ℕ → Option SourceStockState)

def sourceTimedMarks (z : V4.TwoPhaseLaw.Completion) : SourceTimedMarks :=
  fun n => ((wholePath z n).1,(wholePath z n).2.2)

theorem measurable_sourceTimedMarks_coordinate (n : ℕ) :
    Measurable (fun z : V4.TwoPhaseLaw.Completion => sourceTimedMarks z n) := by
  have h : Measurable (fun z : V4.TwoPhaseLaw.Completion => wholePath z n) :=
    (measurable_pi_apply n).comp measurable_wholePath
  exact h.fst.prodMk ((measurable_of_countable (fun y : CF3MarkedKernel.State (literalSourcePar 6) => y.2)).comp h.snd)

theorem measurable_sourceStockRun (x : Raw) (n : ℕ) :
    Measurable (fun z : V4.TwoPhaseLaw.Completion => sourceStockRun x z n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let next : Option SourceStockState × Option (Mark (literalSourcePar 6)) → Option SourceStockState :=
        fun a => match a.1 with
        | none => none
        | some s => if (sourceStockStep s a.2).allowed then some (sourceStockStep s a.2) else none
      have hn : Measurable next := measurable_of_countable _
      have hm : Measurable (fun z : V4.TwoPhaseLaw.Completion => sourceStockMarks z n) :=
        (measurable_sourceTimedMarks_coordinate (n+1)).snd
      have he : (fun z => sourceStockRun x z (n+1)) =
          (fun z => next (sourceStockRun x z n,sourceStockMarks z n)) := by
        funext z
        cases hprev : stockStoppedRun SourceStockState.allowed sourceStockStep
            (sourceStockInitial x) (sourceStockMarks z) n with
        | none => simp only [sourceStockRun,stockStoppedRun,hprev,next]
        | some s =>
            by_cases ha : (sourceStockStep s (sourceStockMarks z n)).allowed <;>
              simp [sourceStockRun,stockStoppedRun,hprev,next,ha]
      rw [he]
      exact hn.comp (ih.prodMk hm)

def sourceStoppedTrace (x : Raw) (z : V4.TwoPhaseLaw.Completion) : SourceFiniteTrace :=
  (sourceTimedMarks z,sourceStockRun x z)

theorem measurable_sourceStoppedTrace (x : Raw) : Measurable (sourceStoppedTrace x) :=
  (measurable_pi_iff.mpr measurable_sourceTimedMarks_coordinate).prodMk
    (measurable_pi_iff.mpr (measurable_sourceStockRun x))

def sourceFiniteStockLaw (x : Raw) : Measure SourceFiniteTrace :=
  (V4.TwoPhaseLaw.completedSwitchLaw x).map (sourceStoppedTrace x)

instance sourceFiniteStockLaw_probability (x : Raw) : IsProbabilityMeasure (sourceFiniteStockLaw x) := by
  constructor
  rw [sourceFiniteStockLaw,Measure.map_apply (measurable_sourceStoppedTrace x) MeasurableSet.univ]
  simp

theorem source_finite_stock_law_no_mass_loss (x : Raw) : sourceFiniteStockLaw x Set.univ = 1 := measure_univ

end
end P161Formal
