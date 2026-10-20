module

public import proofs.CTMCHeredity20261019.V3.Support
public import proofs.CTMCHeredity20261019.V3.WindowIdentity

@[expose] public section

/-! # All windows on the constructed joint law

The deterministic universal-time theorem is applied once on the simultaneous
support set. We do not intersect separate probability-one claims over real time.
The law is unconditional: failed histories are still sampled.
-/

namespace CTMCHeredity20261019.V3.ActualWindows

open FunctionalCapacity MeasureTheory ProbabilityTheory HybridCTMC.Kernel
open CF3Marked CF3RawPathLift V2 V2.LedgerOffsets WindowIdentity
open scoped ENNReal Classical
noncomputable section

local instance (p : Par) : MeasurableSpace (SourceState p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (SourceState p) := ⟨fun _ => trivial⟩
local instance (p : Par) : MeasurableSpace (CF3MarkedKernel.State p) := ⊤
local instance (p : Par) : MeasurableSingletonClass (CF3MarkedKernel.State p) :=
  ⟨fun _ => trivial⟩

def localState (p : Par) {n : ℕ} (h : RawOperated.History p n) (b : Fin n) (t : ℝ) :
    SourceState p := timedState t (h.1 b).2

def globalState (p : Par) (T : ℝ) (n : ℕ) (x : SourceState p)
    (z : RawOperated.History p n × MarkedPath p) (t : ℝ) : SourceState p :=
  timedState t (rawSequence p x (PhysicalOperated.stitch p T n z))

/-- Universal local times and the terminal endpoint hold together under the
actual completed law, for arbitrary initial natural q and nd ledgers. -/
theorem completedLaw_ae_windows_and_terminal {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
        globalState p T n x z ((b.val : ℝ)*T+t) =
          addLedgers p (localState p z.1 b t) (qOffset p T n z.1 b.val) (fun _ => 0)) ∧
      globalState p T n x z ((n : ℝ)*T) =
        addLedgers p z.1.2 (qOffset p T n z.1 n) (fun _ => 0) := by
  filter_upwards [Support.completedLaw_ae_support hp T n x] with z hz
  exact stitch_raw_windows_and_terminal p T hT n x z.1 z.2
    hz.1 hz.2.1 hz.2.2.1 hz.2.2.2

/-- Stored offsets stay at external slots. In particular the nd offset is a
single initial constant, never a sum of cumulative local nd endpoints. -/
theorem completedLaw_ae_windows_and_terminal_addLedgers {p : Par} (hp : p.Valid)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : SourceState p)
    (oq : Fin p.M → Fin p.c → ℕ) (ond : Fin p.M → ℕ) :
    ∀ᵐ z ∂PhysicalOperated.completedLaw hp T n x,
      (∀ b : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
        globalState p T n (addLedgers p x oq ond) z ((b.val : ℝ)*T+t) =
          addLedgers p (localState p z.1 b t)
            (fun i j => qOffset p T n z.1 b.val i j + oq i j) ond) ∧
      globalState p T n (addLedgers p x oq ond) z ((n : ℝ)*T) =
        addLedgers p z.1.2
          (fun i j => qOffset p T n z.1 n i j + oq i j) ond := by
  filter_upwards [Support.completedLaw_ae_support hp T n x] with z hz
  exact stitch_raw_windows_and_terminal_addLedgers p T hT n x z.1 z.2
    hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 oq ond

end
end CTMCHeredity20261019.V3.ActualWindows
