module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum

/-!
Pointwise gross-stock accounting for one uninterrupted history. This module
does not assert a stochastic stock tail, a coupling, or source-law conservation.
It proves the exact consequences of the source's fuel conservation identity and
monotone observations, without replenishing any episode's inventory.
-/

@[expose] public section

namespace P161Formal

/-- Cumulative observations at one prefix. `ordinary` and `triggered` consume
fuel; passive catalyst deaths consume no fuel. Victim fuel is separate. -/
structure GrossLedger where
  feed : ℕ
  seeds : ℕ
  births : ℕ
  activeDeaths : ℕ
  ordinary : ℕ
  triggered : ℕ
  discharge : ℕ
  divisions : ℕ
  victimFuel : ℕ
  victimSlots : ℕ
  deriving DecidableEq

def GrossLedger.consumed (L : GrossLedger) : ℕ :=
  L.births + L.activeDeaths + L.ordinary + L.triggered + L.discharge

def GrossLedger.precursors (L : GrossLedger) : ℕ := L.births + L.seeds

def GrossLedger.credits (L : GrossLedger) : ℕ := L.ordinary + L.triggered

/-- No molecule is supplied by restoring handling capacity after a victim is
overwritten; its capacity bound is kept separate from precursor entries. -/
def GrossLedger.Balanced (L : GrossLedger) (initialFuel remainingFuel : ℕ) : Prop :=
  initialFuel + L.feed = remainingFuel + L.consumed + L.victimFuel

theorem gross_prefix_caps (L : GrossLedger) (initialFuel remainingFuel : ℕ)
    (hbalance : L.Balanced initialFuel remainingFuel)
    (hinitial : initialFuel ≤ 4)
    (hfeed : L.feed ≤ 800000000) (hseed : L.seeds ≤ 5000)
    (hdivision : L.divisions ≤ 1200)
    (hvictimFuel : L.victimFuel ≤ L.divisions)
    (hslots : L.victimSlots ≤ 3 * 2048 * L.divisions) :
    L.consumed ≤ 800000004 ∧ L.precursors ≤ 800005004 ∧
    L.credits ≤ 800000004 ∧ L.victimFuel ≤ 1200 ∧
    L.victimSlots ≤ 7372800 := by
  unfold GrossLedger.Balanced GrossLedger.consumed at hbalance
  simp only [GrossLedger.consumed, GrossLedger.precursors, GrossLedger.credits]
  omega

/-- Monotone global counters supply every prefix's same cap; there is no
per-recovery or per-service-block reset of stock. -/
theorem caps_at_prefix (A E D : ℕ → ℕ)
    (hA : Monotone A) (hE : Monotone E) (hD : Monotone D)
    (n horizon : ℕ) (hn : n ≤ horizon)
    (hAcap : A horizon ≤ 800000000) (hEcap : E horizon ≤ 5000)
    (hDcap : D horizon ≤ 1200) :
    A n ≤ 800000000 ∧ E n ≤ 5000 ∧ D n ≤ 1200 :=
  ⟨le_trans (hA hn) hAcap, le_trans (hE hn) hEcap, le_trans (hD hn) hDcap⟩

/-- The protected daughters are complementary allocations of one parent. -/
theorem complementary_floor_parent (parent first floor : ℕ)
    (hfirst : floor ≤ first) (hsecond : floor ≤ parent - first)
    (hsplit : first ≤ parent) : 2 * floor ≤ parent := by omega

theorem protected_parent_32 (parent first : ℕ)
    (hfirst : 16 ≤ first) (hsecond : 16 ≤ parent - first)
    (hsplit : first ≤ parent) : 32 ≤ parent := by omega

theorem service_credit_arithmetic :
    300 * 4 * 2 * 500 = (1200000 : ℕ) ∧
    300 * 4 * 3 * 500 = (1800000 : ℕ) ∧
    300 * 4 * 2 * 500 + 300 * 4 * 3 * 500 = (3000000 : ℕ) := by norm_num

end P161Formal
