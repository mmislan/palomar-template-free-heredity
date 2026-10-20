module

public import P161Formal.BinomialRecurrence
public import P161Formal.ProfileData
public import P161Formal.LowProfileData
public import Mathlib.Tactic.NormNum

/-! Exact integer cross-multiplication for C11. A full certificate is not
asserted. Pilot the recurrence and the data against the literal specification
before any full 4,066-row evaluation. -/

@[expose] public section
namespace P161Formal

/-- The residual comparison after multiplying by the positive common
denominator N*2^a*10^18*dDen*bDen. Soundness as a real residual follows in a
separate lemma; this decidable integer predicate alone is not that lemma. -/
def checkResetRow (a : ℕ) (fuel : Bool) (bNum : ℤ) (bDen : ℕ) : Bool :=
  let pair := fullProfilePairs[a]?.getD (0, 0)
  let X := (if fuel then pair.2 else pair.1) - 1
  let K := pairedMomentNumerator fullProfileFuelZero a
  let pNum := if fuel then 3 * 2048 + a else 2048
  decide ((2 * pNum * K * 200000000 * bDen : ℤ) ≤
    (93867565097 * X * 2048 * 2^a * bDen : ℤ) +
    bNum * (2048 * 2^a * 10^18 * 200000000 : ℤ))

def checkGlobalResetRow (a : ℕ) (fuel : Bool) : Bool :=
  checkResetRow a fuel 3343277526704540851 125000000000000000

def checkDeficientResetRow (a : ℕ) (fuel : Bool) : Bool :=
  checkResetRow a fuel (-147104211175367700201) 500000000000000000

set_option maxRecDepth 8192 in
theorem full_profile_length : fullProfilePairs.length = 2050 := by
  norm_num [fullProfilePairs, List.length_flatten,
    profileBlock0, profileBlock1, profileBlock2, profileBlock3, profileBlock4, profileBlock5, profileBlock6, profileBlock7, profileBlock8, profileBlock9, profileBlock10, profileBlock11, profileBlock12, profileBlock13, profileBlock14, profileBlock15, profileBlock16]

set_option maxRecDepth 8192 in
theorem full_profile_low_agrees :
    (fullProfilePairs.drop 16).take 496 = lowProfilePairs := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem reset_row32_pilot :
    checkGlobalResetRow 32 false = true ∧ checkGlobalResetRow 32 true = true ∧
    checkDeficientResetRow 32 false = true ∧ checkDeficientResetRow 32 true = true := by
  decide

end P161Formal
