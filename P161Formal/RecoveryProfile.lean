module

public import P161Formal.ProfileData
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum

/-!
The new beta4m recovery witness, defined from the literal low table and the
printed exact high tail. No old unknown band solution is a definition here.
The tail correction retains the conservative junction at768. This file starts
the independent high-envelope/chemical-row interface; no full witness theorem
is asserted before its finite and structural obligations are checked.
-/

@[expose] public section
namespace P161Formal

def profileEntryQ (a : ℕ) (fuel : Bool) : ℚ :=
  let row := fullProfilePairs[a]?.getD (0, 0)
  ((if fuel then row.2 else row.1 : ℕ) : ℚ) / 10^18

def cubicRecoveryTailQ (a : ℕ) : ℚ :=
  ((980 - (a : ℚ)) * (981 - a) * (982 - a)) /
    (((a : ℚ) - 10) * (a - 9) * (a - 8))

def recoveryTailQ (a : ℕ) : ℚ :=
  if a ≤ 768 then cubicRecoveryTailQ a
  else cubicRecoveryTailQ 768 * (10 / 11) ^ (a - 768)

def recoveryTailAQ (a : ℕ) : ℚ := recoveryTailQ a / cubicRecoveryTailQ 512

def recoveryTailKQ (a : ℕ) : ℚ :=
  if a < 768 then
    6 * (1 - (a : ℚ) / 2048) * (recoveryTailQ (a + 1) / recoveryTailQ a - 1) +
      (a : ℚ) * (recoveryTailQ (a - 1) / recoveryTailQ a - 1)
  else 5647 * (a : ℚ) / 56320 - 6 / 11

def recoveryTailDeltaQ (a : ℕ) : ℚ :=
  recoveryTailAQ a * (258 + recoveryTailKQ a) / 8000000

def recoveryBaseQ (a : ℕ) (fuel : Bool) : ℚ :=
  recoveryTailAQ a - if fuel then recoveryTailDeltaQ a else 0

def recoveryAQ (a : ℕ) : ℚ :=
  if a < 512 then profileEntryQ a false else recoveryTailAQ a

def recoveryGapQ (a : ℕ) : ℚ :=
  if a < 512 then profileEntryQ a false - profileEntryQ a true
  else recoveryTailDeltaQ a

def recoveryWitnessQ (a : ℕ) (fuel : Bool) : ℚ :=
  recoveryAQ a - if fuel then (11 / 8) * recoveryGapQ a else 0

def checkTailEnclosure (a : ℕ) (fuel : Bool) : Bool :=
  decide (profileEntryQ a fuel - 1 / 10^18 ≤ recoveryBaseQ a fuel ∧
    recoveryBaseQ a fuel ≤ profileEntryQ a fuel)

/-- Unfueled and fueled reference chemistry, with all resets omitted. -/
def recoveryChemicalQ (a : ℕ) (fuel : Bool) : ℚ :=
  if fuel then
    (a : ℚ) * (recoveryWitnessQ (a - 1) true - recoveryWitnessQ a true) +
    800 * a * (1 - (a : ℚ) / 2048) *
      (recoveryWitnessQ (a + 1) false - recoveryWitnessQ a true) +
    400 * a * (recoveryWitnessQ (a - 1) false - recoveryWitnessQ a true) +
    (4000000 * (3 + (a : ℚ) / 2048) + 800 * 2048) *
      (recoveryWitnessQ a false - recoveryWitnessQ a true)
  else
    (a : ℚ) * (recoveryWitnessQ (a - 1) false - recoveryWitnessQ a false) +
      4000000 * (recoveryWitnessQ a true - recoveryWitnessQ a false)

def checkRecoveryChemical (a : ℕ) (fuel : Bool) : Bool :=
  decide (recoveryChemicalQ a fuel + 150 * recoveryWitnessQ a fuel ≤
    if a < 512 then 0 else 1 / 4700)

end P161Formal
