module

public import P161Formal.RecoveryProfile

/-!
An alternative proof witness for exactly the same P161 mission: A-(15/8)Delta.
The published11/8 witness, literal table, physical rates and event are preserved.
Its selected chemical decay is220, below the scanned230. Exact rational scans are discovery evidence;
the finite/structural inequalities still require strict Lean proofs.
-/

@[expose] public section
namespace P161Formal

def strongRecoveryWitnessQ (a : ℕ) (fuel : Bool) : ℚ :=
  recoveryAQ a - if fuel then (15 / 8) * recoveryGapQ a else 0

def chemicalReferenceForQ (H : ℕ → Bool → ℚ) (a : ℕ) (fuel : Bool) : ℚ :=
  if fuel then
    (a : ℚ) * (H (a - 1) true - H a true) +
    800 * a * (1 - (a : ℚ) / 2048) * (H (a + 1) false - H a true) +
    400 * a * (H (a - 1) false - H a true) +
    (4000000 * (3 + (a : ℚ) / 2048) + 800 * 2048) * (H a false - H a true)
  else (a : ℚ) * (H (a - 1) false - H a false) + 4000000 * (H a true - H a false)

theorem original_chemical_reference_eq (a : ℕ) (fuel : Bool) :
    chemicalReferenceForQ recoveryWitnessQ a fuel = recoveryChemicalQ a fuel := by rfl

def checkStrongRecoveryChemical (a : ℕ) (fuel : Bool) : Bool :=
  decide (chemicalReferenceForQ strongRecoveryWitnessQ a fuel +
    220 * strongRecoveryWitnessQ a fuel ≤ if a < 512 then 0 else 1 / 4700)

def checkStrongRecoveryShape (a : ℕ) : Bool :=
  decide (0 < strongRecoveryWitnessQ a true ∧
    strongRecoveryWitnessQ a true ≤ strongRecoveryWitnessQ a false ∧
    12 * strongRecoveryWitnessQ a false ≤ 338971453059 / 125000 ∧
    (if a < 512 then 1 ≤ strongRecoveryWitnessQ a true else True))

end P161Formal
