module

public import P161Formal.StrongRecoveryProfile

/-! Separate exact lower-count recovery decisions, selected15/8,220 witness.
Both chemical rows and shape are checked by ordinary kernel reduction.
This source makes no stochastic or full-mission assertion. -/

public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem strong_row_576 :
    (checkStrongRecoveryChemical 576 false && checkStrongRecoveryChemical 576 true &&
      checkStrongRecoveryShape 576) = true := by decide +kernel

theorem strong_row_577 :
    (checkStrongRecoveryChemical 577 false && checkStrongRecoveryChemical 577 true &&
      checkStrongRecoveryShape 577) = true := by decide +kernel

theorem strong_row_578 :
    (checkStrongRecoveryChemical 578 false && checkStrongRecoveryChemical 578 true &&
      checkStrongRecoveryShape 578) = true := by decide +kernel

theorem strong_row_579 :
    (checkStrongRecoveryChemical 579 false && checkStrongRecoveryChemical 579 true &&
      checkStrongRecoveryShape 579) = true := by decide +kernel

theorem strong_row_580 :
    (checkStrongRecoveryChemical 580 false && checkStrongRecoveryChemical 580 true &&
      checkStrongRecoveryShape 580) = true := by decide +kernel

theorem strong_row_581 :
    (checkStrongRecoveryChemical 581 false && checkStrongRecoveryChemical 581 true &&
      checkStrongRecoveryShape 581) = true := by decide +kernel

theorem strong_row_582 :
    (checkStrongRecoveryChemical 582 false && checkStrongRecoveryChemical 582 true &&
      checkStrongRecoveryShape 582) = true := by decide +kernel

theorem strong_row_583 :
    (checkStrongRecoveryChemical 583 false && checkStrongRecoveryChemical 583 true &&
      checkStrongRecoveryShape 583) = true := by decide +kernel

theorem strong_row_584 :
    (checkStrongRecoveryChemical 584 false && checkStrongRecoveryChemical 584 true &&
      checkStrongRecoveryShape 584) = true := by decide +kernel

theorem strong_row_585 :
    (checkStrongRecoveryChemical 585 false && checkStrongRecoveryChemical 585 true &&
      checkStrongRecoveryShape 585) = true := by decide +kernel

theorem strong_row_586 :
    (checkStrongRecoveryChemical 586 false && checkStrongRecoveryChemical 586 true &&
      checkStrongRecoveryShape 586) = true := by decide +kernel

theorem strong_row_587 :
    (checkStrongRecoveryChemical 587 false && checkStrongRecoveryChemical 587 true &&
      checkStrongRecoveryShape 587) = true := by decide +kernel

theorem strong_row_588 :
    (checkStrongRecoveryChemical 588 false && checkStrongRecoveryChemical 588 true &&
      checkStrongRecoveryShape 588) = true := by decide +kernel

theorem strong_row_589 :
    (checkStrongRecoveryChemical 589 false && checkStrongRecoveryChemical 589 true &&
      checkStrongRecoveryShape 589) = true := by decide +kernel

theorem strong_row_590 :
    (checkStrongRecoveryChemical 590 false && checkStrongRecoveryChemical 590 true &&
      checkStrongRecoveryShape 590) = true := by decide +kernel

theorem strong_row_591 :
    (checkStrongRecoveryChemical 591 false && checkStrongRecoveryChemical 591 true &&
      checkStrongRecoveryShape 591) = true := by decide +kernel

theorem strong_recovery_rows_576_591 :
    (List.range' 576 16).all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a) = true := by
  change ([576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591].all (fun a => checkStrongRecoveryChemical a false &&
      checkStrongRecoveryChemical a true && checkStrongRecoveryShape a)) = true
  simp only [List.all_cons, List.all_nil, strong_row_576, strong_row_577, strong_row_578, strong_row_579, strong_row_580, strong_row_581, strong_row_582, strong_row_583, strong_row_584, strong_row_585, strong_row_586, strong_row_587, strong_row_588, strong_row_589, strong_row_590, strong_row_591, Bool.and_self]

end P161Formal
