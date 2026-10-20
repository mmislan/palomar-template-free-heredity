module

public import P161Formal.ResetCertificateInterface
public import P161Formal.ResetPilots
public import P161Formal.ResetSeparatePilot

/-! Exact literal residuals for this finite block. Each new parent is checked
by the ordinary kernel decision procedure. No native evaluator is used. -/

@[expose] public section
namespace P161Formal
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

theorem reset_cert_a_464 : resetParentTest 464 = true := by
  decide

theorem reset_cert_a_465 : resetParentTest 465 = true := by
  decide

theorem reset_cert_a_466 : resetParentTest 466 = true := by
  decide

theorem reset_cert_a_467 : resetParentTest 467 = true := by
  decide

theorem reset_cert_a_468 : resetParentTest 468 = true := by
  decide

theorem reset_cert_a_469 : resetParentTest 469 = true := by
  decide

theorem reset_cert_a_470 : resetParentTest 470 = true := by
  decide

theorem reset_cert_a_471 : resetParentTest 471 = true := by
  decide

theorem reset_cert_a_472 : resetParentTest 472 = true := by
  decide

theorem reset_cert_a_473 : resetParentTest 473 = true := by
  decide

theorem reset_cert_a_474 : resetParentTest 474 = true := by
  decide

theorem reset_cert_a_475 : resetParentTest 475 = true := by
  decide

theorem reset_cert_a_476 : resetParentTest 476 = true := by
  decide

theorem reset_cert_a_477 : resetParentTest 477 = true := by
  decide

theorem reset_cert_a_478 : resetParentTest 478 = true := by
  decide

theorem reset_cert_a_479 : resetParentTest 479 = true := by
  decide

def resetParents464To479 : List ℕ := [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]

theorem reset_block_464_to_479 : resetParents464To479.all resetParentTest = true := by
  simp only [resetParents464To479, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_464, ⟨reset_cert_a_465, ⟨reset_cert_a_466, ⟨reset_cert_a_467, ⟨reset_cert_a_468, ⟨reset_cert_a_469, ⟨reset_cert_a_470, ⟨reset_cert_a_471, ⟨reset_cert_a_472, ⟨reset_cert_a_473, ⟨reset_cert_a_474, ⟨reset_cert_a_475, ⟨reset_cert_a_476, ⟨reset_cert_a_477, ⟨reset_cert_a_478, reset_cert_a_479⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
