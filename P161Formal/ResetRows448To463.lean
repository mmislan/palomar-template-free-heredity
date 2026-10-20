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

theorem reset_cert_a_448 : resetParentTest 448 = true := by
  decide

theorem reset_cert_a_449 : resetParentTest 449 = true := by
  decide

theorem reset_cert_a_450 : resetParentTest 450 = true := by
  decide

theorem reset_cert_a_451 : resetParentTest 451 = true := by
  decide

theorem reset_cert_a_452 : resetParentTest 452 = true := by
  decide

theorem reset_cert_a_453 : resetParentTest 453 = true := by
  decide

theorem reset_cert_a_454 : resetParentTest 454 = true := by
  decide

theorem reset_cert_a_455 : resetParentTest 455 = true := by
  decide

theorem reset_cert_a_456 : resetParentTest 456 = true := by
  decide

theorem reset_cert_a_457 : resetParentTest 457 = true := by
  decide

theorem reset_cert_a_458 : resetParentTest 458 = true := by
  decide

theorem reset_cert_a_459 : resetParentTest 459 = true := by
  decide

theorem reset_cert_a_460 : resetParentTest 460 = true := by
  decide

theorem reset_cert_a_461 : resetParentTest 461 = true := by
  decide

theorem reset_cert_a_462 : resetParentTest 462 = true := by
  decide

theorem reset_cert_a_463 : resetParentTest 463 = true := by
  decide

def resetParents448To463 : List ℕ := [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]

theorem reset_block_448_to_463 : resetParents448To463.all resetParentTest = true := by
  simp only [resetParents448To463, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_448, ⟨reset_cert_a_449, ⟨reset_cert_a_450, ⟨reset_cert_a_451, ⟨reset_cert_a_452, ⟨reset_cert_a_453, ⟨reset_cert_a_454, ⟨reset_cert_a_455, ⟨reset_cert_a_456, ⟨reset_cert_a_457, ⟨reset_cert_a_458, ⟨reset_cert_a_459, ⟨reset_cert_a_460, ⟨reset_cert_a_461, ⟨reset_cert_a_462, reset_cert_a_463⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
