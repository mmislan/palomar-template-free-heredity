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

theorem reset_cert_a_576 : resetParentTest 576 = true := by
  decide

theorem reset_cert_a_577 : resetParentTest 577 = true := by
  decide

theorem reset_cert_a_578 : resetParentTest 578 = true := by
  decide

theorem reset_cert_a_579 : resetParentTest 579 = true := by
  decide

theorem reset_cert_a_580 : resetParentTest 580 = true := by
  decide

theorem reset_cert_a_581 : resetParentTest 581 = true := by
  decide

theorem reset_cert_a_582 : resetParentTest 582 = true := by
  decide

theorem reset_cert_a_583 : resetParentTest 583 = true := by
  decide

theorem reset_cert_a_584 : resetParentTest 584 = true := by
  decide

theorem reset_cert_a_585 : resetParentTest 585 = true := by
  decide

theorem reset_cert_a_586 : resetParentTest 586 = true := by
  decide

theorem reset_cert_a_587 : resetParentTest 587 = true := by
  decide

theorem reset_cert_a_588 : resetParentTest 588 = true := by
  decide

theorem reset_cert_a_589 : resetParentTest 589 = true := by
  decide

theorem reset_cert_a_590 : resetParentTest 590 = true := by
  decide

theorem reset_cert_a_591 : resetParentTest 591 = true := by
  decide

def resetParents576To591 : List ℕ := [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]

theorem reset_block_576_to_591 : resetParents576To591.all resetParentTest = true := by
  simp only [resetParents576To591, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_576, ⟨reset_cert_a_577, ⟨reset_cert_a_578, ⟨reset_cert_a_579, ⟨reset_cert_a_580, ⟨reset_cert_a_581, ⟨reset_cert_a_582, ⟨reset_cert_a_583, ⟨reset_cert_a_584, ⟨reset_cert_a_585, ⟨reset_cert_a_586, ⟨reset_cert_a_587, ⟨reset_cert_a_588, ⟨reset_cert_a_589, ⟨reset_cert_a_590, reset_cert_a_591⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
