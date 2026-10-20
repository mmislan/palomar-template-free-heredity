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

theorem reset_cert_a_544 : resetParentTest 544 = true := by
  decide

theorem reset_cert_a_545 : resetParentTest 545 = true := by
  decide

theorem reset_cert_a_546 : resetParentTest 546 = true := by
  decide

theorem reset_cert_a_547 : resetParentTest 547 = true := by
  decide

theorem reset_cert_a_548 : resetParentTest 548 = true := by
  decide

theorem reset_cert_a_549 : resetParentTest 549 = true := by
  decide

theorem reset_cert_a_550 : resetParentTest 550 = true := by
  decide

theorem reset_cert_a_551 : resetParentTest 551 = true := by
  decide

theorem reset_cert_a_552 : resetParentTest 552 = true := by
  decide

theorem reset_cert_a_553 : resetParentTest 553 = true := by
  decide

theorem reset_cert_a_554 : resetParentTest 554 = true := by
  decide

theorem reset_cert_a_555 : resetParentTest 555 = true := by
  decide

theorem reset_cert_a_556 : resetParentTest 556 = true := by
  decide

theorem reset_cert_a_557 : resetParentTest 557 = true := by
  decide

theorem reset_cert_a_558 : resetParentTest 558 = true := by
  decide

theorem reset_cert_a_559 : resetParentTest 559 = true := by
  decide

def resetParents544To559 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]

theorem reset_block_544_to_559 : resetParents544To559.all resetParentTest = true := by
  simp only [resetParents544To559, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_544, ⟨reset_cert_a_545, ⟨reset_cert_a_546, ⟨reset_cert_a_547, ⟨reset_cert_a_548, ⟨reset_cert_a_549, ⟨reset_cert_a_550, ⟨reset_cert_a_551, ⟨reset_cert_a_552, ⟨reset_cert_a_553, ⟨reset_cert_a_554, ⟨reset_cert_a_555, ⟨reset_cert_a_556, ⟨reset_cert_a_557, ⟨reset_cert_a_558, reset_cert_a_559⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
