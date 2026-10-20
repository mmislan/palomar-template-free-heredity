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

theorem reset_cert_a_592 : resetParentTest 592 = true := by
  decide

theorem reset_cert_a_593 : resetParentTest 593 = true := by
  decide

theorem reset_cert_a_594 : resetParentTest 594 = true := by
  decide

theorem reset_cert_a_595 : resetParentTest 595 = true := by
  decide

theorem reset_cert_a_596 : resetParentTest 596 = true := by
  decide

theorem reset_cert_a_597 : resetParentTest 597 = true := by
  decide

theorem reset_cert_a_598 : resetParentTest 598 = true := by
  decide

theorem reset_cert_a_599 : resetParentTest 599 = true := by
  decide

theorem reset_cert_a_600 : resetParentTest 600 = true := by
  decide

theorem reset_cert_a_601 : resetParentTest 601 = true := by
  decide

theorem reset_cert_a_602 : resetParentTest 602 = true := by
  decide

theorem reset_cert_a_603 : resetParentTest 603 = true := by
  decide

theorem reset_cert_a_604 : resetParentTest 604 = true := by
  decide

theorem reset_cert_a_605 : resetParentTest 605 = true := by
  decide

theorem reset_cert_a_606 : resetParentTest 606 = true := by
  decide

theorem reset_cert_a_607 : resetParentTest 607 = true := by
  decide

def resetParents592To607 : List ℕ := [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]

theorem reset_block_592_to_607 : resetParents592To607.all resetParentTest = true := by
  simp only [resetParents592To607, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_592, ⟨reset_cert_a_593, ⟨reset_cert_a_594, ⟨reset_cert_a_595, ⟨reset_cert_a_596, ⟨reset_cert_a_597, ⟨reset_cert_a_598, ⟨reset_cert_a_599, ⟨reset_cert_a_600, ⟨reset_cert_a_601, ⟨reset_cert_a_602, ⟨reset_cert_a_603, ⟨reset_cert_a_604, ⟨reset_cert_a_605, ⟨reset_cert_a_606, reset_cert_a_607⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
