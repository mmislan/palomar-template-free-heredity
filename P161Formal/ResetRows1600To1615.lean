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

theorem reset_cert_a_1600 : resetParentTest 1600 = true := by
  decide

theorem reset_cert_a_1601 : resetParentTest 1601 = true := by
  decide

theorem reset_cert_a_1602 : resetParentTest 1602 = true := by
  decide

theorem reset_cert_a_1603 : resetParentTest 1603 = true := by
  decide

theorem reset_cert_a_1604 : resetParentTest 1604 = true := by
  decide

theorem reset_cert_a_1605 : resetParentTest 1605 = true := by
  decide

theorem reset_cert_a_1606 : resetParentTest 1606 = true := by
  decide

theorem reset_cert_a_1607 : resetParentTest 1607 = true := by
  decide

theorem reset_cert_a_1608 : resetParentTest 1608 = true := by
  decide

theorem reset_cert_a_1609 : resetParentTest 1609 = true := by
  decide

theorem reset_cert_a_1610 : resetParentTest 1610 = true := by
  decide

theorem reset_cert_a_1611 : resetParentTest 1611 = true := by
  decide

theorem reset_cert_a_1612 : resetParentTest 1612 = true := by
  decide

theorem reset_cert_a_1613 : resetParentTest 1613 = true := by
  decide

theorem reset_cert_a_1614 : resetParentTest 1614 = true := by
  decide

theorem reset_cert_a_1615 : resetParentTest 1615 = true := by
  decide

def resetParents1600To1615 : List ℕ := [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]

theorem reset_block_1600_to_1615 : resetParents1600To1615.all resetParentTest = true := by
  simp only [resetParents1600To1615, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1600, ⟨reset_cert_a_1601, ⟨reset_cert_a_1602, ⟨reset_cert_a_1603, ⟨reset_cert_a_1604, ⟨reset_cert_a_1605, ⟨reset_cert_a_1606, ⟨reset_cert_a_1607, ⟨reset_cert_a_1608, ⟨reset_cert_a_1609, ⟨reset_cert_a_1610, ⟨reset_cert_a_1611, ⟨reset_cert_a_1612, ⟨reset_cert_a_1613, ⟨reset_cert_a_1614, reset_cert_a_1615⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
