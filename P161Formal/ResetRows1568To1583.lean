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

theorem reset_cert_a_1568 : resetParentTest 1568 = true := by
  decide

theorem reset_cert_a_1569 : resetParentTest 1569 = true := by
  decide

theorem reset_cert_a_1570 : resetParentTest 1570 = true := by
  decide

theorem reset_cert_a_1571 : resetParentTest 1571 = true := by
  decide

theorem reset_cert_a_1572 : resetParentTest 1572 = true := by
  decide

theorem reset_cert_a_1573 : resetParentTest 1573 = true := by
  decide

theorem reset_cert_a_1574 : resetParentTest 1574 = true := by
  decide

theorem reset_cert_a_1575 : resetParentTest 1575 = true := by
  decide

theorem reset_cert_a_1576 : resetParentTest 1576 = true := by
  decide

theorem reset_cert_a_1577 : resetParentTest 1577 = true := by
  decide

theorem reset_cert_a_1578 : resetParentTest 1578 = true := by
  decide

theorem reset_cert_a_1579 : resetParentTest 1579 = true := by
  decide

theorem reset_cert_a_1580 : resetParentTest 1580 = true := by
  decide

theorem reset_cert_a_1581 : resetParentTest 1581 = true := by
  decide

theorem reset_cert_a_1582 : resetParentTest 1582 = true := by
  decide

theorem reset_cert_a_1583 : resetParentTest 1583 = true := by
  decide

def resetParents1568To1583 : List ℕ := [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]

theorem reset_block_1568_to_1583 : resetParents1568To1583.all resetParentTest = true := by
  simp only [resetParents1568To1583, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1568, ⟨reset_cert_a_1569, ⟨reset_cert_a_1570, ⟨reset_cert_a_1571, ⟨reset_cert_a_1572, ⟨reset_cert_a_1573, ⟨reset_cert_a_1574, ⟨reset_cert_a_1575, ⟨reset_cert_a_1576, ⟨reset_cert_a_1577, ⟨reset_cert_a_1578, ⟨reset_cert_a_1579, ⟨reset_cert_a_1580, ⟨reset_cert_a_1581, ⟨reset_cert_a_1582, reset_cert_a_1583⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
