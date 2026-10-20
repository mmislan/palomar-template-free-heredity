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

theorem reset_cert_a_1632 : resetParentTest 1632 = true := by
  decide

theorem reset_cert_a_1633 : resetParentTest 1633 = true := by
  decide

theorem reset_cert_a_1634 : resetParentTest 1634 = true := by
  decide

theorem reset_cert_a_1635 : resetParentTest 1635 = true := by
  decide

theorem reset_cert_a_1636 : resetParentTest 1636 = true := by
  decide

theorem reset_cert_a_1637 : resetParentTest 1637 = true := by
  decide

theorem reset_cert_a_1638 : resetParentTest 1638 = true := by
  decide

theorem reset_cert_a_1639 : resetParentTest 1639 = true := by
  decide

theorem reset_cert_a_1640 : resetParentTest 1640 = true := by
  decide

theorem reset_cert_a_1641 : resetParentTest 1641 = true := by
  decide

theorem reset_cert_a_1642 : resetParentTest 1642 = true := by
  decide

theorem reset_cert_a_1643 : resetParentTest 1643 = true := by
  decide

theorem reset_cert_a_1644 : resetParentTest 1644 = true := by
  decide

theorem reset_cert_a_1645 : resetParentTest 1645 = true := by
  decide

theorem reset_cert_a_1646 : resetParentTest 1646 = true := by
  decide

theorem reset_cert_a_1647 : resetParentTest 1647 = true := by
  decide

def resetParents1632To1647 : List ℕ := [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]

theorem reset_block_1632_to_1647 : resetParents1632To1647.all resetParentTest = true := by
  simp only [resetParents1632To1647, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1632, ⟨reset_cert_a_1633, ⟨reset_cert_a_1634, ⟨reset_cert_a_1635, ⟨reset_cert_a_1636, ⟨reset_cert_a_1637, ⟨reset_cert_a_1638, ⟨reset_cert_a_1639, ⟨reset_cert_a_1640, ⟨reset_cert_a_1641, ⟨reset_cert_a_1642, ⟨reset_cert_a_1643, ⟨reset_cert_a_1644, ⟨reset_cert_a_1645, ⟨reset_cert_a_1646, reset_cert_a_1647⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
