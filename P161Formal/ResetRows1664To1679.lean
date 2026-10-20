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

theorem reset_cert_a_1664 : resetParentTest 1664 = true := by
  decide

theorem reset_cert_a_1665 : resetParentTest 1665 = true := by
  decide

theorem reset_cert_a_1666 : resetParentTest 1666 = true := by
  decide

theorem reset_cert_a_1667 : resetParentTest 1667 = true := by
  decide

theorem reset_cert_a_1668 : resetParentTest 1668 = true := by
  decide

theorem reset_cert_a_1669 : resetParentTest 1669 = true := by
  decide

theorem reset_cert_a_1670 : resetParentTest 1670 = true := by
  decide

theorem reset_cert_a_1671 : resetParentTest 1671 = true := by
  decide

theorem reset_cert_a_1672 : resetParentTest 1672 = true := by
  decide

theorem reset_cert_a_1673 : resetParentTest 1673 = true := by
  decide

theorem reset_cert_a_1674 : resetParentTest 1674 = true := by
  decide

theorem reset_cert_a_1675 : resetParentTest 1675 = true := by
  decide

theorem reset_cert_a_1676 : resetParentTest 1676 = true := by
  decide

theorem reset_cert_a_1677 : resetParentTest 1677 = true := by
  decide

theorem reset_cert_a_1678 : resetParentTest 1678 = true := by
  decide

theorem reset_cert_a_1679 : resetParentTest 1679 = true := by
  decide

def resetParents1664To1679 : List ℕ := [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]

theorem reset_block_1664_to_1679 : resetParents1664To1679.all resetParentTest = true := by
  simp only [resetParents1664To1679, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1664, ⟨reset_cert_a_1665, ⟨reset_cert_a_1666, ⟨reset_cert_a_1667, ⟨reset_cert_a_1668, ⟨reset_cert_a_1669, ⟨reset_cert_a_1670, ⟨reset_cert_a_1671, ⟨reset_cert_a_1672, ⟨reset_cert_a_1673, ⟨reset_cert_a_1674, ⟨reset_cert_a_1675, ⟨reset_cert_a_1676, ⟨reset_cert_a_1677, ⟨reset_cert_a_1678, reset_cert_a_1679⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
