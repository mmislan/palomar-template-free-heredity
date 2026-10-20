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

theorem reset_cert_a_1680 : resetParentTest 1680 = true := by
  decide

theorem reset_cert_a_1681 : resetParentTest 1681 = true := by
  decide

theorem reset_cert_a_1682 : resetParentTest 1682 = true := by
  decide

theorem reset_cert_a_1683 : resetParentTest 1683 = true := by
  decide

theorem reset_cert_a_1684 : resetParentTest 1684 = true := by
  decide

theorem reset_cert_a_1685 : resetParentTest 1685 = true := by
  decide

theorem reset_cert_a_1686 : resetParentTest 1686 = true := by
  decide

theorem reset_cert_a_1687 : resetParentTest 1687 = true := by
  decide

theorem reset_cert_a_1688 : resetParentTest 1688 = true := by
  decide

theorem reset_cert_a_1689 : resetParentTest 1689 = true := by
  decide

theorem reset_cert_a_1690 : resetParentTest 1690 = true := by
  decide

theorem reset_cert_a_1691 : resetParentTest 1691 = true := by
  decide

theorem reset_cert_a_1692 : resetParentTest 1692 = true := by
  decide

theorem reset_cert_a_1693 : resetParentTest 1693 = true := by
  decide

theorem reset_cert_a_1694 : resetParentTest 1694 = true := by
  decide

theorem reset_cert_a_1695 : resetParentTest 1695 = true := by
  decide

def resetParents1680To1695 : List ℕ := [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]

theorem reset_block_1680_to_1695 : resetParents1680To1695.all resetParentTest = true := by
  simp only [resetParents1680To1695, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1680, ⟨reset_cert_a_1681, ⟨reset_cert_a_1682, ⟨reset_cert_a_1683, ⟨reset_cert_a_1684, ⟨reset_cert_a_1685, ⟨reset_cert_a_1686, ⟨reset_cert_a_1687, ⟨reset_cert_a_1688, ⟨reset_cert_a_1689, ⟨reset_cert_a_1690, ⟨reset_cert_a_1691, ⟨reset_cert_a_1692, ⟨reset_cert_a_1693, ⟨reset_cert_a_1694, reset_cert_a_1695⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
