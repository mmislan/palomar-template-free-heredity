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

theorem reset_cert_a_1728 : resetParentTest 1728 = true := by
  decide

theorem reset_cert_a_1729 : resetParentTest 1729 = true := by
  decide

theorem reset_cert_a_1730 : resetParentTest 1730 = true := by
  decide

theorem reset_cert_a_1731 : resetParentTest 1731 = true := by
  decide

theorem reset_cert_a_1732 : resetParentTest 1732 = true := by
  decide

theorem reset_cert_a_1733 : resetParentTest 1733 = true := by
  decide

theorem reset_cert_a_1734 : resetParentTest 1734 = true := by
  decide

theorem reset_cert_a_1735 : resetParentTest 1735 = true := by
  decide

theorem reset_cert_a_1736 : resetParentTest 1736 = true := by
  decide

theorem reset_cert_a_1737 : resetParentTest 1737 = true := by
  decide

theorem reset_cert_a_1738 : resetParentTest 1738 = true := by
  decide

theorem reset_cert_a_1739 : resetParentTest 1739 = true := by
  decide

theorem reset_cert_a_1740 : resetParentTest 1740 = true := by
  decide

theorem reset_cert_a_1741 : resetParentTest 1741 = true := by
  decide

theorem reset_cert_a_1742 : resetParentTest 1742 = true := by
  decide

theorem reset_cert_a_1743 : resetParentTest 1743 = true := by
  decide

def resetParents1728To1743 : List ℕ := [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]

theorem reset_block_1728_to_1743 : resetParents1728To1743.all resetParentTest = true := by
  simp only [resetParents1728To1743, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1728, ⟨reset_cert_a_1729, ⟨reset_cert_a_1730, ⟨reset_cert_a_1731, ⟨reset_cert_a_1732, ⟨reset_cert_a_1733, ⟨reset_cert_a_1734, ⟨reset_cert_a_1735, ⟨reset_cert_a_1736, ⟨reset_cert_a_1737, ⟨reset_cert_a_1738, ⟨reset_cert_a_1739, ⟨reset_cert_a_1740, ⟨reset_cert_a_1741, ⟨reset_cert_a_1742, reset_cert_a_1743⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
