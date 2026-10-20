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

theorem reset_cert_a_1792 : resetParentTest 1792 = true := by
  decide

theorem reset_cert_a_1793 : resetParentTest 1793 = true := by
  decide

theorem reset_cert_a_1794 : resetParentTest 1794 = true := by
  decide

theorem reset_cert_a_1795 : resetParentTest 1795 = true := by
  decide

theorem reset_cert_a_1796 : resetParentTest 1796 = true := by
  decide

theorem reset_cert_a_1797 : resetParentTest 1797 = true := by
  decide

theorem reset_cert_a_1798 : resetParentTest 1798 = true := by
  decide

theorem reset_cert_a_1799 : resetParentTest 1799 = true := by
  decide

theorem reset_cert_a_1800 : resetParentTest 1800 = true := by
  decide

theorem reset_cert_a_1801 : resetParentTest 1801 = true := by
  decide

theorem reset_cert_a_1802 : resetParentTest 1802 = true := by
  decide

theorem reset_cert_a_1803 : resetParentTest 1803 = true := by
  decide

theorem reset_cert_a_1804 : resetParentTest 1804 = true := by
  decide

theorem reset_cert_a_1805 : resetParentTest 1805 = true := by
  decide

theorem reset_cert_a_1806 : resetParentTest 1806 = true := by
  decide

theorem reset_cert_a_1807 : resetParentTest 1807 = true := by
  decide

def resetParents1792To1807 : List ℕ := [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]

theorem reset_block_1792_to_1807 : resetParents1792To1807.all resetParentTest = true := by
  simp only [resetParents1792To1807, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1792, ⟨reset_cert_a_1793, ⟨reset_cert_a_1794, ⟨reset_cert_a_1795, ⟨reset_cert_a_1796, ⟨reset_cert_a_1797, ⟨reset_cert_a_1798, ⟨reset_cert_a_1799, ⟨reset_cert_a_1800, ⟨reset_cert_a_1801, ⟨reset_cert_a_1802, ⟨reset_cert_a_1803, ⟨reset_cert_a_1804, ⟨reset_cert_a_1805, ⟨reset_cert_a_1806, reset_cert_a_1807⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
