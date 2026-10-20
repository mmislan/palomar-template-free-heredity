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

theorem reset_cert_a_1744 : resetParentTest 1744 = true := by
  decide

theorem reset_cert_a_1745 : resetParentTest 1745 = true := by
  decide

theorem reset_cert_a_1746 : resetParentTest 1746 = true := by
  decide

theorem reset_cert_a_1747 : resetParentTest 1747 = true := by
  decide

theorem reset_cert_a_1748 : resetParentTest 1748 = true := by
  decide

theorem reset_cert_a_1749 : resetParentTest 1749 = true := by
  decide

theorem reset_cert_a_1750 : resetParentTest 1750 = true := by
  decide

theorem reset_cert_a_1751 : resetParentTest 1751 = true := by
  decide

theorem reset_cert_a_1752 : resetParentTest 1752 = true := by
  decide

theorem reset_cert_a_1753 : resetParentTest 1753 = true := by
  decide

theorem reset_cert_a_1754 : resetParentTest 1754 = true := by
  decide

theorem reset_cert_a_1755 : resetParentTest 1755 = true := by
  decide

theorem reset_cert_a_1756 : resetParentTest 1756 = true := by
  decide

theorem reset_cert_a_1757 : resetParentTest 1757 = true := by
  decide

theorem reset_cert_a_1758 : resetParentTest 1758 = true := by
  decide

theorem reset_cert_a_1759 : resetParentTest 1759 = true := by
  decide

def resetParents1744To1759 : List ℕ := [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]

theorem reset_block_1744_to_1759 : resetParents1744To1759.all resetParentTest = true := by
  simp only [resetParents1744To1759, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1744, ⟨reset_cert_a_1745, ⟨reset_cert_a_1746, ⟨reset_cert_a_1747, ⟨reset_cert_a_1748, ⟨reset_cert_a_1749, ⟨reset_cert_a_1750, ⟨reset_cert_a_1751, ⟨reset_cert_a_1752, ⟨reset_cert_a_1753, ⟨reset_cert_a_1754, ⟨reset_cert_a_1755, ⟨reset_cert_a_1756, ⟨reset_cert_a_1757, ⟨reset_cert_a_1758, reset_cert_a_1759⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
