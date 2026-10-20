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

theorem reset_cert_a_1760 : resetParentTest 1760 = true := by
  decide

theorem reset_cert_a_1761 : resetParentTest 1761 = true := by
  decide

theorem reset_cert_a_1762 : resetParentTest 1762 = true := by
  decide

theorem reset_cert_a_1763 : resetParentTest 1763 = true := by
  decide

theorem reset_cert_a_1764 : resetParentTest 1764 = true := by
  decide

theorem reset_cert_a_1765 : resetParentTest 1765 = true := by
  decide

theorem reset_cert_a_1766 : resetParentTest 1766 = true := by
  decide

theorem reset_cert_a_1767 : resetParentTest 1767 = true := by
  decide

theorem reset_cert_a_1768 : resetParentTest 1768 = true := by
  decide

theorem reset_cert_a_1769 : resetParentTest 1769 = true := by
  decide

theorem reset_cert_a_1770 : resetParentTest 1770 = true := by
  decide

theorem reset_cert_a_1771 : resetParentTest 1771 = true := by
  decide

theorem reset_cert_a_1772 : resetParentTest 1772 = true := by
  decide

theorem reset_cert_a_1773 : resetParentTest 1773 = true := by
  decide

theorem reset_cert_a_1774 : resetParentTest 1774 = true := by
  decide

theorem reset_cert_a_1775 : resetParentTest 1775 = true := by
  decide

def resetParents1760To1775 : List ℕ := [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]

theorem reset_block_1760_to_1775 : resetParents1760To1775.all resetParentTest = true := by
  simp only [resetParents1760To1775, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1760, ⟨reset_cert_a_1761, ⟨reset_cert_a_1762, ⟨reset_cert_a_1763, ⟨reset_cert_a_1764, ⟨reset_cert_a_1765, ⟨reset_cert_a_1766, ⟨reset_cert_a_1767, ⟨reset_cert_a_1768, ⟨reset_cert_a_1769, ⟨reset_cert_a_1770, ⟨reset_cert_a_1771, ⟨reset_cert_a_1772, ⟨reset_cert_a_1773, ⟨reset_cert_a_1774, reset_cert_a_1775⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
