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

theorem reset_cert_a_1808 : resetParentTest 1808 = true := by
  decide

theorem reset_cert_a_1809 : resetParentTest 1809 = true := by
  decide

theorem reset_cert_a_1810 : resetParentTest 1810 = true := by
  decide

theorem reset_cert_a_1811 : resetParentTest 1811 = true := by
  decide

theorem reset_cert_a_1812 : resetParentTest 1812 = true := by
  decide

theorem reset_cert_a_1813 : resetParentTest 1813 = true := by
  decide

theorem reset_cert_a_1814 : resetParentTest 1814 = true := by
  decide

theorem reset_cert_a_1815 : resetParentTest 1815 = true := by
  decide

theorem reset_cert_a_1816 : resetParentTest 1816 = true := by
  decide

theorem reset_cert_a_1817 : resetParentTest 1817 = true := by
  decide

theorem reset_cert_a_1818 : resetParentTest 1818 = true := by
  decide

theorem reset_cert_a_1819 : resetParentTest 1819 = true := by
  decide

theorem reset_cert_a_1820 : resetParentTest 1820 = true := by
  decide

theorem reset_cert_a_1821 : resetParentTest 1821 = true := by
  decide

theorem reset_cert_a_1822 : resetParentTest 1822 = true := by
  decide

theorem reset_cert_a_1823 : resetParentTest 1823 = true := by
  decide

def resetParents1808To1823 : List ℕ := [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]

theorem reset_block_1808_to_1823 : resetParents1808To1823.all resetParentTest = true := by
  simp only [resetParents1808To1823, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1808, ⟨reset_cert_a_1809, ⟨reset_cert_a_1810, ⟨reset_cert_a_1811, ⟨reset_cert_a_1812, ⟨reset_cert_a_1813, ⟨reset_cert_a_1814, ⟨reset_cert_a_1815, ⟨reset_cert_a_1816, ⟨reset_cert_a_1817, ⟨reset_cert_a_1818, ⟨reset_cert_a_1819, ⟨reset_cert_a_1820, ⟨reset_cert_a_1821, ⟨reset_cert_a_1822, reset_cert_a_1823⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
