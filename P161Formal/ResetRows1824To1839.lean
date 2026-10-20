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

theorem reset_cert_a_1824 : resetParentTest 1824 = true := by
  decide

theorem reset_cert_a_1825 : resetParentTest 1825 = true := by
  decide

theorem reset_cert_a_1826 : resetParentTest 1826 = true := by
  decide

theorem reset_cert_a_1827 : resetParentTest 1827 = true := by
  decide

theorem reset_cert_a_1828 : resetParentTest 1828 = true := by
  decide

theorem reset_cert_a_1829 : resetParentTest 1829 = true := by
  decide

theorem reset_cert_a_1830 : resetParentTest 1830 = true := by
  decide

theorem reset_cert_a_1831 : resetParentTest 1831 = true := by
  decide

theorem reset_cert_a_1832 : resetParentTest 1832 = true := by
  decide

theorem reset_cert_a_1833 : resetParentTest 1833 = true := by
  decide

theorem reset_cert_a_1834 : resetParentTest 1834 = true := by
  decide

theorem reset_cert_a_1835 : resetParentTest 1835 = true := by
  decide

theorem reset_cert_a_1836 : resetParentTest 1836 = true := by
  decide

theorem reset_cert_a_1837 : resetParentTest 1837 = true := by
  decide

theorem reset_cert_a_1838 : resetParentTest 1838 = true := by
  decide

theorem reset_cert_a_1839 : resetParentTest 1839 = true := by
  decide

def resetParents1824To1839 : List ℕ := [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]

theorem reset_block_1824_to_1839 : resetParents1824To1839.all resetParentTest = true := by
  simp only [resetParents1824To1839, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1824, ⟨reset_cert_a_1825, ⟨reset_cert_a_1826, ⟨reset_cert_a_1827, ⟨reset_cert_a_1828, ⟨reset_cert_a_1829, ⟨reset_cert_a_1830, ⟨reset_cert_a_1831, ⟨reset_cert_a_1832, ⟨reset_cert_a_1833, ⟨reset_cert_a_1834, ⟨reset_cert_a_1835, ⟨reset_cert_a_1836, ⟨reset_cert_a_1837, ⟨reset_cert_a_1838, reset_cert_a_1839⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
