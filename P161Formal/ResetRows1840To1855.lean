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

theorem reset_cert_a_1840 : resetParentTest 1840 = true := by
  decide

theorem reset_cert_a_1841 : resetParentTest 1841 = true := by
  decide

theorem reset_cert_a_1842 : resetParentTest 1842 = true := by
  decide

theorem reset_cert_a_1843 : resetParentTest 1843 = true := by
  decide

theorem reset_cert_a_1844 : resetParentTest 1844 = true := by
  decide

theorem reset_cert_a_1845 : resetParentTest 1845 = true := by
  decide

theorem reset_cert_a_1846 : resetParentTest 1846 = true := by
  decide

theorem reset_cert_a_1847 : resetParentTest 1847 = true := by
  decide

theorem reset_cert_a_1848 : resetParentTest 1848 = true := by
  decide

theorem reset_cert_a_1849 : resetParentTest 1849 = true := by
  decide

theorem reset_cert_a_1850 : resetParentTest 1850 = true := by
  decide

theorem reset_cert_a_1851 : resetParentTest 1851 = true := by
  decide

theorem reset_cert_a_1852 : resetParentTest 1852 = true := by
  decide

theorem reset_cert_a_1853 : resetParentTest 1853 = true := by
  decide

theorem reset_cert_a_1854 : resetParentTest 1854 = true := by
  decide

theorem reset_cert_a_1855 : resetParentTest 1855 = true := by
  decide

def resetParents1840To1855 : List ℕ := [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]

theorem reset_block_1840_to_1855 : resetParents1840To1855.all resetParentTest = true := by
  simp only [resetParents1840To1855, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1840, ⟨reset_cert_a_1841, ⟨reset_cert_a_1842, ⟨reset_cert_a_1843, ⟨reset_cert_a_1844, ⟨reset_cert_a_1845, ⟨reset_cert_a_1846, ⟨reset_cert_a_1847, ⟨reset_cert_a_1848, ⟨reset_cert_a_1849, ⟨reset_cert_a_1850, ⟨reset_cert_a_1851, ⟨reset_cert_a_1852, ⟨reset_cert_a_1853, ⟨reset_cert_a_1854, reset_cert_a_1855⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
