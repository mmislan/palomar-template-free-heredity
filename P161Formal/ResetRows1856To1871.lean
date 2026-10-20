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

theorem reset_cert_a_1856 : resetParentTest 1856 = true := by
  decide

theorem reset_cert_a_1857 : resetParentTest 1857 = true := by
  decide

theorem reset_cert_a_1858 : resetParentTest 1858 = true := by
  decide

theorem reset_cert_a_1859 : resetParentTest 1859 = true := by
  decide

theorem reset_cert_a_1860 : resetParentTest 1860 = true := by
  decide

theorem reset_cert_a_1861 : resetParentTest 1861 = true := by
  decide

theorem reset_cert_a_1862 : resetParentTest 1862 = true := by
  decide

theorem reset_cert_a_1863 : resetParentTest 1863 = true := by
  decide

theorem reset_cert_a_1864 : resetParentTest 1864 = true := by
  decide

theorem reset_cert_a_1865 : resetParentTest 1865 = true := by
  decide

theorem reset_cert_a_1866 : resetParentTest 1866 = true := by
  decide

theorem reset_cert_a_1867 : resetParentTest 1867 = true := by
  decide

theorem reset_cert_a_1868 : resetParentTest 1868 = true := by
  decide

theorem reset_cert_a_1869 : resetParentTest 1869 = true := by
  decide

theorem reset_cert_a_1870 : resetParentTest 1870 = true := by
  decide

theorem reset_cert_a_1871 : resetParentTest 1871 = true := by
  decide

def resetParents1856To1871 : List ℕ := [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]

theorem reset_block_1856_to_1871 : resetParents1856To1871.all resetParentTest = true := by
  simp only [resetParents1856To1871, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1856, ⟨reset_cert_a_1857, ⟨reset_cert_a_1858, ⟨reset_cert_a_1859, ⟨reset_cert_a_1860, ⟨reset_cert_a_1861, ⟨reset_cert_a_1862, ⟨reset_cert_a_1863, ⟨reset_cert_a_1864, ⟨reset_cert_a_1865, ⟨reset_cert_a_1866, ⟨reset_cert_a_1867, ⟨reset_cert_a_1868, ⟨reset_cert_a_1869, ⟨reset_cert_a_1870, reset_cert_a_1871⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
