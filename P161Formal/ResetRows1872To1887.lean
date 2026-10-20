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

theorem reset_cert_a_1872 : resetParentTest 1872 = true := by
  decide

theorem reset_cert_a_1873 : resetParentTest 1873 = true := by
  decide

theorem reset_cert_a_1874 : resetParentTest 1874 = true := by
  decide

theorem reset_cert_a_1875 : resetParentTest 1875 = true := by
  decide

theorem reset_cert_a_1876 : resetParentTest 1876 = true := by
  decide

theorem reset_cert_a_1877 : resetParentTest 1877 = true := by
  decide

theorem reset_cert_a_1878 : resetParentTest 1878 = true := by
  decide

theorem reset_cert_a_1879 : resetParentTest 1879 = true := by
  decide

theorem reset_cert_a_1880 : resetParentTest 1880 = true := by
  decide

theorem reset_cert_a_1881 : resetParentTest 1881 = true := by
  decide

theorem reset_cert_a_1882 : resetParentTest 1882 = true := by
  decide

theorem reset_cert_a_1883 : resetParentTest 1883 = true := by
  decide

theorem reset_cert_a_1884 : resetParentTest 1884 = true := by
  decide

theorem reset_cert_a_1885 : resetParentTest 1885 = true := by
  decide

theorem reset_cert_a_1886 : resetParentTest 1886 = true := by
  decide

theorem reset_cert_a_1887 : resetParentTest 1887 = true := by
  decide

def resetParents1872To1887 : List ℕ := [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]

theorem reset_block_1872_to_1887 : resetParents1872To1887.all resetParentTest = true := by
  simp only [resetParents1872To1887, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1872, ⟨reset_cert_a_1873, ⟨reset_cert_a_1874, ⟨reset_cert_a_1875, ⟨reset_cert_a_1876, ⟨reset_cert_a_1877, ⟨reset_cert_a_1878, ⟨reset_cert_a_1879, ⟨reset_cert_a_1880, ⟨reset_cert_a_1881, ⟨reset_cert_a_1882, ⟨reset_cert_a_1883, ⟨reset_cert_a_1884, ⟨reset_cert_a_1885, ⟨reset_cert_a_1886, reset_cert_a_1887⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
