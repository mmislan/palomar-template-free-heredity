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

theorem reset_cert_a_1888 : resetParentTest 1888 = true := by
  decide

theorem reset_cert_a_1889 : resetParentTest 1889 = true := by
  decide

theorem reset_cert_a_1890 : resetParentTest 1890 = true := by
  decide

theorem reset_cert_a_1891 : resetParentTest 1891 = true := by
  decide

theorem reset_cert_a_1892 : resetParentTest 1892 = true := by
  decide

theorem reset_cert_a_1893 : resetParentTest 1893 = true := by
  decide

theorem reset_cert_a_1894 : resetParentTest 1894 = true := by
  decide

theorem reset_cert_a_1895 : resetParentTest 1895 = true := by
  decide

theorem reset_cert_a_1896 : resetParentTest 1896 = true := by
  decide

theorem reset_cert_a_1897 : resetParentTest 1897 = true := by
  decide

theorem reset_cert_a_1898 : resetParentTest 1898 = true := by
  decide

theorem reset_cert_a_1899 : resetParentTest 1899 = true := by
  decide

theorem reset_cert_a_1900 : resetParentTest 1900 = true := by
  decide

theorem reset_cert_a_1901 : resetParentTest 1901 = true := by
  decide

theorem reset_cert_a_1902 : resetParentTest 1902 = true := by
  decide

theorem reset_cert_a_1903 : resetParentTest 1903 = true := by
  decide

def resetParents1888To1903 : List ℕ := [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]

theorem reset_block_1888_to_1903 : resetParents1888To1903.all resetParentTest = true := by
  simp only [resetParents1888To1903, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1888, ⟨reset_cert_a_1889, ⟨reset_cert_a_1890, ⟨reset_cert_a_1891, ⟨reset_cert_a_1892, ⟨reset_cert_a_1893, ⟨reset_cert_a_1894, ⟨reset_cert_a_1895, ⟨reset_cert_a_1896, ⟨reset_cert_a_1897, ⟨reset_cert_a_1898, ⟨reset_cert_a_1899, ⟨reset_cert_a_1900, ⟨reset_cert_a_1901, ⟨reset_cert_a_1902, reset_cert_a_1903⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
