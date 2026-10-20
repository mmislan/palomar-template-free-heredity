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

theorem reset_cert_a_2032 : resetParentTest 2032 = true := by
  decide

theorem reset_cert_a_2033 : resetParentTest 2033 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2033
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2034 : resetParentTest 2034 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2034
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2035 : resetParentTest 2035 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2035
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2036 : resetParentTest 2036 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2036
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2037 : resetParentTest 2037 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2037
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2038 : resetParentTest 2038 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2038
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2039 : resetParentTest 2039 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2039
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2040 : resetParentTest 2040 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2040
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2041 : resetParentTest 2041 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2041
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2042 : resetParentTest 2042 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2042
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2043 : resetParentTest 2043 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2043
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2044 : resetParentTest 2044 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2044
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2045 : resetParentTest 2045 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2045
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2046 : resetParentTest 2046 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2046
  simp [resetParentTest, g0, g1]

theorem reset_cert_a_2047 : resetParentTest 2047 = true := by
  obtain ⟨g0, g1⟩ := separate_reset_2047
  simp [resetParentTest, g0, g1]

def resetParents2032To2047 : List ℕ := [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]

theorem reset_block_2032_to_2047 : resetParents2032To2047.all resetParentTest = true := by
  simp only [resetParents2032To2047, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_2032, ⟨reset_cert_a_2033, ⟨reset_cert_a_2034, ⟨reset_cert_a_2035, ⟨reset_cert_a_2036, ⟨reset_cert_a_2037, ⟨reset_cert_a_2038, ⟨reset_cert_a_2039, ⟨reset_cert_a_2040, ⟨reset_cert_a_2041, ⟨reset_cert_a_2042, ⟨reset_cert_a_2043, ⟨reset_cert_a_2044, ⟨reset_cert_a_2045, ⟨reset_cert_a_2046, reset_cert_a_2047⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
