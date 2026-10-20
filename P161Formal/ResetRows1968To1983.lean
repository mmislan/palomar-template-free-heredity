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

theorem reset_cert_a_1968 : resetParentTest 1968 = true := by
  decide

theorem reset_cert_a_1969 : resetParentTest 1969 = true := by
  decide

theorem reset_cert_a_1970 : resetParentTest 1970 = true := by
  decide

theorem reset_cert_a_1971 : resetParentTest 1971 = true := by
  decide

theorem reset_cert_a_1972 : resetParentTest 1972 = true := by
  decide

theorem reset_cert_a_1973 : resetParentTest 1973 = true := by
  decide

theorem reset_cert_a_1974 : resetParentTest 1974 = true := by
  decide

theorem reset_cert_a_1975 : resetParentTest 1975 = true := by
  decide

theorem reset_cert_a_1976 : resetParentTest 1976 = true := by
  decide

theorem reset_cert_a_1977 : resetParentTest 1977 = true := by
  decide

theorem reset_cert_a_1978 : resetParentTest 1978 = true := by
  decide

theorem reset_cert_a_1979 : resetParentTest 1979 = true := by
  decide

theorem reset_cert_a_1980 : resetParentTest 1980 = true := by
  decide

theorem reset_cert_a_1981 : resetParentTest 1981 = true := by
  decide

theorem reset_cert_a_1982 : resetParentTest 1982 = true := by
  decide

theorem reset_cert_a_1983 : resetParentTest 1983 = true := by
  decide

def resetParents1968To1983 : List ℕ := [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]

theorem reset_block_1968_to_1983 : resetParents1968To1983.all resetParentTest = true := by
  simp only [resetParents1968To1983, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1968, ⟨reset_cert_a_1969, ⟨reset_cert_a_1970, ⟨reset_cert_a_1971, ⟨reset_cert_a_1972, ⟨reset_cert_a_1973, ⟨reset_cert_a_1974, ⟨reset_cert_a_1975, ⟨reset_cert_a_1976, ⟨reset_cert_a_1977, ⟨reset_cert_a_1978, ⟨reset_cert_a_1979, ⟨reset_cert_a_1980, ⟨reset_cert_a_1981, ⟨reset_cert_a_1982, reset_cert_a_1983⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
