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

theorem reset_cert_a_1056 : resetParentTest 1056 = true := by
  decide

theorem reset_cert_a_1057 : resetParentTest 1057 = true := by
  decide

theorem reset_cert_a_1058 : resetParentTest 1058 = true := by
  decide

theorem reset_cert_a_1059 : resetParentTest 1059 = true := by
  decide

theorem reset_cert_a_1060 : resetParentTest 1060 = true := by
  decide

theorem reset_cert_a_1061 : resetParentTest 1061 = true := by
  decide

theorem reset_cert_a_1062 : resetParentTest 1062 = true := by
  decide

theorem reset_cert_a_1063 : resetParentTest 1063 = true := by
  decide

theorem reset_cert_a_1064 : resetParentTest 1064 = true := by
  decide

theorem reset_cert_a_1065 : resetParentTest 1065 = true := by
  decide

theorem reset_cert_a_1066 : resetParentTest 1066 = true := by
  decide

theorem reset_cert_a_1067 : resetParentTest 1067 = true := by
  decide

theorem reset_cert_a_1068 : resetParentTest 1068 = true := by
  decide

theorem reset_cert_a_1069 : resetParentTest 1069 = true := by
  decide

theorem reset_cert_a_1070 : resetParentTest 1070 = true := by
  decide

theorem reset_cert_a_1071 : resetParentTest 1071 = true := by
  decide

def resetParents1056To1071 : List ℕ := [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]

theorem reset_block_1056_to_1071 : resetParents1056To1071.all resetParentTest = true := by
  simp only [resetParents1056To1071, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1056, ⟨reset_cert_a_1057, ⟨reset_cert_a_1058, ⟨reset_cert_a_1059, ⟨reset_cert_a_1060, ⟨reset_cert_a_1061, ⟨reset_cert_a_1062, ⟨reset_cert_a_1063, ⟨reset_cert_a_1064, ⟨reset_cert_a_1065, ⟨reset_cert_a_1066, ⟨reset_cert_a_1067, ⟨reset_cert_a_1068, ⟨reset_cert_a_1069, ⟨reset_cert_a_1070, reset_cert_a_1071⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
