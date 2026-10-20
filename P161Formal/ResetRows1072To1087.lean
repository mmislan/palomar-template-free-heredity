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

theorem reset_cert_a_1072 : resetParentTest 1072 = true := by
  decide

theorem reset_cert_a_1073 : resetParentTest 1073 = true := by
  decide

theorem reset_cert_a_1074 : resetParentTest 1074 = true := by
  decide

theorem reset_cert_a_1075 : resetParentTest 1075 = true := by
  decide

theorem reset_cert_a_1076 : resetParentTest 1076 = true := by
  decide

theorem reset_cert_a_1077 : resetParentTest 1077 = true := by
  decide

theorem reset_cert_a_1078 : resetParentTest 1078 = true := by
  decide

theorem reset_cert_a_1079 : resetParentTest 1079 = true := by
  decide

theorem reset_cert_a_1080 : resetParentTest 1080 = true := by
  decide

theorem reset_cert_a_1081 : resetParentTest 1081 = true := by
  decide

theorem reset_cert_a_1082 : resetParentTest 1082 = true := by
  decide

theorem reset_cert_a_1083 : resetParentTest 1083 = true := by
  decide

theorem reset_cert_a_1084 : resetParentTest 1084 = true := by
  decide

theorem reset_cert_a_1085 : resetParentTest 1085 = true := by
  decide

theorem reset_cert_a_1086 : resetParentTest 1086 = true := by
  decide

theorem reset_cert_a_1087 : resetParentTest 1087 = true := by
  decide

def resetParents1072To1087 : List ℕ := [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]

theorem reset_block_1072_to_1087 : resetParents1072To1087.all resetParentTest = true := by
  simp only [resetParents1072To1087, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1072, ⟨reset_cert_a_1073, ⟨reset_cert_a_1074, ⟨reset_cert_a_1075, ⟨reset_cert_a_1076, ⟨reset_cert_a_1077, ⟨reset_cert_a_1078, ⟨reset_cert_a_1079, ⟨reset_cert_a_1080, ⟨reset_cert_a_1081, ⟨reset_cert_a_1082, ⟨reset_cert_a_1083, ⟨reset_cert_a_1084, ⟨reset_cert_a_1085, ⟨reset_cert_a_1086, reset_cert_a_1087⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
