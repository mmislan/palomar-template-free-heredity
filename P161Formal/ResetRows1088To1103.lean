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

theorem reset_cert_a_1088 : resetParentTest 1088 = true := by
  decide

theorem reset_cert_a_1089 : resetParentTest 1089 = true := by
  decide

theorem reset_cert_a_1090 : resetParentTest 1090 = true := by
  decide

theorem reset_cert_a_1091 : resetParentTest 1091 = true := by
  decide

theorem reset_cert_a_1092 : resetParentTest 1092 = true := by
  decide

theorem reset_cert_a_1093 : resetParentTest 1093 = true := by
  decide

theorem reset_cert_a_1094 : resetParentTest 1094 = true := by
  decide

theorem reset_cert_a_1095 : resetParentTest 1095 = true := by
  decide

theorem reset_cert_a_1096 : resetParentTest 1096 = true := by
  decide

theorem reset_cert_a_1097 : resetParentTest 1097 = true := by
  decide

theorem reset_cert_a_1098 : resetParentTest 1098 = true := by
  decide

theorem reset_cert_a_1099 : resetParentTest 1099 = true := by
  decide

theorem reset_cert_a_1100 : resetParentTest 1100 = true := by
  decide

theorem reset_cert_a_1101 : resetParentTest 1101 = true := by
  decide

theorem reset_cert_a_1102 : resetParentTest 1102 = true := by
  decide

theorem reset_cert_a_1103 : resetParentTest 1103 = true := by
  decide

def resetParents1088To1103 : List ℕ := [1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103]

theorem reset_block_1088_to_1103 : resetParents1088To1103.all resetParentTest = true := by
  simp only [resetParents1088To1103, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1088, ⟨reset_cert_a_1089, ⟨reset_cert_a_1090, ⟨reset_cert_a_1091, ⟨reset_cert_a_1092, ⟨reset_cert_a_1093, ⟨reset_cert_a_1094, ⟨reset_cert_a_1095, ⟨reset_cert_a_1096, ⟨reset_cert_a_1097, ⟨reset_cert_a_1098, ⟨reset_cert_a_1099, ⟨reset_cert_a_1100, ⟨reset_cert_a_1101, ⟨reset_cert_a_1102, reset_cert_a_1103⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
