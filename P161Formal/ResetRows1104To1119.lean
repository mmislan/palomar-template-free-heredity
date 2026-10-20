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

theorem reset_cert_a_1104 : resetParentTest 1104 = true := by
  decide

theorem reset_cert_a_1105 : resetParentTest 1105 = true := by
  decide

theorem reset_cert_a_1106 : resetParentTest 1106 = true := by
  decide

theorem reset_cert_a_1107 : resetParentTest 1107 = true := by
  decide

theorem reset_cert_a_1108 : resetParentTest 1108 = true := by
  decide

theorem reset_cert_a_1109 : resetParentTest 1109 = true := by
  decide

theorem reset_cert_a_1110 : resetParentTest 1110 = true := by
  decide

theorem reset_cert_a_1111 : resetParentTest 1111 = true := by
  decide

theorem reset_cert_a_1112 : resetParentTest 1112 = true := by
  decide

theorem reset_cert_a_1113 : resetParentTest 1113 = true := by
  decide

theorem reset_cert_a_1114 : resetParentTest 1114 = true := by
  decide

theorem reset_cert_a_1115 : resetParentTest 1115 = true := by
  decide

theorem reset_cert_a_1116 : resetParentTest 1116 = true := by
  decide

theorem reset_cert_a_1117 : resetParentTest 1117 = true := by
  decide

theorem reset_cert_a_1118 : resetParentTest 1118 = true := by
  decide

theorem reset_cert_a_1119 : resetParentTest 1119 = true := by
  decide

def resetParents1104To1119 : List ℕ := [1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119]

theorem reset_block_1104_to_1119 : resetParents1104To1119.all resetParentTest = true := by
  simp only [resetParents1104To1119, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1104, ⟨reset_cert_a_1105, ⟨reset_cert_a_1106, ⟨reset_cert_a_1107, ⟨reset_cert_a_1108, ⟨reset_cert_a_1109, ⟨reset_cert_a_1110, ⟨reset_cert_a_1111, ⟨reset_cert_a_1112, ⟨reset_cert_a_1113, ⟨reset_cert_a_1114, ⟨reset_cert_a_1115, ⟨reset_cert_a_1116, ⟨reset_cert_a_1117, ⟨reset_cert_a_1118, reset_cert_a_1119⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
