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

theorem reset_cert_a_1136 : resetParentTest 1136 = true := by
  decide

theorem reset_cert_a_1137 : resetParentTest 1137 = true := by
  decide

theorem reset_cert_a_1138 : resetParentTest 1138 = true := by
  decide

theorem reset_cert_a_1139 : resetParentTest 1139 = true := by
  decide

theorem reset_cert_a_1140 : resetParentTest 1140 = true := by
  decide

theorem reset_cert_a_1141 : resetParentTest 1141 = true := by
  decide

theorem reset_cert_a_1142 : resetParentTest 1142 = true := by
  decide

theorem reset_cert_a_1143 : resetParentTest 1143 = true := by
  decide

theorem reset_cert_a_1144 : resetParentTest 1144 = true := by
  decide

theorem reset_cert_a_1145 : resetParentTest 1145 = true := by
  decide

theorem reset_cert_a_1146 : resetParentTest 1146 = true := by
  decide

theorem reset_cert_a_1147 : resetParentTest 1147 = true := by
  decide

theorem reset_cert_a_1148 : resetParentTest 1148 = true := by
  decide

theorem reset_cert_a_1149 : resetParentTest 1149 = true := by
  decide

theorem reset_cert_a_1150 : resetParentTest 1150 = true := by
  decide

theorem reset_cert_a_1151 : resetParentTest 1151 = true := by
  decide

def resetParents1136To1151 : List ℕ := [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]

theorem reset_block_1136_to_1151 : resetParents1136To1151.all resetParentTest = true := by
  simp only [resetParents1136To1151, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1136, ⟨reset_cert_a_1137, ⟨reset_cert_a_1138, ⟨reset_cert_a_1139, ⟨reset_cert_a_1140, ⟨reset_cert_a_1141, ⟨reset_cert_a_1142, ⟨reset_cert_a_1143, ⟨reset_cert_a_1144, ⟨reset_cert_a_1145, ⟨reset_cert_a_1146, ⟨reset_cert_a_1147, ⟨reset_cert_a_1148, ⟨reset_cert_a_1149, ⟨reset_cert_a_1150, reset_cert_a_1151⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
