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

theorem reset_cert_a_1168 : resetParentTest 1168 = true := by
  decide

theorem reset_cert_a_1169 : resetParentTest 1169 = true := by
  decide

theorem reset_cert_a_1170 : resetParentTest 1170 = true := by
  decide

theorem reset_cert_a_1171 : resetParentTest 1171 = true := by
  decide

theorem reset_cert_a_1172 : resetParentTest 1172 = true := by
  decide

theorem reset_cert_a_1173 : resetParentTest 1173 = true := by
  decide

theorem reset_cert_a_1174 : resetParentTest 1174 = true := by
  decide

theorem reset_cert_a_1175 : resetParentTest 1175 = true := by
  decide

theorem reset_cert_a_1176 : resetParentTest 1176 = true := by
  decide

theorem reset_cert_a_1177 : resetParentTest 1177 = true := by
  decide

theorem reset_cert_a_1178 : resetParentTest 1178 = true := by
  decide

theorem reset_cert_a_1179 : resetParentTest 1179 = true := by
  decide

theorem reset_cert_a_1180 : resetParentTest 1180 = true := by
  decide

theorem reset_cert_a_1181 : resetParentTest 1181 = true := by
  decide

theorem reset_cert_a_1182 : resetParentTest 1182 = true := by
  decide

theorem reset_cert_a_1183 : resetParentTest 1183 = true := by
  decide

def resetParents1168To1183 : List ℕ := [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]

theorem reset_block_1168_to_1183 : resetParents1168To1183.all resetParentTest = true := by
  simp only [resetParents1168To1183, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1168, ⟨reset_cert_a_1169, ⟨reset_cert_a_1170, ⟨reset_cert_a_1171, ⟨reset_cert_a_1172, ⟨reset_cert_a_1173, ⟨reset_cert_a_1174, ⟨reset_cert_a_1175, ⟨reset_cert_a_1176, ⟨reset_cert_a_1177, ⟨reset_cert_a_1178, ⟨reset_cert_a_1179, ⟨reset_cert_a_1180, ⟨reset_cert_a_1181, ⟨reset_cert_a_1182, reset_cert_a_1183⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
