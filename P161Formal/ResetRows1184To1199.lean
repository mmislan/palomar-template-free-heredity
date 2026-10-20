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

theorem reset_cert_a_1184 : resetParentTest 1184 = true := by
  decide

theorem reset_cert_a_1185 : resetParentTest 1185 = true := by
  decide

theorem reset_cert_a_1186 : resetParentTest 1186 = true := by
  decide

theorem reset_cert_a_1187 : resetParentTest 1187 = true := by
  decide

theorem reset_cert_a_1188 : resetParentTest 1188 = true := by
  decide

theorem reset_cert_a_1189 : resetParentTest 1189 = true := by
  decide

theorem reset_cert_a_1190 : resetParentTest 1190 = true := by
  decide

theorem reset_cert_a_1191 : resetParentTest 1191 = true := by
  decide

theorem reset_cert_a_1192 : resetParentTest 1192 = true := by
  decide

theorem reset_cert_a_1193 : resetParentTest 1193 = true := by
  decide

theorem reset_cert_a_1194 : resetParentTest 1194 = true := by
  decide

theorem reset_cert_a_1195 : resetParentTest 1195 = true := by
  decide

theorem reset_cert_a_1196 : resetParentTest 1196 = true := by
  decide

theorem reset_cert_a_1197 : resetParentTest 1197 = true := by
  decide

theorem reset_cert_a_1198 : resetParentTest 1198 = true := by
  decide

theorem reset_cert_a_1199 : resetParentTest 1199 = true := by
  decide

def resetParents1184To1199 : List ℕ := [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]

theorem reset_block_1184_to_1199 : resetParents1184To1199.all resetParentTest = true := by
  simp only [resetParents1184To1199, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1184, ⟨reset_cert_a_1185, ⟨reset_cert_a_1186, ⟨reset_cert_a_1187, ⟨reset_cert_a_1188, ⟨reset_cert_a_1189, ⟨reset_cert_a_1190, ⟨reset_cert_a_1191, ⟨reset_cert_a_1192, ⟨reset_cert_a_1193, ⟨reset_cert_a_1194, ⟨reset_cert_a_1195, ⟨reset_cert_a_1196, ⟨reset_cert_a_1197, ⟨reset_cert_a_1198, reset_cert_a_1199⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
