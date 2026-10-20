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

theorem reset_cert_a_1216 : resetParentTest 1216 = true := by
  decide

theorem reset_cert_a_1217 : resetParentTest 1217 = true := by
  decide

theorem reset_cert_a_1218 : resetParentTest 1218 = true := by
  decide

theorem reset_cert_a_1219 : resetParentTest 1219 = true := by
  decide

theorem reset_cert_a_1220 : resetParentTest 1220 = true := by
  decide

theorem reset_cert_a_1221 : resetParentTest 1221 = true := by
  decide

theorem reset_cert_a_1222 : resetParentTest 1222 = true := by
  decide

theorem reset_cert_a_1223 : resetParentTest 1223 = true := by
  decide

theorem reset_cert_a_1224 : resetParentTest 1224 = true := by
  decide

theorem reset_cert_a_1225 : resetParentTest 1225 = true := by
  decide

theorem reset_cert_a_1226 : resetParentTest 1226 = true := by
  decide

theorem reset_cert_a_1227 : resetParentTest 1227 = true := by
  decide

theorem reset_cert_a_1228 : resetParentTest 1228 = true := by
  decide

theorem reset_cert_a_1229 : resetParentTest 1229 = true := by
  decide

theorem reset_cert_a_1230 : resetParentTest 1230 = true := by
  decide

theorem reset_cert_a_1231 : resetParentTest 1231 = true := by
  decide

def resetParents1216To1231 : List ℕ := [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]

theorem reset_block_1216_to_1231 : resetParents1216To1231.all resetParentTest = true := by
  simp only [resetParents1216To1231, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1216, ⟨reset_cert_a_1217, ⟨reset_cert_a_1218, ⟨reset_cert_a_1219, ⟨reset_cert_a_1220, ⟨reset_cert_a_1221, ⟨reset_cert_a_1222, ⟨reset_cert_a_1223, ⟨reset_cert_a_1224, ⟨reset_cert_a_1225, ⟨reset_cert_a_1226, ⟨reset_cert_a_1227, ⟨reset_cert_a_1228, ⟨reset_cert_a_1229, ⟨reset_cert_a_1230, reset_cert_a_1231⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
