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

theorem reset_cert_a_1232 : resetParentTest 1232 = true := by
  decide

theorem reset_cert_a_1233 : resetParentTest 1233 = true := by
  decide

theorem reset_cert_a_1234 : resetParentTest 1234 = true := by
  decide

theorem reset_cert_a_1235 : resetParentTest 1235 = true := by
  decide

theorem reset_cert_a_1236 : resetParentTest 1236 = true := by
  decide

theorem reset_cert_a_1237 : resetParentTest 1237 = true := by
  decide

theorem reset_cert_a_1238 : resetParentTest 1238 = true := by
  decide

theorem reset_cert_a_1239 : resetParentTest 1239 = true := by
  decide

theorem reset_cert_a_1240 : resetParentTest 1240 = true := by
  decide

theorem reset_cert_a_1241 : resetParentTest 1241 = true := by
  decide

theorem reset_cert_a_1242 : resetParentTest 1242 = true := by
  decide

theorem reset_cert_a_1243 : resetParentTest 1243 = true := by
  decide

theorem reset_cert_a_1244 : resetParentTest 1244 = true := by
  decide

theorem reset_cert_a_1245 : resetParentTest 1245 = true := by
  decide

theorem reset_cert_a_1246 : resetParentTest 1246 = true := by
  decide

theorem reset_cert_a_1247 : resetParentTest 1247 = true := by
  decide

def resetParents1232To1247 : List ℕ := [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]

theorem reset_block_1232_to_1247 : resetParents1232To1247.all resetParentTest = true := by
  simp only [resetParents1232To1247, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1232, ⟨reset_cert_a_1233, ⟨reset_cert_a_1234, ⟨reset_cert_a_1235, ⟨reset_cert_a_1236, ⟨reset_cert_a_1237, ⟨reset_cert_a_1238, ⟨reset_cert_a_1239, ⟨reset_cert_a_1240, ⟨reset_cert_a_1241, ⟨reset_cert_a_1242, ⟨reset_cert_a_1243, ⟨reset_cert_a_1244, ⟨reset_cert_a_1245, ⟨reset_cert_a_1246, reset_cert_a_1247⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
