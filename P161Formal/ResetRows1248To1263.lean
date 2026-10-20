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

theorem reset_cert_a_1248 : resetParentTest 1248 = true := by
  decide

theorem reset_cert_a_1249 : resetParentTest 1249 = true := by
  decide

theorem reset_cert_a_1250 : resetParentTest 1250 = true := by
  decide

theorem reset_cert_a_1251 : resetParentTest 1251 = true := by
  decide

theorem reset_cert_a_1252 : resetParentTest 1252 = true := by
  decide

theorem reset_cert_a_1253 : resetParentTest 1253 = true := by
  decide

theorem reset_cert_a_1254 : resetParentTest 1254 = true := by
  decide

theorem reset_cert_a_1255 : resetParentTest 1255 = true := by
  decide

theorem reset_cert_a_1256 : resetParentTest 1256 = true := by
  decide

theorem reset_cert_a_1257 : resetParentTest 1257 = true := by
  decide

theorem reset_cert_a_1258 : resetParentTest 1258 = true := by
  decide

theorem reset_cert_a_1259 : resetParentTest 1259 = true := by
  decide

theorem reset_cert_a_1260 : resetParentTest 1260 = true := by
  decide

theorem reset_cert_a_1261 : resetParentTest 1261 = true := by
  decide

theorem reset_cert_a_1262 : resetParentTest 1262 = true := by
  decide

theorem reset_cert_a_1263 : resetParentTest 1263 = true := by
  decide

def resetParents1248To1263 : List ℕ := [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]

theorem reset_block_1248_to_1263 : resetParents1248To1263.all resetParentTest = true := by
  simp only [resetParents1248To1263, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1248, ⟨reset_cert_a_1249, ⟨reset_cert_a_1250, ⟨reset_cert_a_1251, ⟨reset_cert_a_1252, ⟨reset_cert_a_1253, ⟨reset_cert_a_1254, ⟨reset_cert_a_1255, ⟨reset_cert_a_1256, ⟨reset_cert_a_1257, ⟨reset_cert_a_1258, ⟨reset_cert_a_1259, ⟨reset_cert_a_1260, ⟨reset_cert_a_1261, ⟨reset_cert_a_1262, reset_cert_a_1263⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
