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

theorem reset_cert_a_1200 : resetParentTest 1200 = true := by
  decide

theorem reset_cert_a_1201 : resetParentTest 1201 = true := by
  decide

theorem reset_cert_a_1202 : resetParentTest 1202 = true := by
  decide

theorem reset_cert_a_1203 : resetParentTest 1203 = true := by
  decide

theorem reset_cert_a_1204 : resetParentTest 1204 = true := by
  decide

theorem reset_cert_a_1205 : resetParentTest 1205 = true := by
  decide

theorem reset_cert_a_1206 : resetParentTest 1206 = true := by
  decide

theorem reset_cert_a_1207 : resetParentTest 1207 = true := by
  decide

theorem reset_cert_a_1208 : resetParentTest 1208 = true := by
  decide

theorem reset_cert_a_1209 : resetParentTest 1209 = true := by
  decide

theorem reset_cert_a_1210 : resetParentTest 1210 = true := by
  decide

theorem reset_cert_a_1211 : resetParentTest 1211 = true := by
  decide

theorem reset_cert_a_1212 : resetParentTest 1212 = true := by
  decide

theorem reset_cert_a_1213 : resetParentTest 1213 = true := by
  decide

theorem reset_cert_a_1214 : resetParentTest 1214 = true := by
  decide

theorem reset_cert_a_1215 : resetParentTest 1215 = true := by
  decide

def resetParents1200To1215 : List ℕ := [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]

theorem reset_block_1200_to_1215 : resetParents1200To1215.all resetParentTest = true := by
  simp only [resetParents1200To1215, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1200, ⟨reset_cert_a_1201, ⟨reset_cert_a_1202, ⟨reset_cert_a_1203, ⟨reset_cert_a_1204, ⟨reset_cert_a_1205, ⟨reset_cert_a_1206, ⟨reset_cert_a_1207, ⟨reset_cert_a_1208, ⟨reset_cert_a_1209, ⟨reset_cert_a_1210, ⟨reset_cert_a_1211, ⟨reset_cert_a_1212, ⟨reset_cert_a_1213, ⟨reset_cert_a_1214, reset_cert_a_1215⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
