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

theorem reset_cert_a_240 : resetParentTest 240 = true := by
  decide

theorem reset_cert_a_241 : resetParentTest 241 = true := by
  decide

theorem reset_cert_a_242 : resetParentTest 242 = true := by
  decide

theorem reset_cert_a_243 : resetParentTest 243 = true := by
  decide

theorem reset_cert_a_244 : resetParentTest 244 = true := by
  decide

theorem reset_cert_a_245 : resetParentTest 245 = true := by
  decide

theorem reset_cert_a_246 : resetParentTest 246 = true := by
  decide

theorem reset_cert_a_247 : resetParentTest 247 = true := by
  decide

theorem reset_cert_a_248 : resetParentTest 248 = true := by
  decide

theorem reset_cert_a_249 : resetParentTest 249 = true := by
  decide

theorem reset_cert_a_250 : resetParentTest 250 = true := by
  decide

theorem reset_cert_a_251 : resetParentTest 251 = true := by
  decide

theorem reset_cert_a_252 : resetParentTest 252 = true := by
  decide

theorem reset_cert_a_253 : resetParentTest 253 = true := by
  decide

theorem reset_cert_a_254 : resetParentTest 254 = true := by
  decide

theorem reset_cert_a_255 : resetParentTest 255 = true := by
  decide

def resetParents240To255 : List ℕ := [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]

theorem reset_block_240_to_255 : resetParents240To255.all resetParentTest = true := by
  simp only [resetParents240To255, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_240, ⟨reset_cert_a_241, ⟨reset_cert_a_242, ⟨reset_cert_a_243, ⟨reset_cert_a_244, ⟨reset_cert_a_245, ⟨reset_cert_a_246, ⟨reset_cert_a_247, ⟨reset_cert_a_248, ⟨reset_cert_a_249, ⟨reset_cert_a_250, ⟨reset_cert_a_251, ⟨reset_cert_a_252, ⟨reset_cert_a_253, ⟨reset_cert_a_254, reset_cert_a_255⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
