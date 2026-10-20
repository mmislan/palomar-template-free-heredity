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

theorem reset_cert_a_224 : resetParentTest 224 = true := by
  decide

theorem reset_cert_a_225 : resetParentTest 225 = true := by
  decide

theorem reset_cert_a_226 : resetParentTest 226 = true := by
  decide

theorem reset_cert_a_227 : resetParentTest 227 = true := by
  decide

theorem reset_cert_a_228 : resetParentTest 228 = true := by
  decide

theorem reset_cert_a_229 : resetParentTest 229 = true := by
  decide

theorem reset_cert_a_230 : resetParentTest 230 = true := by
  decide

theorem reset_cert_a_231 : resetParentTest 231 = true := by
  decide

theorem reset_cert_a_232 : resetParentTest 232 = true := by
  decide

theorem reset_cert_a_233 : resetParentTest 233 = true := by
  decide

theorem reset_cert_a_234 : resetParentTest 234 = true := by
  decide

theorem reset_cert_a_235 : resetParentTest 235 = true := by
  decide

theorem reset_cert_a_236 : resetParentTest 236 = true := by
  decide

theorem reset_cert_a_237 : resetParentTest 237 = true := by
  decide

theorem reset_cert_a_238 : resetParentTest 238 = true := by
  decide

theorem reset_cert_a_239 : resetParentTest 239 = true := by
  decide

def resetParents224To239 : List ℕ := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]

theorem reset_block_224_to_239 : resetParents224To239.all resetParentTest = true := by
  simp only [resetParents224To239, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_224, ⟨reset_cert_a_225, ⟨reset_cert_a_226, ⟨reset_cert_a_227, ⟨reset_cert_a_228, ⟨reset_cert_a_229, ⟨reset_cert_a_230, ⟨reset_cert_a_231, ⟨reset_cert_a_232, ⟨reset_cert_a_233, ⟨reset_cert_a_234, ⟨reset_cert_a_235, ⟨reset_cert_a_236, ⟨reset_cert_a_237, ⟨reset_cert_a_238, reset_cert_a_239⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
