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

theorem reset_cert_a_256 : resetParentTest 256 = true := by
  decide

theorem reset_cert_a_257 : resetParentTest 257 = true := by
  decide

theorem reset_cert_a_258 : resetParentTest 258 = true := by
  decide

theorem reset_cert_a_259 : resetParentTest 259 = true := by
  decide

theorem reset_cert_a_260 : resetParentTest 260 = true := by
  decide

theorem reset_cert_a_261 : resetParentTest 261 = true := by
  decide

theorem reset_cert_a_262 : resetParentTest 262 = true := by
  decide

theorem reset_cert_a_263 : resetParentTest 263 = true := by
  decide

theorem reset_cert_a_264 : resetParentTest 264 = true := by
  decide

theorem reset_cert_a_265 : resetParentTest 265 = true := by
  decide

theorem reset_cert_a_266 : resetParentTest 266 = true := by
  decide

theorem reset_cert_a_267 : resetParentTest 267 = true := by
  decide

theorem reset_cert_a_268 : resetParentTest 268 = true := by
  decide

theorem reset_cert_a_269 : resetParentTest 269 = true := by
  decide

theorem reset_cert_a_270 : resetParentTest 270 = true := by
  decide

theorem reset_cert_a_271 : resetParentTest 271 = true := by
  decide

def resetParents256To271 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]

theorem reset_block_256_to_271 : resetParents256To271.all resetParentTest = true := by
  simp only [resetParents256To271, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_256, ⟨reset_cert_a_257, ⟨reset_cert_a_258, ⟨reset_cert_a_259, ⟨reset_cert_a_260, ⟨reset_cert_a_261, ⟨reset_cert_a_262, ⟨reset_cert_a_263, ⟨reset_cert_a_264, ⟨reset_cert_a_265, ⟨reset_cert_a_266, ⟨reset_cert_a_267, ⟨reset_cert_a_268, ⟨reset_cert_a_269, ⟨reset_cert_a_270, reset_cert_a_271⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
