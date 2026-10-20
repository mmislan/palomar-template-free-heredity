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

theorem reset_cert_a_272 : resetParentTest 272 = true := by
  decide

theorem reset_cert_a_273 : resetParentTest 273 = true := by
  decide

theorem reset_cert_a_274 : resetParentTest 274 = true := by
  decide

theorem reset_cert_a_275 : resetParentTest 275 = true := by
  decide

theorem reset_cert_a_276 : resetParentTest 276 = true := by
  decide

theorem reset_cert_a_277 : resetParentTest 277 = true := by
  decide

theorem reset_cert_a_278 : resetParentTest 278 = true := by
  decide

theorem reset_cert_a_279 : resetParentTest 279 = true := by
  decide

theorem reset_cert_a_280 : resetParentTest 280 = true := by
  decide

theorem reset_cert_a_281 : resetParentTest 281 = true := by
  decide

theorem reset_cert_a_282 : resetParentTest 282 = true := by
  decide

theorem reset_cert_a_283 : resetParentTest 283 = true := by
  decide

theorem reset_cert_a_284 : resetParentTest 284 = true := by
  decide

theorem reset_cert_a_285 : resetParentTest 285 = true := by
  decide

theorem reset_cert_a_286 : resetParentTest 286 = true := by
  decide

theorem reset_cert_a_287 : resetParentTest 287 = true := by
  decide

def resetParents272To287 : List ℕ := [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287]

theorem reset_block_272_to_287 : resetParents272To287.all resetParentTest = true := by
  simp only [resetParents272To287, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_272, ⟨reset_cert_a_273, ⟨reset_cert_a_274, ⟨reset_cert_a_275, ⟨reset_cert_a_276, ⟨reset_cert_a_277, ⟨reset_cert_a_278, ⟨reset_cert_a_279, ⟨reset_cert_a_280, ⟨reset_cert_a_281, ⟨reset_cert_a_282, ⟨reset_cert_a_283, ⟨reset_cert_a_284, ⟨reset_cert_a_285, ⟨reset_cert_a_286, reset_cert_a_287⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
