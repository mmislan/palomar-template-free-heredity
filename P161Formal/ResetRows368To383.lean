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

theorem reset_cert_a_368 : resetParentTest 368 = true := by
  decide

theorem reset_cert_a_369 : resetParentTest 369 = true := by
  decide

theorem reset_cert_a_370 : resetParentTest 370 = true := by
  decide

theorem reset_cert_a_371 : resetParentTest 371 = true := by
  decide

theorem reset_cert_a_372 : resetParentTest 372 = true := by
  decide

theorem reset_cert_a_373 : resetParentTest 373 = true := by
  decide

theorem reset_cert_a_374 : resetParentTest 374 = true := by
  decide

theorem reset_cert_a_375 : resetParentTest 375 = true := by
  decide

theorem reset_cert_a_376 : resetParentTest 376 = true := by
  decide

theorem reset_cert_a_377 : resetParentTest 377 = true := by
  decide

theorem reset_cert_a_378 : resetParentTest 378 = true := by
  decide

theorem reset_cert_a_379 : resetParentTest 379 = true := by
  decide

theorem reset_cert_a_380 : resetParentTest 380 = true := by
  decide

theorem reset_cert_a_381 : resetParentTest 381 = true := by
  decide

theorem reset_cert_a_382 : resetParentTest 382 = true := by
  decide

theorem reset_cert_a_383 : resetParentTest 383 = true := by
  decide

def resetParents368To383 : List ℕ := [368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]

theorem reset_block_368_to_383 : resetParents368To383.all resetParentTest = true := by
  simp only [resetParents368To383, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_368, ⟨reset_cert_a_369, ⟨reset_cert_a_370, ⟨reset_cert_a_371, ⟨reset_cert_a_372, ⟨reset_cert_a_373, ⟨reset_cert_a_374, ⟨reset_cert_a_375, ⟨reset_cert_a_376, ⟨reset_cert_a_377, ⟨reset_cert_a_378, ⟨reset_cert_a_379, ⟨reset_cert_a_380, ⟨reset_cert_a_381, ⟨reset_cert_a_382, reset_cert_a_383⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
