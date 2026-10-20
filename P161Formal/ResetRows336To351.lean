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

theorem reset_cert_a_336 : resetParentTest 336 = true := by
  decide

theorem reset_cert_a_337 : resetParentTest 337 = true := by
  decide

theorem reset_cert_a_338 : resetParentTest 338 = true := by
  decide

theorem reset_cert_a_339 : resetParentTest 339 = true := by
  decide

theorem reset_cert_a_340 : resetParentTest 340 = true := by
  decide

theorem reset_cert_a_341 : resetParentTest 341 = true := by
  decide

theorem reset_cert_a_342 : resetParentTest 342 = true := by
  decide

theorem reset_cert_a_343 : resetParentTest 343 = true := by
  decide

theorem reset_cert_a_344 : resetParentTest 344 = true := by
  decide

theorem reset_cert_a_345 : resetParentTest 345 = true := by
  decide

theorem reset_cert_a_346 : resetParentTest 346 = true := by
  decide

theorem reset_cert_a_347 : resetParentTest 347 = true := by
  decide

theorem reset_cert_a_348 : resetParentTest 348 = true := by
  decide

theorem reset_cert_a_349 : resetParentTest 349 = true := by
  decide

theorem reset_cert_a_350 : resetParentTest 350 = true := by
  decide

theorem reset_cert_a_351 : resetParentTest 351 = true := by
  decide

def resetParents336To351 : List ℕ := [336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]

theorem reset_block_336_to_351 : resetParents336To351.all resetParentTest = true := by
  simp only [resetParents336To351, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_336, ⟨reset_cert_a_337, ⟨reset_cert_a_338, ⟨reset_cert_a_339, ⟨reset_cert_a_340, ⟨reset_cert_a_341, ⟨reset_cert_a_342, ⟨reset_cert_a_343, ⟨reset_cert_a_344, ⟨reset_cert_a_345, ⟨reset_cert_a_346, ⟨reset_cert_a_347, ⟨reset_cert_a_348, ⟨reset_cert_a_349, ⟨reset_cert_a_350, reset_cert_a_351⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
