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

theorem reset_cert_a_320 : resetParentTest 320 = true := by
  decide

theorem reset_cert_a_321 : resetParentTest 321 = true := by
  decide

theorem reset_cert_a_322 : resetParentTest 322 = true := by
  decide

theorem reset_cert_a_323 : resetParentTest 323 = true := by
  decide

theorem reset_cert_a_324 : resetParentTest 324 = true := by
  decide

theorem reset_cert_a_325 : resetParentTest 325 = true := by
  decide

theorem reset_cert_a_326 : resetParentTest 326 = true := by
  decide

theorem reset_cert_a_327 : resetParentTest 327 = true := by
  decide

theorem reset_cert_a_328 : resetParentTest 328 = true := by
  decide

theorem reset_cert_a_329 : resetParentTest 329 = true := by
  decide

theorem reset_cert_a_330 : resetParentTest 330 = true := by
  decide

theorem reset_cert_a_331 : resetParentTest 331 = true := by
  decide

theorem reset_cert_a_332 : resetParentTest 332 = true := by
  decide

theorem reset_cert_a_333 : resetParentTest 333 = true := by
  decide

theorem reset_cert_a_334 : resetParentTest 334 = true := by
  decide

theorem reset_cert_a_335 : resetParentTest 335 = true := by
  decide

def resetParents320To335 : List ℕ := [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]

theorem reset_block_320_to_335 : resetParents320To335.all resetParentTest = true := by
  simp only [resetParents320To335, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_320, ⟨reset_cert_a_321, ⟨reset_cert_a_322, ⟨reset_cert_a_323, ⟨reset_cert_a_324, ⟨reset_cert_a_325, ⟨reset_cert_a_326, ⟨reset_cert_a_327, ⟨reset_cert_a_328, ⟨reset_cert_a_329, ⟨reset_cert_a_330, ⟨reset_cert_a_331, ⟨reset_cert_a_332, ⟨reset_cert_a_333, ⟨reset_cert_a_334, reset_cert_a_335⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
