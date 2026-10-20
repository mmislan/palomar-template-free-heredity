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

theorem reset_cert_a_352 : resetParentTest 352 = true := by
  decide

theorem reset_cert_a_353 : resetParentTest 353 = true := by
  decide

theorem reset_cert_a_354 : resetParentTest 354 = true := by
  decide

theorem reset_cert_a_355 : resetParentTest 355 = true := by
  decide

theorem reset_cert_a_356 : resetParentTest 356 = true := by
  decide

theorem reset_cert_a_357 : resetParentTest 357 = true := by
  decide

theorem reset_cert_a_358 : resetParentTest 358 = true := by
  decide

theorem reset_cert_a_359 : resetParentTest 359 = true := by
  decide

theorem reset_cert_a_360 : resetParentTest 360 = true := by
  decide

theorem reset_cert_a_361 : resetParentTest 361 = true := by
  decide

theorem reset_cert_a_362 : resetParentTest 362 = true := by
  decide

theorem reset_cert_a_363 : resetParentTest 363 = true := by
  decide

theorem reset_cert_a_364 : resetParentTest 364 = true := by
  decide

theorem reset_cert_a_365 : resetParentTest 365 = true := by
  decide

theorem reset_cert_a_366 : resetParentTest 366 = true := by
  decide

theorem reset_cert_a_367 : resetParentTest 367 = true := by
  decide

def resetParents352To367 : List ℕ := [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]

theorem reset_block_352_to_367 : resetParents352To367.all resetParentTest = true := by
  simp only [resetParents352To367, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_352, ⟨reset_cert_a_353, ⟨reset_cert_a_354, ⟨reset_cert_a_355, ⟨reset_cert_a_356, ⟨reset_cert_a_357, ⟨reset_cert_a_358, ⟨reset_cert_a_359, ⟨reset_cert_a_360, ⟨reset_cert_a_361, ⟨reset_cert_a_362, ⟨reset_cert_a_363, ⟨reset_cert_a_364, ⟨reset_cert_a_365, ⟨reset_cert_a_366, reset_cert_a_367⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
