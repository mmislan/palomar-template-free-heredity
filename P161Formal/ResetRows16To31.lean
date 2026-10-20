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

theorem reset_cert_a_16 : resetParentTest 16 = true := by
  decide

theorem reset_cert_a_17 : resetParentTest 17 = true := by
  decide

theorem reset_cert_a_18 : resetParentTest 18 = true := by
  decide

theorem reset_cert_a_19 : resetParentTest 19 = true := by
  decide

theorem reset_cert_a_20 : resetParentTest 20 = true := by
  decide

theorem reset_cert_a_21 : resetParentTest 21 = true := by
  decide

theorem reset_cert_a_22 : resetParentTest 22 = true := by
  decide

theorem reset_cert_a_23 : resetParentTest 23 = true := by
  decide

theorem reset_cert_a_24 : resetParentTest 24 = true := by
  decide

theorem reset_cert_a_25 : resetParentTest 25 = true := by
  decide

theorem reset_cert_a_26 : resetParentTest 26 = true := by
  decide

theorem reset_cert_a_27 : resetParentTest 27 = true := by
  decide

theorem reset_cert_a_28 : resetParentTest 28 = true := by
  decide

theorem reset_cert_a_29 : resetParentTest 29 = true := by
  decide

theorem reset_cert_a_30 : resetParentTest 30 = true := by
  decide

theorem reset_cert_a_31 : resetParentTest 31 = true := by
  decide

def resetParents16To31 : List ℕ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

theorem reset_block_16_to_31 : resetParents16To31.all resetParentTest = true := by
  simp only [resetParents16To31, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_16, ⟨reset_cert_a_17, ⟨reset_cert_a_18, ⟨reset_cert_a_19, ⟨reset_cert_a_20, ⟨reset_cert_a_21, ⟨reset_cert_a_22, ⟨reset_cert_a_23, ⟨reset_cert_a_24, ⟨reset_cert_a_25, ⟨reset_cert_a_26, ⟨reset_cert_a_27, ⟨reset_cert_a_28, ⟨reset_cert_a_29, ⟨reset_cert_a_30, reset_cert_a_31⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
