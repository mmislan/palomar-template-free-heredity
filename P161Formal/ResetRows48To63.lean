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

theorem reset_cert_a_48 : resetParentTest 48 = true := by
  decide

theorem reset_cert_a_49 : resetParentTest 49 = true := by
  decide

theorem reset_cert_a_50 : resetParentTest 50 = true := by
  decide

theorem reset_cert_a_51 : resetParentTest 51 = true := by
  decide

theorem reset_cert_a_52 : resetParentTest 52 = true := by
  decide

theorem reset_cert_a_53 : resetParentTest 53 = true := by
  decide

theorem reset_cert_a_54 : resetParentTest 54 = true := by
  decide

theorem reset_cert_a_55 : resetParentTest 55 = true := by
  decide

theorem reset_cert_a_56 : resetParentTest 56 = true := by
  decide

theorem reset_cert_a_57 : resetParentTest 57 = true := by
  decide

theorem reset_cert_a_58 : resetParentTest 58 = true := by
  decide

theorem reset_cert_a_59 : resetParentTest 59 = true := by
  decide

theorem reset_cert_a_60 : resetParentTest 60 = true := by
  decide

theorem reset_cert_a_61 : resetParentTest 61 = true := by
  decide

theorem reset_cert_a_62 : resetParentTest 62 = true := by
  decide

theorem reset_cert_a_63 : resetParentTest 63 = true := by
  decide

def resetParents48To63 : List ℕ := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

theorem reset_block_48_to_63 : resetParents48To63.all resetParentTest = true := by
  simp only [resetParents48To63, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_48, ⟨reset_cert_a_49, ⟨reset_cert_a_50, ⟨reset_cert_a_51, ⟨reset_cert_a_52, ⟨reset_cert_a_53, ⟨reset_cert_a_54, ⟨reset_cert_a_55, ⟨reset_cert_a_56, ⟨reset_cert_a_57, ⟨reset_cert_a_58, ⟨reset_cert_a_59, ⟨reset_cert_a_60, ⟨reset_cert_a_61, ⟨reset_cert_a_62, reset_cert_a_63⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
