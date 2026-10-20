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

theorem reset_cert_a_64 : resetParentTest 64 = true := by
  decide

theorem reset_cert_a_65 : resetParentTest 65 = true := by
  decide

theorem reset_cert_a_66 : resetParentTest 66 = true := by
  decide

theorem reset_cert_a_67 : resetParentTest 67 = true := by
  decide

theorem reset_cert_a_68 : resetParentTest 68 = true := by
  decide

theorem reset_cert_a_69 : resetParentTest 69 = true := by
  decide

theorem reset_cert_a_70 : resetParentTest 70 = true := by
  decide

theorem reset_cert_a_71 : resetParentTest 71 = true := by
  decide

theorem reset_cert_a_72 : resetParentTest 72 = true := by
  decide

theorem reset_cert_a_73 : resetParentTest 73 = true := by
  decide

theorem reset_cert_a_74 : resetParentTest 74 = true := by
  decide

theorem reset_cert_a_75 : resetParentTest 75 = true := by
  decide

theorem reset_cert_a_76 : resetParentTest 76 = true := by
  decide

theorem reset_cert_a_77 : resetParentTest 77 = true := by
  decide

theorem reset_cert_a_78 : resetParentTest 78 = true := by
  decide

theorem reset_cert_a_79 : resetParentTest 79 = true := by
  decide

def resetParents64To79 : List ℕ := [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]

theorem reset_block_64_to_79 : resetParents64To79.all resetParentTest = true := by
  simp only [resetParents64To79, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_64, ⟨reset_cert_a_65, ⟨reset_cert_a_66, ⟨reset_cert_a_67, ⟨reset_cert_a_68, ⟨reset_cert_a_69, ⟨reset_cert_a_70, ⟨reset_cert_a_71, ⟨reset_cert_a_72, ⟨reset_cert_a_73, ⟨reset_cert_a_74, ⟨reset_cert_a_75, ⟨reset_cert_a_76, ⟨reset_cert_a_77, ⟨reset_cert_a_78, reset_cert_a_79⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
