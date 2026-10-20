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

theorem reset_cert_a_96 : resetParentTest 96 = true := by
  decide

theorem reset_cert_a_97 : resetParentTest 97 = true := by
  decide

theorem reset_cert_a_98 : resetParentTest 98 = true := by
  decide

theorem reset_cert_a_99 : resetParentTest 99 = true := by
  decide

theorem reset_cert_a_100 : resetParentTest 100 = true := by
  decide

theorem reset_cert_a_101 : resetParentTest 101 = true := by
  decide

theorem reset_cert_a_102 : resetParentTest 102 = true := by
  decide

theorem reset_cert_a_103 : resetParentTest 103 = true := by
  decide

theorem reset_cert_a_104 : resetParentTest 104 = true := by
  decide

theorem reset_cert_a_105 : resetParentTest 105 = true := by
  decide

theorem reset_cert_a_106 : resetParentTest 106 = true := by
  decide

theorem reset_cert_a_107 : resetParentTest 107 = true := by
  decide

theorem reset_cert_a_108 : resetParentTest 108 = true := by
  decide

theorem reset_cert_a_109 : resetParentTest 109 = true := by
  decide

theorem reset_cert_a_110 : resetParentTest 110 = true := by
  decide

theorem reset_cert_a_111 : resetParentTest 111 = true := by
  decide

def resetParents96To111 : List ℕ := [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]

theorem reset_block_96_to_111 : resetParents96To111.all resetParentTest = true := by
  simp only [resetParents96To111, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_96, ⟨reset_cert_a_97, ⟨reset_cert_a_98, ⟨reset_cert_a_99, ⟨reset_cert_a_100, ⟨reset_cert_a_101, ⟨reset_cert_a_102, ⟨reset_cert_a_103, ⟨reset_cert_a_104, ⟨reset_cert_a_105, ⟨reset_cert_a_106, ⟨reset_cert_a_107, ⟨reset_cert_a_108, ⟨reset_cert_a_109, ⟨reset_cert_a_110, reset_cert_a_111⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
