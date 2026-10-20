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

theorem reset_cert_a_160 : resetParentTest 160 = true := by
  decide

theorem reset_cert_a_161 : resetParentTest 161 = true := by
  decide

theorem reset_cert_a_162 : resetParentTest 162 = true := by
  decide

theorem reset_cert_a_163 : resetParentTest 163 = true := by
  decide

theorem reset_cert_a_164 : resetParentTest 164 = true := by
  decide

theorem reset_cert_a_165 : resetParentTest 165 = true := by
  decide

theorem reset_cert_a_166 : resetParentTest 166 = true := by
  decide

theorem reset_cert_a_167 : resetParentTest 167 = true := by
  decide

theorem reset_cert_a_168 : resetParentTest 168 = true := by
  decide

theorem reset_cert_a_169 : resetParentTest 169 = true := by
  decide

theorem reset_cert_a_170 : resetParentTest 170 = true := by
  decide

theorem reset_cert_a_171 : resetParentTest 171 = true := by
  decide

theorem reset_cert_a_172 : resetParentTest 172 = true := by
  decide

theorem reset_cert_a_173 : resetParentTest 173 = true := by
  decide

theorem reset_cert_a_174 : resetParentTest 174 = true := by
  decide

theorem reset_cert_a_175 : resetParentTest 175 = true := by
  decide

def resetParents160To175 : List ℕ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]

theorem reset_block_160_to_175 : resetParents160To175.all resetParentTest = true := by
  simp only [resetParents160To175, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_160, ⟨reset_cert_a_161, ⟨reset_cert_a_162, ⟨reset_cert_a_163, ⟨reset_cert_a_164, ⟨reset_cert_a_165, ⟨reset_cert_a_166, ⟨reset_cert_a_167, ⟨reset_cert_a_168, ⟨reset_cert_a_169, ⟨reset_cert_a_170, ⟨reset_cert_a_171, ⟨reset_cert_a_172, ⟨reset_cert_a_173, ⟨reset_cert_a_174, reset_cert_a_175⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
