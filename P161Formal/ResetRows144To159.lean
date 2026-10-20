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

theorem reset_cert_a_144 : resetParentTest 144 = true := by
  decide

theorem reset_cert_a_145 : resetParentTest 145 = true := by
  decide

theorem reset_cert_a_146 : resetParentTest 146 = true := by
  decide

theorem reset_cert_a_147 : resetParentTest 147 = true := by
  decide

theorem reset_cert_a_148 : resetParentTest 148 = true := by
  decide

theorem reset_cert_a_149 : resetParentTest 149 = true := by
  decide

theorem reset_cert_a_150 : resetParentTest 150 = true := by
  decide

theorem reset_cert_a_151 : resetParentTest 151 = true := by
  decide

theorem reset_cert_a_152 : resetParentTest 152 = true := by
  decide

theorem reset_cert_a_153 : resetParentTest 153 = true := by
  decide

theorem reset_cert_a_154 : resetParentTest 154 = true := by
  decide

theorem reset_cert_a_155 : resetParentTest 155 = true := by
  decide

theorem reset_cert_a_156 : resetParentTest 156 = true := by
  decide

theorem reset_cert_a_157 : resetParentTest 157 = true := by
  decide

theorem reset_cert_a_158 : resetParentTest 158 = true := by
  decide

theorem reset_cert_a_159 : resetParentTest 159 = true := by
  decide

def resetParents144To159 : List ℕ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]

theorem reset_block_144_to_159 : resetParents144To159.all resetParentTest = true := by
  simp only [resetParents144To159, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_144, ⟨reset_cert_a_145, ⟨reset_cert_a_146, ⟨reset_cert_a_147, ⟨reset_cert_a_148, ⟨reset_cert_a_149, ⟨reset_cert_a_150, ⟨reset_cert_a_151, ⟨reset_cert_a_152, ⟨reset_cert_a_153, ⟨reset_cert_a_154, ⟨reset_cert_a_155, ⟨reset_cert_a_156, ⟨reset_cert_a_157, ⟨reset_cert_a_158, reset_cert_a_159⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
