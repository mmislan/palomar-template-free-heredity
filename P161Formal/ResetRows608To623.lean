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

theorem reset_cert_a_608 : resetParentTest 608 = true := by
  decide

theorem reset_cert_a_609 : resetParentTest 609 = true := by
  decide

theorem reset_cert_a_610 : resetParentTest 610 = true := by
  decide

theorem reset_cert_a_611 : resetParentTest 611 = true := by
  decide

theorem reset_cert_a_612 : resetParentTest 612 = true := by
  decide

theorem reset_cert_a_613 : resetParentTest 613 = true := by
  decide

theorem reset_cert_a_614 : resetParentTest 614 = true := by
  decide

theorem reset_cert_a_615 : resetParentTest 615 = true := by
  decide

theorem reset_cert_a_616 : resetParentTest 616 = true := by
  decide

theorem reset_cert_a_617 : resetParentTest 617 = true := by
  decide

theorem reset_cert_a_618 : resetParentTest 618 = true := by
  decide

theorem reset_cert_a_619 : resetParentTest 619 = true := by
  decide

theorem reset_cert_a_620 : resetParentTest 620 = true := by
  decide

theorem reset_cert_a_621 : resetParentTest 621 = true := by
  decide

theorem reset_cert_a_622 : resetParentTest 622 = true := by
  decide

theorem reset_cert_a_623 : resetParentTest 623 = true := by
  decide

def resetParents608To623 : List ℕ := [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]

theorem reset_block_608_to_623 : resetParents608To623.all resetParentTest = true := by
  simp only [resetParents608To623, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_608, ⟨reset_cert_a_609, ⟨reset_cert_a_610, ⟨reset_cert_a_611, ⟨reset_cert_a_612, ⟨reset_cert_a_613, ⟨reset_cert_a_614, ⟨reset_cert_a_615, ⟨reset_cert_a_616, ⟨reset_cert_a_617, ⟨reset_cert_a_618, ⟨reset_cert_a_619, ⟨reset_cert_a_620, ⟨reset_cert_a_621, ⟨reset_cert_a_622, reset_cert_a_623⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
