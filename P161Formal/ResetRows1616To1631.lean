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

theorem reset_cert_a_1616 : resetParentTest 1616 = true := by
  decide

theorem reset_cert_a_1617 : resetParentTest 1617 = true := by
  decide

theorem reset_cert_a_1618 : resetParentTest 1618 = true := by
  decide

theorem reset_cert_a_1619 : resetParentTest 1619 = true := by
  decide

theorem reset_cert_a_1620 : resetParentTest 1620 = true := by
  decide

theorem reset_cert_a_1621 : resetParentTest 1621 = true := by
  decide

theorem reset_cert_a_1622 : resetParentTest 1622 = true := by
  decide

theorem reset_cert_a_1623 : resetParentTest 1623 = true := by
  decide

theorem reset_cert_a_1624 : resetParentTest 1624 = true := by
  decide

theorem reset_cert_a_1625 : resetParentTest 1625 = true := by
  decide

theorem reset_cert_a_1626 : resetParentTest 1626 = true := by
  decide

theorem reset_cert_a_1627 : resetParentTest 1627 = true := by
  decide

theorem reset_cert_a_1628 : resetParentTest 1628 = true := by
  decide

theorem reset_cert_a_1629 : resetParentTest 1629 = true := by
  decide

theorem reset_cert_a_1630 : resetParentTest 1630 = true := by
  decide

theorem reset_cert_a_1631 : resetParentTest 1631 = true := by
  decide

def resetParents1616To1631 : List ℕ := [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]

theorem reset_block_1616_to_1631 : resetParents1616To1631.all resetParentTest = true := by
  simp only [resetParents1616To1631, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1616, ⟨reset_cert_a_1617, ⟨reset_cert_a_1618, ⟨reset_cert_a_1619, ⟨reset_cert_a_1620, ⟨reset_cert_a_1621, ⟨reset_cert_a_1622, ⟨reset_cert_a_1623, ⟨reset_cert_a_1624, ⟨reset_cert_a_1625, ⟨reset_cert_a_1626, ⟨reset_cert_a_1627, ⟨reset_cert_a_1628, ⟨reset_cert_a_1629, ⟨reset_cert_a_1630, reset_cert_a_1631⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
