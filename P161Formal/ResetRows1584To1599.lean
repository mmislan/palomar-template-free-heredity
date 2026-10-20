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

theorem reset_cert_a_1584 : resetParentTest 1584 = true := by
  decide

theorem reset_cert_a_1585 : resetParentTest 1585 = true := by
  decide

theorem reset_cert_a_1586 : resetParentTest 1586 = true := by
  decide

theorem reset_cert_a_1587 : resetParentTest 1587 = true := by
  decide

theorem reset_cert_a_1588 : resetParentTest 1588 = true := by
  decide

theorem reset_cert_a_1589 : resetParentTest 1589 = true := by
  decide

theorem reset_cert_a_1590 : resetParentTest 1590 = true := by
  decide

theorem reset_cert_a_1591 : resetParentTest 1591 = true := by
  decide

theorem reset_cert_a_1592 : resetParentTest 1592 = true := by
  decide

theorem reset_cert_a_1593 : resetParentTest 1593 = true := by
  decide

theorem reset_cert_a_1594 : resetParentTest 1594 = true := by
  decide

theorem reset_cert_a_1595 : resetParentTest 1595 = true := by
  decide

theorem reset_cert_a_1596 : resetParentTest 1596 = true := by
  decide

theorem reset_cert_a_1597 : resetParentTest 1597 = true := by
  decide

theorem reset_cert_a_1598 : resetParentTest 1598 = true := by
  decide

theorem reset_cert_a_1599 : resetParentTest 1599 = true := by
  decide

def resetParents1584To1599 : List ℕ := [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]

theorem reset_block_1584_to_1599 : resetParents1584To1599.all resetParentTest = true := by
  simp only [resetParents1584To1599, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1584, ⟨reset_cert_a_1585, ⟨reset_cert_a_1586, ⟨reset_cert_a_1587, ⟨reset_cert_a_1588, ⟨reset_cert_a_1589, ⟨reset_cert_a_1590, ⟨reset_cert_a_1591, ⟨reset_cert_a_1592, ⟨reset_cert_a_1593, ⟨reset_cert_a_1594, ⟨reset_cert_a_1595, ⟨reset_cert_a_1596, ⟨reset_cert_a_1597, ⟨reset_cert_a_1598, reset_cert_a_1599⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
