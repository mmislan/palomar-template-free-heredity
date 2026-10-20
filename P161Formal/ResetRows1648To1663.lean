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

theorem reset_cert_a_1648 : resetParentTest 1648 = true := by
  decide

theorem reset_cert_a_1649 : resetParentTest 1649 = true := by
  decide

theorem reset_cert_a_1650 : resetParentTest 1650 = true := by
  decide

theorem reset_cert_a_1651 : resetParentTest 1651 = true := by
  decide

theorem reset_cert_a_1652 : resetParentTest 1652 = true := by
  decide

theorem reset_cert_a_1653 : resetParentTest 1653 = true := by
  decide

theorem reset_cert_a_1654 : resetParentTest 1654 = true := by
  decide

theorem reset_cert_a_1655 : resetParentTest 1655 = true := by
  decide

theorem reset_cert_a_1656 : resetParentTest 1656 = true := by
  decide

theorem reset_cert_a_1657 : resetParentTest 1657 = true := by
  decide

theorem reset_cert_a_1658 : resetParentTest 1658 = true := by
  decide

theorem reset_cert_a_1659 : resetParentTest 1659 = true := by
  decide

theorem reset_cert_a_1660 : resetParentTest 1660 = true := by
  decide

theorem reset_cert_a_1661 : resetParentTest 1661 = true := by
  decide

theorem reset_cert_a_1662 : resetParentTest 1662 = true := by
  decide

theorem reset_cert_a_1663 : resetParentTest 1663 = true := by
  decide

def resetParents1648To1663 : List ℕ := [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]

theorem reset_block_1648_to_1663 : resetParents1648To1663.all resetParentTest = true := by
  simp only [resetParents1648To1663, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1648, ⟨reset_cert_a_1649, ⟨reset_cert_a_1650, ⟨reset_cert_a_1651, ⟨reset_cert_a_1652, ⟨reset_cert_a_1653, ⟨reset_cert_a_1654, ⟨reset_cert_a_1655, ⟨reset_cert_a_1656, ⟨reset_cert_a_1657, ⟨reset_cert_a_1658, ⟨reset_cert_a_1659, ⟨reset_cert_a_1660, ⟨reset_cert_a_1661, ⟨reset_cert_a_1662, reset_cert_a_1663⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
