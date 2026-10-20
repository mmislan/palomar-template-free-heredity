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

theorem reset_cert_a_1712 : resetParentTest 1712 = true := by
  decide

theorem reset_cert_a_1713 : resetParentTest 1713 = true := by
  decide

theorem reset_cert_a_1714 : resetParentTest 1714 = true := by
  decide

theorem reset_cert_a_1715 : resetParentTest 1715 = true := by
  decide

theorem reset_cert_a_1716 : resetParentTest 1716 = true := by
  decide

theorem reset_cert_a_1717 : resetParentTest 1717 = true := by
  decide

theorem reset_cert_a_1718 : resetParentTest 1718 = true := by
  decide

theorem reset_cert_a_1719 : resetParentTest 1719 = true := by
  decide

theorem reset_cert_a_1720 : resetParentTest 1720 = true := by
  decide

theorem reset_cert_a_1721 : resetParentTest 1721 = true := by
  decide

theorem reset_cert_a_1722 : resetParentTest 1722 = true := by
  decide

theorem reset_cert_a_1723 : resetParentTest 1723 = true := by
  decide

theorem reset_cert_a_1724 : resetParentTest 1724 = true := by
  decide

theorem reset_cert_a_1725 : resetParentTest 1725 = true := by
  decide

theorem reset_cert_a_1726 : resetParentTest 1726 = true := by
  decide

theorem reset_cert_a_1727 : resetParentTest 1727 = true := by
  decide

def resetParents1712To1727 : List ℕ := [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]

theorem reset_block_1712_to_1727 : resetParents1712To1727.all resetParentTest = true := by
  simp only [resetParents1712To1727, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1712, ⟨reset_cert_a_1713, ⟨reset_cert_a_1714, ⟨reset_cert_a_1715, ⟨reset_cert_a_1716, ⟨reset_cert_a_1717, ⟨reset_cert_a_1718, ⟨reset_cert_a_1719, ⟨reset_cert_a_1720, ⟨reset_cert_a_1721, ⟨reset_cert_a_1722, ⟨reset_cert_a_1723, ⟨reset_cert_a_1724, ⟨reset_cert_a_1725, ⟨reset_cert_a_1726, reset_cert_a_1727⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
