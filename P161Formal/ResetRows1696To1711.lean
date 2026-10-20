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

theorem reset_cert_a_1696 : resetParentTest 1696 = true := by
  decide

theorem reset_cert_a_1697 : resetParentTest 1697 = true := by
  decide

theorem reset_cert_a_1698 : resetParentTest 1698 = true := by
  decide

theorem reset_cert_a_1699 : resetParentTest 1699 = true := by
  decide

theorem reset_cert_a_1700 : resetParentTest 1700 = true := by
  decide

theorem reset_cert_a_1701 : resetParentTest 1701 = true := by
  decide

theorem reset_cert_a_1702 : resetParentTest 1702 = true := by
  decide

theorem reset_cert_a_1703 : resetParentTest 1703 = true := by
  decide

theorem reset_cert_a_1704 : resetParentTest 1704 = true := by
  decide

theorem reset_cert_a_1705 : resetParentTest 1705 = true := by
  decide

theorem reset_cert_a_1706 : resetParentTest 1706 = true := by
  decide

theorem reset_cert_a_1707 : resetParentTest 1707 = true := by
  decide

theorem reset_cert_a_1708 : resetParentTest 1708 = true := by
  decide

theorem reset_cert_a_1709 : resetParentTest 1709 = true := by
  decide

theorem reset_cert_a_1710 : resetParentTest 1710 = true := by
  decide

theorem reset_cert_a_1711 : resetParentTest 1711 = true := by
  decide

def resetParents1696To1711 : List ℕ := [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]

theorem reset_block_1696_to_1711 : resetParents1696To1711.all resetParentTest = true := by
  simp only [resetParents1696To1711, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1696, ⟨reset_cert_a_1697, ⟨reset_cert_a_1698, ⟨reset_cert_a_1699, ⟨reset_cert_a_1700, ⟨reset_cert_a_1701, ⟨reset_cert_a_1702, ⟨reset_cert_a_1703, ⟨reset_cert_a_1704, ⟨reset_cert_a_1705, ⟨reset_cert_a_1706, ⟨reset_cert_a_1707, ⟨reset_cert_a_1708, ⟨reset_cert_a_1709, ⟨reset_cert_a_1710, reset_cert_a_1711⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
