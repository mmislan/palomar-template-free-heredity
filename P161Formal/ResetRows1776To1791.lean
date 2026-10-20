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

theorem reset_cert_a_1776 : resetParentTest 1776 = true := by
  decide

theorem reset_cert_a_1777 : resetParentTest 1777 = true := by
  decide

theorem reset_cert_a_1778 : resetParentTest 1778 = true := by
  decide

theorem reset_cert_a_1779 : resetParentTest 1779 = true := by
  decide

theorem reset_cert_a_1780 : resetParentTest 1780 = true := by
  decide

theorem reset_cert_a_1781 : resetParentTest 1781 = true := by
  decide

theorem reset_cert_a_1782 : resetParentTest 1782 = true := by
  decide

theorem reset_cert_a_1783 : resetParentTest 1783 = true := by
  decide

theorem reset_cert_a_1784 : resetParentTest 1784 = true := by
  decide

theorem reset_cert_a_1785 : resetParentTest 1785 = true := by
  decide

theorem reset_cert_a_1786 : resetParentTest 1786 = true := by
  decide

theorem reset_cert_a_1787 : resetParentTest 1787 = true := by
  decide

theorem reset_cert_a_1788 : resetParentTest 1788 = true := by
  decide

theorem reset_cert_a_1789 : resetParentTest 1789 = true := by
  decide

theorem reset_cert_a_1790 : resetParentTest 1790 = true := by
  decide

theorem reset_cert_a_1791 : resetParentTest 1791 = true := by
  decide

def resetParents1776To1791 : List ℕ := [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]

theorem reset_block_1776_to_1791 : resetParents1776To1791.all resetParentTest = true := by
  simp only [resetParents1776To1791, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1776, ⟨reset_cert_a_1777, ⟨reset_cert_a_1778, ⟨reset_cert_a_1779, ⟨reset_cert_a_1780, ⟨reset_cert_a_1781, ⟨reset_cert_a_1782, ⟨reset_cert_a_1783, ⟨reset_cert_a_1784, ⟨reset_cert_a_1785, ⟨reset_cert_a_1786, ⟨reset_cert_a_1787, ⟨reset_cert_a_1788, ⟨reset_cert_a_1789, ⟨reset_cert_a_1790, reset_cert_a_1791⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
