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

theorem reset_cert_a_1984 : resetParentTest 1984 = true := by
  decide

theorem reset_cert_a_1985 : resetParentTest 1985 = true := by
  decide

theorem reset_cert_a_1986 : resetParentTest 1986 = true := by
  decide

theorem reset_cert_a_1987 : resetParentTest 1987 = true := by
  decide

theorem reset_cert_a_1988 : resetParentTest 1988 = true := by
  decide

theorem reset_cert_a_1989 : resetParentTest 1989 = true := by
  decide

theorem reset_cert_a_1990 : resetParentTest 1990 = true := by
  decide

theorem reset_cert_a_1991 : resetParentTest 1991 = true := by
  decide

theorem reset_cert_a_1992 : resetParentTest 1992 = true := by
  decide

theorem reset_cert_a_1993 : resetParentTest 1993 = true := by
  decide

theorem reset_cert_a_1994 : resetParentTest 1994 = true := by
  decide

theorem reset_cert_a_1995 : resetParentTest 1995 = true := by
  decide

theorem reset_cert_a_1996 : resetParentTest 1996 = true := by
  decide

theorem reset_cert_a_1997 : resetParentTest 1997 = true := by
  decide

theorem reset_cert_a_1998 : resetParentTest 1998 = true := by
  decide

theorem reset_cert_a_1999 : resetParentTest 1999 = true := by
  decide

def resetParents1984To1999 : List ℕ := [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]

theorem reset_block_1984_to_1999 : resetParents1984To1999.all resetParentTest = true := by
  simp only [resetParents1984To1999, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_1984, ⟨reset_cert_a_1985, ⟨reset_cert_a_1986, ⟨reset_cert_a_1987, ⟨reset_cert_a_1988, ⟨reset_cert_a_1989, ⟨reset_cert_a_1990, ⟨reset_cert_a_1991, ⟨reset_cert_a_1992, ⟨reset_cert_a_1993, ⟨reset_cert_a_1994, ⟨reset_cert_a_1995, ⟨reset_cert_a_1996, ⟨reset_cert_a_1997, ⟨reset_cert_a_1998, reset_cert_a_1999⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
