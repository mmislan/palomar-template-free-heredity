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

theorem reset_cert_a_2000 : resetParentTest 2000 = true := by
  decide

theorem reset_cert_a_2001 : resetParentTest 2001 = true := by
  decide

theorem reset_cert_a_2002 : resetParentTest 2002 = true := by
  decide

theorem reset_cert_a_2003 : resetParentTest 2003 = true := by
  decide

theorem reset_cert_a_2004 : resetParentTest 2004 = true := by
  decide

theorem reset_cert_a_2005 : resetParentTest 2005 = true := by
  decide

theorem reset_cert_a_2006 : resetParentTest 2006 = true := by
  decide

theorem reset_cert_a_2007 : resetParentTest 2007 = true := by
  decide

theorem reset_cert_a_2008 : resetParentTest 2008 = true := by
  decide

theorem reset_cert_a_2009 : resetParentTest 2009 = true := by
  decide

theorem reset_cert_a_2010 : resetParentTest 2010 = true := by
  decide

theorem reset_cert_a_2011 : resetParentTest 2011 = true := by
  decide

theorem reset_cert_a_2012 : resetParentTest 2012 = true := by
  decide

theorem reset_cert_a_2013 : resetParentTest 2013 = true := by
  decide

theorem reset_cert_a_2014 : resetParentTest 2014 = true := by
  decide

theorem reset_cert_a_2015 : resetParentTest 2015 = true := by
  decide

def resetParents2000To2015 : List ℕ := [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]

theorem reset_block_2000_to_2015 : resetParents2000To2015.all resetParentTest = true := by
  simp only [resetParents2000To2015, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨reset_cert_a_2000, ⟨reset_cert_a_2001, ⟨reset_cert_a_2002, ⟨reset_cert_a_2003, ⟨reset_cert_a_2004, ⟨reset_cert_a_2005, ⟨reset_cert_a_2006, ⟨reset_cert_a_2007, ⟨reset_cert_a_2008, ⟨reset_cert_a_2009, ⟨reset_cert_a_2010, ⟨reset_cert_a_2011, ⟨reset_cert_a_2012, ⟨reset_cert_a_2013, ⟨reset_cert_a_2014, reset_cert_a_2015⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end P161Formal
