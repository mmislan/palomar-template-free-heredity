module

public import P161Formal.FuelAccounting
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-! Independent physical chemical updates, completing the visible count/fuel
model beside Contract's rates and complete division operation. All stock and
service ledgers remain external observations of actual physical marks. -/

@[expose] public section
namespace P161Formal
noncomputable section

def incrementCopies (a : Fin 2049) : Fin 2049 :=
  ⟨min (a.val+1) 2048, by omega⟩

def decrementCopies (a : Fin 2049) : Fin 2049 :=
  ⟨a.val-1, by have h := a.isLt; omega⟩

def changeCountAt (x : Population) (i : SiteId) (j : SpeciesId)
    (f : Fin 2049 → Fin 2049) : SiteId → SpeciesId → Fin 2049 :=
  Function.update x.count i (Function.update (x.count i) j (f (x.count i j)))

def chemicalCountsAfter (x : Population) : ChemicalChannel → SiteId → SpeciesId → Fin 2049
  | .seed i j | .birth i j => changeCountAt x i j incrementCopies
  | .passive i j | .activeDeath i j => changeCountAt x i j decrementCopies
  | .ordinary _ _ | .recharge _ | .discharge _ => x.count

def afterChemical (x : Population) (k : ChemicalChannel) : Population where
  count := chemicalCountsAfter x k
  fuel := chemicalFuelAfter x k

theorem population_ext {x y : Population}
    (hc : ∀ i j, x.count i j = y.count i j) (hf : ∀ i, x.fuel i = y.fuel i) : x = y := by
  cases x with
  | mk c f =>
      cases y with
      | mk d g =>
          have hcount : c = d := funext (fun i => funext (fun j => hc i j))
          have hfuel : f = g := funext hf
          cases hcount
          cases hfuel
          rfl

def populationEquiv : Population ≃
    ((SiteId → SpeciesId → Fin 2049) × (SiteId → Bool)) where
  toFun x := (x.count,x.fuel)
  invFun p := ⟨p.1,p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl

instance populationFintype : Fintype Population := Fintype.ofEquiv _ populationEquiv.symm
instance populationDecidableEq : DecidableEq Population := Classical.decEq _

end
end P161Formal
