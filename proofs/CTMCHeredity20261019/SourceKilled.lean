module

public import proofs.FunctionalCapacity.Defs

@[expose] public section

/-! Minimal killed-generator constructor copied from the existing FunctionalCapacity proof.
This private adapter imports only the source definitions and does not assume any path-law bridge. -/

namespace CTMCHeredity20261019
open FunctionalCapacity

noncomputable section
open Finset

variable {σ : Type}

/-! ### Generators -/

theorem generatorKilled_zero {L : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (x : σ) :
    G (fun _ => 0) x = 0 := by
  have h := hG.smul 0 (fun _ => 0) x
  simpa using h

theorem generatorKilled_sub {L : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (f g : σ → ℝ) (x : σ) :
    G (fun y => f y - g y) x = G f x - G g x := by
  have h1 := hG.add f (fun y => (-1) * g y) x
  have h2 := hG.smul (-1) g x
  have e : (fun y => f y - g y) = fun y => f y + (-1) * g y := by
    funext y; ring
  rw [e, h1, h2]; ring

theorem generatorKilled_kill_add (dead : σ → Prop) [DecidablePred dead] (f g : σ → ℝ) :
    kill dead (fun y => f y + g y) = fun y => kill dead f y + kill dead g y := by
  funext y
  simp only [kill]
  split_ifs <;> simp

theorem generatorKilled_kill_smul (dead : σ → Prop) [DecidablePred dead] (c : ℝ) (f : σ → ℝ) :
    kill dead (fun y => c * f y) = fun y => c * kill dead f y := by
  funext y
  simp only [kill]
  split_ifs <;> simp

/-- The killed uniformized tick of a bounded generator is a sub-Markov operator. -/
def generatorKilled {L Lam : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (dead : σ → Prop) [DecidablePred dead] : SubMarkov σ where
  P := stepK G Lam dead
  mono := by
    intro f g h x
    simp only [stepK]
    split_ifs with hx
    · exact le_rfl
    · have hd : ∀ y, 0 ≤ kill dead g y - kill dead f y := by
        intro y
        simp only [kill]
        split_ifs
        · simp
        · linarith [h y]
      have hp : 0 ≤ L * (kill dead g x - kill dead f x)
          + G (fun y => kill dead g y - kill dead f y) x := hG.pos _ hd x
      rw [generatorKilled_sub hG] at hp
      have hk : kill dead g x - kill dead f x = g x - f x := by simp [kill, hx]
      rw [hk] at hp
      have h1 : L * (g x - f x) ≤ Lam * (g x - f x) :=
        mul_le_mul_of_nonneg_right hL (by linarith [h x])
      have h2 : G (kill dead f) x / Lam - G (kill dead g) x / Lam ≤ g x - f x := by
        rw [← sub_div, div_le_iff₀ hLam]
        linarith
      linarith
  add := by
    intro f g x
    simp only [stepK]
    rw [generatorKilled_kill_add, hG.add]
    split_ifs
    · simp
    · ring
  smul := by
    intro c f x
    simp only [stepK]
    rw [generatorKilled_kill_smul, hG.smul]
    split_ifs
    · simp
    · ring
  le_one := by
    intro x
    simp only [stepK]
    split_ifs with hx
    · exact zero_le_one
    · have e : kill dead (fun _ => (1 : ℝ)) = fun y => 1 - (if dead y then (1 : ℝ) else 0) := by
        funext y
        simp only [kill]
        split_ifs <;> simp
      have hp : 0 ≤ L * (if dead x then (1 : ℝ) else 0)
          + G (fun y => if dead y then (1 : ℝ) else 0) x :=
        hG.pos (fun y => if dead y then (1 : ℝ) else 0)
          (fun y => by
            show (0 : ℝ) ≤ if dead y then (1 : ℝ) else 0
            split_ifs <;> norm_num) x
      rw [ite_eq_right hx, mul_zero, zero_add] at hp
      have e2 := generatorKilled_sub hG (fun _ => (1 : ℝ)) (fun y => if dead y then (1 : ℝ) else 0) x
      rw [e, e2, hG.one]
      have h3 : (0 - G (fun y => if dead y then (1 : ℝ) else 0) x) / Lam ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hLam.le
      linarith

@[simp] theorem generatorKilled_P {L Lam : ℝ} {G : (σ → ℝ) → σ → ℝ} (hG : IsGen L G) (hLam : 0 < Lam)
    (hL : L ≤ Lam) (dead : σ → Prop) [DecidablePred dead] :
    (generatorKilled hG hLam hL dead).P = stepK G Lam dead := rfl


end
end CTMCHeredity20261019
