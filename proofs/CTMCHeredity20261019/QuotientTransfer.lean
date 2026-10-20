module

public import proofs.CTMCHeredity20261019.CF3Capped
public import proofs.CTMCHeredity20261019.GeneratorAdapter

@[expose] public section

/-! Exact quotient transfer for killed ticks, Poisson mixtures and grid blocks.
These are equalities of the existing scalar operators. The physical multi-time
path event identification remains a separate theorem. -/
namespace CTMCHeredity20261019
open FunctionalCapacity
open scoped Classical
noncomputable section

/-- The source killed tick is the actual reconstructed stochastic kernel
expectation killed at both the initial and post-jump state. -/
theorem stepK_as_stochastic_kernel {S : Type} [Fintype S] [DecidableEq S]
    {L Lam : ℝ} {G : (S → ℝ) → S → ℝ}
    (hG : IsGen L G) (hLam : 0 < Lam) (hL : L ≤ Lam)
    (dead : S → Prop) (f : S → ℝ) (x : S) :
    stepK G Lam dead f x = if dead x then 0 else
      (uniformizedKernel hG hLam hL).expect (kill dead f) x := by
  unfold stepK
  by_cases hx : dead x
  · simp [hx]
  · simp only [hx, ite_false]
    rw [uniformizedKernel_expect]
    simp [kill, hx]

theorem stepK_quotient {S T : Type} (π : S → T)
    (G : (S → ℝ) → S → ℝ) (H : (T → ℝ) → T → ℝ)
    (hG : ∀ f x, G (fun y => f (π y)) x = H f (π x))
    (Lam : ℝ) (dead : T → Prop) (f : T → ℝ) (x : S) :
    stepK G Lam (fun y => dead (π y)) (fun y => f (π y)) x =
      stepK H Lam dead f (π x) := by
  unfold stepK
  by_cases hx : dead (π x)
  · simp [hx]
  · simp only [hx, ite_false]
    have hk : kill (fun y => dead (π y)) (fun y => f (π y)) =
        fun y => (kill dead f) (π y) := rfl
    rw [hk, hG]

theorem iter_quotient {S T : Type} (π : S → T)
    (K : SubMarkov S) (H : SubMarkov T)
    (hP : ∀ f x, K.P (fun y => f (π y)) x = H.P f (π x))
    (n : ℕ) (f : T → ℝ) (x : S) :
    K.iter n (fun y => f (π y)) x = H.iter n f (π x) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change K.iter n (K.P (fun y => f (π y))) x = H.iter n (H.P f) (π x)
    have he : K.P (fun y => f (π y)) = fun y => H.P f (π y) := by
      funext y
      exact hP f y
    rw [he]
    exact ih _

theorem ct_quotient {S T : Type} (π : S → T)
    (K : SubMarkov S) (H : SubMarkov T)
    (hP : ∀ f x, K.P (fun y => f (π y)) x = H.P f (π x))
    (μ : ℝ) (f : T → ℝ) (x : S) :
    K.ct μ (fun y => f (π y)) x = H.ct μ f (π x) := by
  unfold SubMarkov.ct
  apply tsum_congr
  intro n
  rw [iter_quotient π K H hP]

theorem blocks_quotient {S T : Type} (π : S → T)
    (K : SubMarkov S) (H : SubMarkov T)
    (hP : ∀ f x, K.P (fun y => f (π y)) x = H.P f (π x))
    (μ : ℝ) (ok : T → Prop) (resetS : S → S) (resetT : T → T)
    (hr : ∀ x, π (resetS x) = resetT (π x))
    (n : ℕ) (f : T → ℝ) (x : S) :
    blocks K μ (fun y => ok (π y)) resetS n (fun y => f (π y)) x =
      blocks H μ ok resetT n f (π x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change K.ct μ (fun y => if ok (π y) then
      blocks K μ (fun z => ok (π z)) resetS n (fun z => f (π z)) (resetS y) else 0) x = _
    have he : (fun y => if ok (π y) then
        blocks K μ (fun z => ok (π z)) resetS n (fun z => f (π z)) (resetS y) else 0) =
        (fun y => (if ok (π y) then blocks H μ ok resetT n f (resetT (π y)) else 0)) := by
      funext y
      rw [ih, hr]
    rw [he]
    exact ct_quotient π K H hP μ
      (fun z => if ok z then blocks H μ ok resetT n f (resetT z) else 0) x

/-- The capped source intertwines the actual killed tick, including the complete
post-jump floor check. No boundary-crossing jump is discarded. -/
theorem cf3_capped_stepK (p : Par) (Q D : ℕ) (Lam : ℝ)
    (dead : CappedState p Q D → Prop) (f : CappedState p Q D → ℝ)
    (x : CappedSource p) :
    stepK (cf3Gen p) Lam (fun y => dead (capProject Q D y))
      (fun y => f (capProject Q D y)) x =
        stepK (cappedGen p Q D) Lam dead f (capProject Q D x) :=
  stepK_quotient (capProject Q D) (cf3Gen p) (cappedGen p Q D)
    (cf3Gen_capped_lump p Q D) Lam dead f x

end
end CTMCHeredity20261019
