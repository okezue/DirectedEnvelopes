import DirectedEnvelopes.Defs
import DirectedEnvelopes.Envelope

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

theorem prior_free {w : Wt n} (C : Clos w) (g : Fin n → ℝ)
    (c : Fin n → ℝ) (hc : ∀ θ, 0 < c θ)
    (r : Fin n → ℝ) (hf : Feas w g r) :
    ∑ θ : Fin n, c θ * envSol C.d g θ ≤ ∑ θ : Fin n, c θ * r θ := by
  apply Finset.sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left
  · exact envSol_min C g r hf θ
  · exact le_of_lt (hc θ)

end DE
