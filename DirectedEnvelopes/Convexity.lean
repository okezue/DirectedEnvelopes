import DirectedEnvelopes.Defs
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Finset Real

namespace DE

variable {n : ℕ} [NeZero n]

theorem single_exp_convex (θ : Fin n) :
    ConvexOn ℝ Set.univ (fun r : Fin n → ℝ => rexp (r θ)) := by
  constructor
  · exact convex_univ
  · intro r₁ _ r₂ _ a b ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (convexOn_exp).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem weighted_exp_convex (μ : Fin n → ℝ) (hμ : ∀ θ, 0 ≤ μ θ) (θ : Fin n) :
    ConvexOn ℝ Set.univ (fun r : Fin n → ℝ => μ θ * rexp (r θ)) :=
  (single_exp_convex θ).smul (hμ θ)

theorem expSum_convex (μ : Fin n → ℝ) (hμ : ∀ θ, 0 ≤ μ θ) :
    ConvexOn ℝ Set.univ (fun r : Fin n → ℝ => ∑ θ, μ θ * rexp (r θ)) := by
  induction (univ : Finset (Fin n)) using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact convexOn_const 0 convex_univ
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact (weighted_exp_convex μ hμ a).add ih

theorem diffConstr_convex :
    Convex ℝ {p : (Fin n → ℝ) × (Fin n → Fin n → ℝ) |
      ∀ θ i, p.1 i - p.1 θ ≤ p.2 θ i} := by
  intro ⟨r₁, w₁⟩ h₁ ⟨r₂, w₂⟩ h₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  intro θ i
  simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]
  nlinarith [h₁ θ i, h₂ θ i]

theorem lbConstr_convex (g : Fin n → ℝ) :
    Convex ℝ {r : Fin n → ℝ | ∀ i, g i ≤ r i} := by
  intro r₁ h₁ r₂ h₂ a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc g i = (a + b) * g i := by rw [hab]; ring
    _ = a * g i + b * g i := by ring
    _ ≤ a * r₁ i + b * r₂ i := add_le_add
        (mul_le_mul_of_nonneg_left (h₁ i) ha)
        (mul_le_mul_of_nonneg_left (h₂ i) hb)

theorem envSol_convex_in_g (d : Wt n) (θ : Fin n) :
    ConvexOn ℝ Set.univ (fun g : Fin n → ℝ => envSol d g θ) := by
  constructor
  · exact convex_univ
  · intro g₁ _ g₂ _ a b ha hb hab
    simp only [envSol]
    apply sup'_le
    intro j _
    set S₁ := univ.sup' univ_nonempty (fun k => g₁ k - d θ k)
    set S₂ := univ.sup' univ_nonempty (fun k => g₂ k - d θ k)
    have hle₁ := le_sup' (f := fun k => g₁ k - d θ k) (mem_univ j)
    have hle₂ := le_sup' (f := fun k => g₂ k - d θ k) (mem_univ j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc a * g₁ j + b * g₂ j - d θ j
        = a * g₁ j + b * g₂ j - (a + b) * d θ j := by rw [hab]; ring
      _ = a * (g₁ j - d θ j) + b * (g₂ j - d θ j) := by ring
      _ ≤ a * S₁ + b * S₂ := add_le_add
          (mul_le_mul_of_nonneg_left hle₁ ha)
          (mul_le_mul_of_nonneg_left hle₂ hb)

theorem exp_envSol_convex (d : Wt n) (θ : Fin n) :
    ConvexOn ℝ Set.univ (fun g : Fin n → ℝ => rexp (envSol d g θ)) := by
  constructor
  · exact convex_univ
  · intro g₁ _ g₂ _ a b ha hb hab
    have henv := (envSol_convex_in_g d θ).2 (Set.mem_univ g₁) (Set.mem_univ g₂) ha hb hab
    calc rexp (envSol d (a • g₁ + b • g₂) θ)
        ≤ rexp (a * envSol d g₁ θ + b * envSol d g₂ θ) := by
          apply exp_le_exp.mpr
          simpa [smul_eq_mul] using henv
      _ ≤ a * rexp (envSol d g₁ θ) + b * rexp (envSol d g₂ θ) :=
          (convexOn_exp).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

end DE
