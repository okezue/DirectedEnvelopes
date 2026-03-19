import DirectedEnvelopes.Defs
import DirectedEnvelopes.Submodularity
import Mathlib.Tactic

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

theorem mul_sup'_of_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    c * s.sup' hs f = s.sup' hs (fun i => c * f i) := by
  apply le_antisymm
  · obtain ⟨j, hj, hje⟩ := exists_mem_eq_sup' hs f
    rw [hje]
    exact le_sup' (fun i => c * f i) hj
  · apply sup'_le
    intro j hj
    exact mul_le_mul_of_nonneg_left (le_sup' f hj) hc

def P0 (μ : Fin n → ℝ) (c0 : Fin n → Fin n → ℝ)
    (φ : Fin n → ℝ → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ θ : Fin n, μ θ * univ.sup' univ_nonempty (fun j => c0 θ j * φ j (q j))

theorem P_scales (μ : Fin n → ℝ) (hμ : ∀ θ, 0 ≤ μ θ)
    (c0 : Fin n → Fin n → ℝ) (hc0 : ∀ θ j, 0 ≤ c0 θ j)
    (φ : Fin n → ℝ → ℝ) (hφ_nn : ∀ j q, 0 ≤ φ j q)
    (κ : ℝ) (hκ : 0 ≤ κ) (q : Fin n → ℝ) :
    ∑ θ : Fin n, μ θ *
      univ.sup' univ_nonempty (fun j => (κ * c0 θ j) * φ j (q j)) =
    κ * P0 μ c0 φ q := by
  simp only [P0, Finset.mul_sum]
  congr 1; ext θ
  have hrw : (fun j => (κ * c0 θ j) * φ j (q j)) =
             (fun j => κ * (c0 θ j * φ j (q j))) := by ext j; ring
  rw [hrw, ← mul_sup'_of_nonneg _ _ _ κ hκ]; ring

theorem P0_mono (μ : Fin n → ℝ) (hμ : ∀ θ, 0 ≤ μ θ)
    (c0 : Fin n → Fin n → ℝ) (hc0 : ∀ θ j, 0 ≤ c0 θ j)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ j, Monotone (φ j))
    (hφ_nn : ∀ j q, 0 ≤ φ j q)
    (q q' : Fin n → ℝ) (hq : q ≤ q') :
    P0 μ c0 φ q ≤ P0 μ c0 φ q' := by
  apply Finset.sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left _ (hμ θ)
  apply sup'_le
  intro j hj
  calc c0 θ j * φ j (q j) ≤ c0 θ j * φ j (q' j) :=
    mul_le_mul_of_nonneg_left ((hφ j) (hq j)) (hc0 θ j)
    _ ≤ _ := le_sup' (f := fun j => c0 θ j * φ j (q' j)) hj

theorem twoStage_supermod
    (V : (Fin n → ℝ) → ℝ) (C : ℝ → ℝ)
    (μ : Fin n → ℝ) (hμ : ∀ θ, 0 ≤ μ θ)
    (c0 : Fin n → Fin n → ℝ) (hc0 : ∀ θ j, 0 ≤ c0 θ j)
    (φ : Fin n → ℝ → ℝ) (hφ : ∀ j, Monotone (φ j))
    (hφ_nn : ∀ j q, 0 ≤ φ j q)
    (κ : ℝ → ℝ) (hκ_nn : ∀ t, 0 ≤ κ t)
    (hκ_anti : Antitone κ)
    (q q' : Fin n → ℝ) (hq : q ≤ q')
    (t t' : ℝ) (ht : t ≤ t') :
    let F := fun q t => V q - κ t * P0 μ c0 φ q - C t
    F q' t' + F q t - F q' t - F q t' ≥ 0 := by
  intro F
  simp only [F]
  ring_nf
  have hκd : 0 ≤ κ t - κ t' := sub_nonneg.mpr (hκ_anti ht)
  have hPd : 0 ≤ P0 μ c0 φ q' - P0 μ c0 φ q :=
    sub_nonneg.mpr (P0_mono μ hμ c0 hc0 φ hφ hφ_nn q q' hq)
  nlinarith

end DE
