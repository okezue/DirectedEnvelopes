import DirectedEnvelopes.Defs
import Mathlib.Tactic

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

def MonoMargWedgeCost (P : ℝ → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ q q' : Fin n → ℝ, q ≤ q' →
    ∀ t t' : ℝ, t ≤ t' →
      P t' q' - P t' q ≤ P t q' - P t q

theorem single_crossing
    (V : (Fin n → ℝ) → ℝ) (P : ℝ → (Fin n → ℝ) → ℝ) (C : ℝ → ℝ)
    (hP : MonoMargWedgeCost P)
    (q q' : Fin n → ℝ) (hq : q ≤ q')
    (t t' : ℝ) (ht : t ≤ t')
    (hF : V q' - P t q' ≥ V q - P t q) :
    V q' - P t' q' ≥ V q - P t' q := by
  have hm := hP q q' hq t t' ht
  linarith

def QuasiSupermod (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ q q' : Fin n → ℝ,
    f q ≥ f (q ⊓ q') → f (q ⊔ q') ≥ f q'

theorem monotone_selection
    (V : (Fin n → ℝ) → ℝ) (P : ℝ → (Fin n → ℝ) → ℝ) (C : ℝ → ℝ)
    (hP : MonoMargWedgeCost P)
    (hQS : ∀ t, QuasiSupermod (fun q => V q - P t q))
    (q₁ q₂ : Fin n → ℝ)
    (t₁ t₂ : ℝ) (ht : t₁ ≤ t₂)
    (hopt₁ : ∀ q, V q - P t₁ q ≤ V q₁ - P t₁ q₁)
    (hopt₂ : ∀ q, V q - P t₂ q ≤ V q₂ - P t₂ q₂) :
    V (q₁ ⊔ q₂) - P t₂ (q₁ ⊔ q₂) ≤ V q₂ - P t₂ q₂ ∧
    V (q₁ ⊓ q₂) - P t₁ (q₁ ⊓ q₂) ≤ V q₁ - P t₁ q₁ :=
  ⟨hopt₂ (q₁ ⊔ q₂), hopt₁ (q₁ ⊓ q₂)⟩

theorem ms_increasing_differences
    (V : (Fin n → ℝ) → ℝ) (P : ℝ → (Fin n → ℝ) → ℝ) (C : ℝ → ℝ)
    (hP : MonoMargWedgeCost P)
    (t₁ t₂ : ℝ) (ht : t₁ ≤ t₂)
    (q q' : Fin n → ℝ) (hq : q ≤ q') :
    let F := fun q t => V q - P t q - C t
    F q' t₂ - F q t₂ ≥ F q' t₁ - F q t₁ := by
  simp only
  set a := V q'; set b := V q; set c := C t₁; set d := C t₂
  set p1 := P t₁ q'; set p2 := P t₁ q; set p3 := P t₂ q'; set p4 := P t₂ q
  have h := hP q q' hq t₁ t₂ ht
  change p3 - p4 ≤ p1 - p2 at h
  linarith

end DE
