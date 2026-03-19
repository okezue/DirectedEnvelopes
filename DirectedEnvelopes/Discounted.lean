import DirectedEnvelopes.Defs
import Mathlib.Tactic

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

structure DiscClos (n : ℕ) [NeZero n] where
  α : Fin n → Fin n → ℝ
  Δ : Fin n → Fin n → ℝ
  ρ : ℝ
  hρ : ρ < 1
  hρ0 : 0 ≤ ρ
  hα_nn : ∀ θ i, 0 ≤ α θ i
  hαρ : ∀ θ i, α θ i ≤ ρ

def discT (dc : DiscClos n) (b : Fin n → ℝ) (θ : Fin n) : ℝ :=
  max 0 (univ.sup' univ_nonempty (fun i => dc.α θ i * b i - dc.Δ θ i))

theorem discT_mono (dc : DiscClos n) :
    Monotone (fun b => fun θ => discT dc b θ) := by
  intro b₁ b₂ h θ
  simp only [discT]
  apply max_le_max_left
  apply sup'_le; intro i _
  have := mul_le_mul_of_nonneg_left (h i) (dc.hα_nn θ i)
  linarith [le_sup' (f := fun j => dc.α θ j * b₂ j - dc.Δ θ j) (mem_univ i)]

def discFeas' (dc : DiscClos n) (b : Fin n → ℝ) : Prop :=
  (∀ θ, 0 ≤ b θ) ∧ (∀ θ i, dc.α θ i * b i - dc.Δ θ i ≤ b θ)

theorem discFeas'_iff (dc : DiscClos n) (b : Fin n → ℝ) :
    discFeas' dc b ↔ ∀ θ, discT dc b θ ≤ b θ := by
  constructor
  · intro ⟨hnn, hic⟩ θ
    simp only [discT]
    exact max_le (hnn θ) (sup'_le _ _ (fun i _ => hic θ i))
  · intro h
    refine ⟨fun θ => le_trans (le_max_left _ _) (h θ), fun θ i => ?_⟩
    exact le_trans
      (le_trans (le_sup' (f := fun j => dc.α θ j * b j - dc.Δ θ j) (mem_univ i))
        (le_max_right _ _))
      (h θ)

def discIter (dc : DiscClos n) : ℕ → (Fin n → ℝ)
  | 0 => fun _ => 0
  | k + 1 => fun θ => discT dc (discIter dc k) θ

theorem discIter_mono (dc : DiscClos n) :
    ∀ k, discIter dc k ≤ discIter dc (k + 1) := by
  intro k
  induction k with
  | zero => intro θ; simp only [discIter, discT]; exact le_max_left 0 _
  | succ k ih => intro θ; simp only [discIter]; exact discT_mono dc ih θ

theorem discIter_le_sup (dc : DiscClos n) (b : Fin n → ℝ)
    (hb : discFeas' dc b) : ∀ k, discIter dc k ≤ b := by
  intro k
  induction k with
  | zero => intro θ; simp [discIter]; exact hb.1 θ
  | succ k ih =>
    intro θ; simp only [discIter]
    calc discT dc (discIter dc k) θ
        ≤ discT dc b θ := discT_mono dc ih θ
      _ ≤ b θ := (discFeas'_iff dc b).mp hb θ

private theorem pointwise_bound (dc : DiscClos n)
    (b₁ b₂ : Fin n → ℝ) (θ i : Fin n)
    (M : ℝ) (hM : ∀ j, |b₁ j - b₂ j| ≤ M) :
    dc.α θ i * b₁ i - dc.Δ θ i ≤
    (dc.α θ i * b₂ i - dc.Δ θ i) + dc.ρ * M := by
  have h1 : b₁ i - b₂ i ≤ |b₁ i - b₂ i| := le_abs_self _
  have h2 : |b₁ i - b₂ i| ≤ M := hM i
  have h3 : dc.α θ i * (b₁ i - b₂ i) ≤ dc.α θ i * M :=
    mul_le_mul_of_nonneg_left (le_trans h1 h2) (dc.hα_nn θ i)
  have h4 : dc.α θ i * M ≤ dc.ρ * M :=
    mul_le_mul_of_nonneg_right (dc.hαρ θ i) (le_trans (abs_nonneg _) (hM ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩))
  nlinarith

private theorem sup'_shift (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) :
    s.sup' hs (fun i => f i + c) = s.sup' hs f + c := by
  apply le_antisymm
  · apply sup'_le; intro i hi
    linarith [le_sup' f hi]
  · obtain ⟨j, hj, hjmax⟩ := exists_mem_eq_sup' hs f
    rw [hjmax]
    linarith [le_sup' (f := fun i => f i + c) hj]

private theorem max_zero_add_le (x c : ℝ) (hc : 0 ≤ c) :
    max 0 (x + c) ≤ max 0 x + c := by
  apply max_le
  · linarith [le_max_left 0 x]
  · linarith [le_max_right 0 x]

theorem discT_one_side (dc : DiscClos n) (b₁ b₂ : Fin n → ℝ) (θ : Fin n) :
    discT dc b₁ θ ≤ discT dc b₂ θ +
    dc.ρ * univ.sup' univ_nonempty (fun i => |b₁ i - b₂ i|) := by
  set M := univ.sup' univ_nonempty (fun i => |b₁ i - b₂ i|)
  set f₁ := fun i => dc.α θ i * b₁ i - dc.Δ θ i
  set f₂ := fun i => dc.α θ i * b₂ i - dc.Δ θ i
  have hM_nn : 0 ≤ dc.ρ * M := by
    apply mul_nonneg dc.hρ0
    apply le_trans (abs_nonneg (b₁ ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ - b₂ ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩))
    exact le_sup' (f := fun i => |b₁ i - b₂ i|) (mem_univ _)
  have hpw : ∀ i, |b₁ i - b₂ i| ≤ M :=
    fun i => le_sup' (f := fun j => |b₁ j - b₂ j|) (mem_univ i)
  have step1 : univ.sup' univ_nonempty f₁ ≤
      univ.sup' univ_nonempty f₂ + dc.ρ * M := by
    have hpw2 : ∀ i, f₁ i ≤ f₂ i + dc.ρ * M :=
      fun i => pointwise_bound dc b₁ b₂ θ i M hpw
    calc univ.sup' univ_nonempty f₁
        ≤ univ.sup' univ_nonempty (fun i => f₂ i + dc.ρ * M) :=
          sup'_le _ _ (fun i hi => le_trans (hpw2 i)
            (le_sup' (f := fun i => f₂ i + dc.ρ * M) hi))
      _ = univ.sup' univ_nonempty f₂ + dc.ρ * M :=
          sup'_shift _ _ f₂ (dc.ρ * M)
  simp only [discT]
  calc max 0 (univ.sup' univ_nonempty f₁)
      ≤ max 0 (univ.sup' univ_nonempty f₂ + dc.ρ * M) :=
        max_le_max_left 0 step1
    _ ≤ max 0 (univ.sup' univ_nonempty f₂) + dc.ρ * M :=
        max_zero_add_le _ _ hM_nn

theorem discT_contract (dc : DiscClos n) (b₁ b₂ : Fin n → ℝ) (θ : Fin n) :
    |discT dc b₁ θ - discT dc b₂ θ| ≤
    dc.ρ * univ.sup' univ_nonempty (fun i => |b₁ i - b₂ i|) := by
  rw [abs_le]
  have hsym : univ.sup' univ_nonempty (fun i => |b₂ i - b₁ i|) =
              univ.sup' univ_nonempty (fun i => |b₁ i - b₂ i|) := by
    congr 1; ext i; exact abs_sub_comm _ _
  have h12 := discT_one_side dc b₁ b₂ θ
  have h21 := discT_one_side dc b₂ b₁ θ
  rw [hsym] at h21
  constructor <;> linarith

end DE
