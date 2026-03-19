import DirectedEnvelopes.Defs
import Mathlib.Tactic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

noncomputable section
open Finset

namespace DE

variable {n : ℕ} [NeZero n]

inductive Walk (n : ℕ) : Fin n → Fin n → Type where
  | edge (i j : Fin n) : Walk n i j
  | cons (i j k : Fin n) (p : Walk n j k) : Walk n i k

def Walk.wt (w : Wt n) : Walk n s t → ℝ
  | .edge i j => w i j
  | .cons i j _ p => w i j + p.wt w

def Walk.cat : Walk n i j → Walk n j k → Walk n i k
  | .edge a b, q => .cons a b _ q
  | .cons a b c p, q => .cons a b _ (p.cat q)

theorem Walk.wt_cat (w : Wt n) :
    (p : Walk n i j) → (q : Walk n j k) →
    (p.cat q).wt w = p.wt w + q.wt w
  | .edge _ _, _ => by simp [cat, wt]
  | .cons _ _ _ p, q => by simp [cat, wt, wt_cat w p q]; ring

theorem Walk.wt_nn (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) :
    (p : Walk n s t) → 0 ≤ p.wt w
  | .edge i j => hw i j
  | .cons i j _ p => add_nonneg (hw i j) (p.wt_nn w hw)

theorem Walk.tele (w : Wt n) (r : Fin n → ℝ) (hr : DC w r) :
    (p : Walk n s t) → r t - r s ≤ p.wt w
  | .edge i j => hr i j
  | .cons i j _ p => by simp [wt]; linarith [hr i j, p.tele w r hr]

def WS (w : Wt n) (s t : Fin n) : Set ℝ :=
  {x | ∃ p : Walk n s t, x = p.wt w}

theorem ws_ne (w : Wt n) (s t : Fin n) : (WS w s t).Nonempty :=
  ⟨_, .edge s t, rfl⟩

theorem ws_bdd (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (s t : Fin n) :
    BddBelow (WS w s t) :=
  ⟨0, fun _ ⟨p, hx⟩ => hx ▸ p.wt_nn w hw⟩

def spd (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (s t : Fin n) : ℝ :=
  sInf (WS w s t)

theorem spd_le_wt (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (p : Walk n s t) :
    spd w hw s t ≤ p.wt w :=
  csInf_le (ws_bdd w hw s t) ⟨p, rfl⟩

theorem spd_le_w (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (s t : Fin n) :
    spd w hw s t ≤ w s t :=
  spd_le_wt w hw (.edge s t)

theorem spd_nn (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (s t : Fin n) :
    0 ≤ spd w hw s t :=
  le_csInf (ws_ne w s t) fun _ ⟨p, hx⟩ => hx ▸ p.wt_nn w hw

theorem spd_diag (w : Wt n) (hw : ∀ i j, 0 ≤ w i j)
    (hwd : ∀ i, w i i = 0) (s : Fin n) : spd w hw s s = 0 :=
  le_antisymm (by linarith [spd_le_w w hw s s, hwd s]) (spd_nn w hw s s)

theorem spd_tri (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (i j k : Fin n) :
    spd w hw i k ≤ spd w hw i j + spd w hw j k := by
  suffices h1 : ∀ a ∈ WS w i j, spd w hw i k - a ≤ spd w hw j k by
    have h2 : spd w hw i k - spd w hw j k ≤ sInf (WS w i j) :=
      le_csInf (ws_ne w i j) (fun a ha => by linarith [h1 a ha])
    have : spd w hw i j = sInf (WS w i j) := rfl
    linarith
  intro a ⟨p₁, ha⟩
  apply le_csInf (ws_ne w j k)
  intro b ⟨p₂, hb⟩
  have := spd_le_wt w hw (p₁.cat p₂)
  rw [Walk.wt_cat] at this
  linarith [ha, hb]

theorem spd_tight (w : Wt n) (hw : ∀ i j, 0 ≤ w i j)
    (r : Fin n → ℝ) (hr : DC w r) : DC (spd w hw) r := by
  intro θ k
  exact le_csInf (ws_ne w θ k) fun _ ⟨p, hx⟩ => hx ▸ p.tele w r hr

def mkClos (w : Wt n) (hw : ∀ i j, 0 ≤ w i j) (hwd : ∀ i, w i i = 0) :
    Clos w where
  d := spd w hw
  diag := spd_diag w hw hwd
  nn := spd_nn w hw
  lew := spd_le_w w hw
  tri := spd_tri w hw
  tight := spd_tight w hw

end DE
