
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_2 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + b * c + c * a > 0 → 1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b) ≥ 2 / (a * b + b * c + c * a) := by
  have h_main : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + b * c + c * a > 0 → 1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b) ≥ 2 / (a * b + b * c + c * a) := by
    intro a b c ⟨ha, hb, hc, h⟩
    have h₁ : 0 ≤ a * b := by nlinarith
    have h₂ : 0 ≤ b * c := by nlinarith
    have h₃ : 0 ≤ c * a := by nlinarith
    have h₄ : 0 < a * b + b * c + c * a := by nlinarith
    have h₅ : 0 ≤ a * b * c := by positivity
    have h₆ : 0 ≤ a * b * c * a := by positivity
    have h₇ : 0 ≤ a * b * c * b := by positivity
    have h₈ : 0 ≤ a * b * c * c := by positivity
    have h₉ : 0 < a * b + b * c + c * a := by nlinarith
    -- Use the Cauchy-Schwarz inequality to prove the desired inequality
    have h₁₀ : 0 < 2 * a ^ 2 + b * c := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h₁₁ : 0 < 2 * b ^ 2 + c * a := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h₁₂ : 0 < 2 * c ^ 2 + a * b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a)),
      mul_nonneg (sq_nonneg (b * c - c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (c * a - a * b)) (sq_nonneg (a * b - b * c))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_11 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≥ 10 / (a + b + c) ^ 2 := by
  intro a b c h
  have h_main : 1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2) ≥ 10 / (a + b + c) ^ 2 := by
    rcases h with ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h₅ : 0 < a * b * c * a := by positivity
    have h₆ : 0 < a * b * c * b := by positivity
    have h₇ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * c),
      sq_nonneg (a ^ 2 * b - a ^ 2 * c), sq_nonneg (b ^ 2 * c - b ^ 2 * a), sq_nonneg (c ^ 2 * a - c ^ 2 * b),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₃.le (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos (mul_pos ha hb) (mul_pos hb hc),
      mul_pos (mul_pos hb hc) (mul_pos hc ha), mul_pos (mul_pos hc ha) (mul_pos ha hb)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_27 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 2 * (1 / (a ^ 2 + 8 * b * c) + 1 / (b ^ 2 + 8 * c * a) + 1 / (c ^ 2 + 8 * a * b)) ≥ 1 / (a * b + b * c + c * a) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h_main : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 2 * (1 / (a ^ 2 + 8 * b * c) + 1 / (b ^ 2 + 8 * c * a) + 1 / (c ^ 2 + 8 * a * b)) ≥ 1 / (a * b + b * c + c * a) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h₅ : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by positivity
    have h₆ : 0 < a * b * c * (a * b + b * c + c * a) := by positivity
    have h₇ : 0 < a ^ 2 * b ^ 2 := by positivity
    have h₈ : 0 < b ^ 2 * c ^ 2 := by positivity
    have h₉ : 0 < c ^ 2 * a ^ 2 := by positivity
    have h₁₀ : 0 < a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) := by positivity
    -- Use the fact that the denominators are positive to apply the division inequality
    have h₁₁ : 2 * (1 / (a ^ 2 + 8 * b * c) + 1 / (b ^ 2 + 8 * c * a) + 1 / (c ^ 2 + 8 * a * b)) ≥ 1 / (a * b + b * c + c * a) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) := by
      field_simp
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * c),
        sq_nonneg (a ^ 2 * b - a ^ 2 * c), sq_nonneg (b ^ 2 * c - b ^ 2 * a), sq_nonneg (c ^ 2 * a - c ^ 2 * b),
        sq_nonneg (a * b * c * (a - b)), sq_nonneg (a * b * c * (b - c)), sq_nonneg (a * b * c * (c - a)),
        mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₃.le (sq_nonneg (c - a)),
        mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
        mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
        mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
        mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
    exact h₁₁
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_28 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 5 / 3 * (1 / (4 * a ^ 2 + b * c) + 1 / (4 * b ^ 2 + c * a) + 1 / (4 * c ^ 2 + a * b)) ≥ 2 / (a * b + b * c + c * a) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c h
  have h_main : 5 / 3 * (1 / (4 * a ^ 2 + b * c) + 1 / (4 * b ^ 2 + c * a) + 1 / (4 * c ^ 2 + a * b)) ≥ 2 / (a * b + b * c + c * a) + 1 / (a ^ 2 + b ^ 2 + c ^ 2) := by
    rcases h with ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h₅ : 0 < a * b * c * a := by positivity
    have h₆ : 0 < a * b * c * b := by positivity
    have h₇ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * c),
      sq_nonneg (a ^ 2 * b - a ^ 2 * c), sq_nonneg (b ^ 2 * a - b ^ 2 * c), sq_nonneg (c ^ 2 * a - c ^ 2 * b),
      sq_nonneg (a * b * c * (a - b)), sq_nonneg (a * b * c * (b - c)), sq_nonneg (a * b * c * (c - a)),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₃.le (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos (mul_pos ha hb) (mul_pos hb hc),
      mul_pos (mul_pos hb hc) (mul_pos hc ha), mul_pos (mul_pos hc ha) (mul_pos ha hb)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_567_29 : ∀ (a b c d e : ℝ), a + b + c + d + e = 0 → 30 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + e ^ 4) ≥ 7 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  intro a b c d e h
  have h_main : 30 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + e ^ 4) ≥ 7 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    have h1 : e = -(a + b + c + d) := by linarith
    rw [h1]
    nlinarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), sq_nonneg (b + c - a - d), sq_nonneg (b + d - a - c),
      sq_nonneg (c + d - a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - d^2), sq_nonneg (b^2 - c^2), sq_nonneg (b^2 - d^2),
      sq_nonneg (c^2 - d^2)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_37 : ∀ (a b : ℝ), 9 * a ^ 2 + 8 * a * b + 7 * b ^ 2 ≤ 6 → 7 * a + 5 * b + 12 * a * b ≤ 9 := by
  intro a b h
  have h₁ : 7 * a + 5 * b + 12 * a * b ≤ 9 := by
    nlinarith [sq_nonneg (a - b / 2), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2),
      sq_nonneg (a + b), sq_nonneg (a - 3 / 2), sq_nonneg (b + 3 / 2),
      sq_nonneg (3 * a + 4 * b), sq_nonneg (3 * a - 4 * b), sq_nonneg (a + 4 * b),
      sq_nonneg (a - 4 * b), sq_nonneg (3 * a + b), sq_nonneg (3 * a - b),
      sq_nonneg (a + 2 * b), sq_nonneg (a - 2 * b), sq_nonneg (3 * a + 2 * b),
      sq_nonneg (3 * a - 2 * b), sq_nonneg (2 * a + 3 * b), sq_nonneg (2 * a - 3 * b)]
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_45 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a) ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 := by
  intro a b c h
  have h_main : a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a) ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₃.le (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
      mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
      mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂), mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃),
      mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁), mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_56 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ (a + b + c) / (2 * (a * b + b * c + c * a)) + 3 / (a + b + c) := by
  intro a b c h
  have h_main : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ (a + b + c) / (2 * (a * b + b * c + c * a)) + 3 / (a + b + c) := by
    rcases h with ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := by positivity
    have h₅ : 0 < a * b ^ 2 := by positivity
    have h₆ : 0 < b * c ^ 2 := by positivity
    have h₇ : 0 < c * a ^ 2 := by positivity
    have h₈ : 0 < a ^ 2 * b := by positivity
    have h₉ : 0 < b ^ 2 * c := by positivity
    have h₁₀ : 0 < c ^ 2 * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - c * a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_83 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a → a / (2 * a ^ 2 + b * c) + b / (2 * b ^ 2 + c * a) + c / (2 * c ^ 2 + a * b) ≥ (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c h
  have h_main : a / (2 * a ^ 2 + b * c) + b / (2 * b ^ 2 + c * a) + c / (2 * c ^ 2 + a * b) ≥ (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2) := by
    rcases h with ⟨ha, hb, hc, habc, hacb, hbc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < a * c := mul_pos ha hc
    have h₃ : 0 < b * c := mul_pos hb hc
    have h₄ : 0 < a * b * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (a ^ 2 * c - c ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b),
      sq_nonneg (a ^ 2 * b - a ^ 2 * c), sq_nonneg (b ^ 2 * a - b ^ 2 * c), sq_nonneg (c ^ 2 * a - c ^ 2 * b),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - c)), mul_pos (mul_pos ha hb) (mul_pos ha hc),
      mul_pos (mul_pos ha hb) (mul_pos hb hc), mul_pos (mul_pos ha hc) (mul_pos ha hb),
      mul_pos (mul_pos ha hc) (mul_pos hb hc), mul_pos (mul_pos hb hc) (mul_pos ha hb),
      mul_pos (mul_pos hb hc) (mul_pos ha hc)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_567_85 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + b * c + c * a > 0 → 1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b) ≥ 2 / (a * b + b * c + c * a) := by
  have h_main : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + b * c + c * a > 0 → 1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b) ≥ 2 / (a * b + b * c + c * a) := by
    intro a b c ⟨ha, hb, hc, h⟩
    have h₁ : 0 ≤ a * b := by nlinarith
    have h₂ : 0 ≤ b * c := by nlinarith
    have h₃ : 0 ≤ c * a := by nlinarith
    have h₄ : 0 < a * b + b * c + c * a := by nlinarith
    have h₅ : 0 < 2 * a ^ 2 + b * c := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]
    have h₆ : 0 < 2 * b ^ 2 + c * a := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]
    have h₇ : 0 < 2 * c ^ 2 + a * b := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]
    have h₈ : 0 < a * b + b * c + c * a := by nlinarith
    have h₉ : 0 < (2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b) := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a)),
      mul_nonneg (sq_nonneg (b * c - c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (c * a - a * b)) (sq_nonneg (a * b - b * c))]
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem leanqr_int_pall : (12 : ℤ) ^ 2 = 144 := by norm_num

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_96 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a ^ 2 + b * c) * (b + c) / (b ^ 2 + b * c + c ^ 2) + (b ^ 2 + c * a) * (c + a) / (c ^ 2 + c * a + a ^ 2) + (c ^ 2 + a * b) * (a + b) / (a ^ 2 + a * b + b ^ 2) ≥ 4 / 3 * (a + b + c) := by
  intro a b c h
  have h_main : (a ^ 2 + b * c) * (b + c) / (b ^ 2 + b * c + c ^ 2) + (b ^ 2 + c * a) * (c + a) / (c ^ 2 + c * a + a ^ 2) + (c ^ 2 + a * b) * (a + b) / (a ^ 2 + a * b + b ^ 2) ≥ 4 / 3 * (a + b + c) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b ^ 2 := by positivity
    have h₉ : 0 < b * c ^ 2 := by positivity
    have h₁₀ : 0 < c * a ^ 2 := by positivity
    have h₁₁ : 0 < a ^ 2 * b := by positivity
    have h₁₂ : 0 < b ^ 2 * c := by positivity
    have h₁₃ : 0 < c ^ 2 * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₄.le (sq_nonneg (a - b)), mul_nonneg h₅.le (sq_nonneg (b - c)),
      mul_nonneg h₆.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (c + a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_111 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → (a * b * c + 1) / ((a + 1) * (b + 1) * (c + 1)) ≥ (a * b * c - 1) ^ 2 / ((a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1)) := by
  intro a b c h
  have h_main : (a * b * c + 1) / ((a + 1) * (b + 1) * (c + 1)) ≥ (a * b * c - 1) ^ 2 / ((a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1)) := by
    have h₁ : 0 ≤ a := by linarith
    have h₂ : 0 ≤ b := by linarith
    have h₃ : 0 ≤ c := by linarith
    have h₄ : 0 ≤ a * b := by positivity
    have h₅ : 0 ≤ b * c := by positivity
    have h₆ : 0 ≤ c * a := by positivity
    have h₇ : 0 ≤ a * b * c := by positivity
    -- We use the fact that the denominator on the right is larger than the denominator on the left
    have h₈ : (a + 1) * (b + 1) * (c + 1) > 0 := by positivity
    have h₉ : (a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1) > 0 := by positivity
    -- Use the division inequality to compare the fractions
    have h₁₀ : (a * b * c + 1) / ((a + 1) * (b + 1) * (c + 1)) ≥ (a * b * c - 1) ^ 2 / ((a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1)) := by
      -- Use the division inequality to compare the fractions
      have h₁₁ : 0 ≤ a * b * c := by positivity
      have h₁₂ : 0 ≤ a * b * c * a := by positivity
      have h₁₃ : 0 ≤ a * b * c * b := by positivity
      have h₁₄ : 0 ≤ a * b * c * c := by positivity
      -- Use the division inequality to compare the fractions
      field_simp [h₈, h₉]
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to verify the inequality
      nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁,
        mul_nonneg (mul_nonneg h₁ h₂) h₃, mul_nonneg (mul_nonneg h₂ h₃) h₁,
        mul_nonneg (mul_nonneg h₃ h₁) h₂, mul_nonneg (sq_nonneg (a - 1)) h₂,
        mul_nonneg (sq_nonneg (b - 1)) h₃, mul_nonneg (sq_nonneg (c - 1)) h₁,
        mul_nonneg (sq_nonneg (a - 1)) (mul_nonneg h₂ h₃),
        mul_nonneg (sq_nonneg (b - 1)) (mul_nonneg h₃ h₁),
        mul_nonneg (sq_nonneg (c - 1)) (mul_nonneg h₁ h₂)]
    exact h₁₀
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_119 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥ (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) * (a * b + b * c + c * a) ^ 2 + 10 * a ^ 2 * b ^ 2 * c ^ 2 := by
  intro a b c h
  have h_main : (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 ≥ (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) * (a * b + b * c + c * a) ^ 2 + 10 * a ^ 2 * b ^ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h.1 h.2.1, mul_nonneg h.2.1 h.2.2, mul_nonneg h.2.2 h.1,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a + b - c)) (sq_nonneg (a - b)), mul_nonneg (sq_nonneg (b + c - a)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (c + a - b)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a * b + b * c + c * a)) (sq_nonneg (a * b - b * c)),
      mul_nonneg (sq_nonneg (a * b + b * c + c * a)) (sq_nonneg (b * c - c * a)), mul_nonneg (sq_nonneg (a * b + b * c + c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a)), mul_nonneg (sq_nonneg (b * c - c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (c * a - a * b)) (sq_nonneg (a * b - b * c))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_121 : ∀ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z → Real.sqrt (x ^ 2 + x * y + y ^ 2) + Real.sqrt (y ^ 2 + y * z + z ^ 2) + Real.sqrt (z ^ 2 + z * x + x ^ 2) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
  intro x y z h
  have h₁ : Real.sqrt (x ^ 2 + x * y + y ^ 2) ≥ (Real.sqrt 3 / 2) * (x + y) := by
    have h₂ : 0 < x := by linarith
    have h₃ : 0 < y := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < Real.sqrt 3 := by positivity
    have h₆ : 0 < Real.sqrt 3 * x := by positivity
    have h₇ : 0 < Real.sqrt 3 * y := by positivity
    -- Use the fact that the square root of a non-negative number is non-negative.
    have h₈ : 0 ≤ Real.sqrt (x ^ 2 + x * y + y ^ 2) := by positivity
    have h₉ : 0 ≤ Real.sqrt 3 := by positivity
    -- Use the fact that the square root of a non-negative number is non-negative.
    have h₁₀ : (Real.sqrt 3 / 2) * (x + y) ≤ Real.sqrt (x ^ 2 + x * y + y ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), sq_nonneg (x - y), sq_nonneg (x + y),
        sq_nonneg (Real.sqrt 3 * x - Real.sqrt 3 * y), Real.sq_sqrt (show 0 ≤ 3 by norm_num),
        sq_nonneg (x + y - Real.sqrt 3 * (x - y))]
    linarith
  
  have h₂ : Real.sqrt (y ^ 2 + y * z + z ^ 2) ≥ (Real.sqrt 3 / 2) * (y + z) := by
    have h₃ : 0 < y := by linarith
    have h₄ : 0 < z := by linarith
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < Real.sqrt 3 := by positivity
    have h₇ : 0 < Real.sqrt 3 * y := by positivity
    have h₈ : 0 < Real.sqrt 3 * z := by positivity
    have h₉ : 0 ≤ Real.sqrt (y ^ 2 + y * z + z ^ 2) := by positivity
    have h₁₀ : (Real.sqrt 3 / 2) * (y + z) ≤ Real.sqrt (y ^ 2 + y * z + z ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), sq_nonneg (y - z), sq_nonneg (y + z),
        sq_nonneg (Real.sqrt 3 * y - Real.sqrt 3 * z), Real.sq_sqrt (show 0 ≤ 3 by norm_num),
        sq_nonneg (y + z - Real.sqrt 3 * (y - z))]
    linarith
  
  have h₃ : Real.sqrt (z ^ 2 + z * x + x ^ 2) ≥ (Real.sqrt 3 / 2) * (z + x) := by
    have h₄ : 0 < z := by linarith
    have h₅ : 0 < x := by linarith
    have h₆ : 0 < z * x := by positivity
    have h₇ : 0 < Real.sqrt 3 := by positivity
    have h₈ : 0 < Real.sqrt 3 * z := by positivity
    have h₉ : 0 < Real.sqrt 3 * x := by positivity
    have h₁₀ : 0 ≤ Real.sqrt (z ^ 2 + z * x + x ^ 2) := by positivity
    have h₁₁ : (Real.sqrt 3 / 2) * (z + x) ≤ Real.sqrt (z ^ 2 + z * x + x ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), sq_nonneg (z - x), sq_nonneg (z + x),
        sq_nonneg (Real.sqrt 3 * z - Real.sqrt 3 * x), Real.sq_sqrt (show 0 ≤ 3 by norm_num),
        sq_nonneg (z + x - Real.sqrt 3 * (z - x))]
    linarith
  
  have h₄ : Real.sqrt (x ^ 2 + x * y + y ^ 2) + Real.sqrt (y ^ 2 + y * z + z ^ 2) + Real.sqrt (z ^ 2 + z * x + x ^ 2) ≥ Real.sqrt 3 * (x + y + z) := by
    have h₅ : Real.sqrt (x ^ 2 + x * y + y ^ 2) + Real.sqrt (y ^ 2 + y * z + z ^ 2) + Real.sqrt (z ^ 2 + z * x + x ^ 2) ≥ (Real.sqrt 3 / 2) * (x + y) + (Real.sqrt 3 / 2) * (y + z) + (Real.sqrt 3 / 2) * (z + x) := by
      linarith [h₁, h₂, h₃]
    have h₆ : (Real.sqrt 3 / 2) * (x + y) + (Real.sqrt 3 / 2) * (y + z) + (Real.sqrt 3 / 2) * (z + x) = Real.sqrt 3 * (x + y + z) := by
      ring_nf
      <;>
      field_simp [Real.sqrt_eq_iff_sq_eq] <;>
      ring_nf <;>
      nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
    linarith
  
  have h₅ : Real.sqrt 3 * (x + y + z) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
    have h₅₁ : 0 < x := by linarith
    have h₅₂ : 0 < y := by linarith
    have h₅₃ : 0 < z := by linarith
    have h₅₄ : 0 < x * y := by positivity
    have h₅₅ : 0 < y * z := by positivity
    have h₅₆ : 0 < z * x := by positivity
    have h₅₇ : Real.sqrt 3 ≥ 0 := by positivity
    have h₅₈ : Real.sqrt (x * y + y * z + z * x) ≥ 0 := by positivity
    have h₅₉ : (Real.sqrt 3) * (x + y + z) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
      have h₅₉₁ : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      have h₅₉₂ : Real.sqrt 3 * (x + y + z) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
        have h₅₉₃ : Real.sqrt 3 * (x + y + z) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
          have h₅₉₄ : Real.sqrt 3 * (x + y + z) = Real.sqrt 3 * (x + y + z) := by rfl
          have h₅₉₅ : 3 * Real.sqrt (x * y + y * z + z * x) = 3 * Real.sqrt (x * y + y * z + z * x) := by rfl
          have h₅₉₆ : Real.sqrt 3 * (x + y + z) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
            apply le_of_pow_le_pow_left two_ne_zero (by positivity)
            nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sq_sqrt (show 0 ≤ x * y + y * z + z * x by positivity),
              Real.sqrt_nonneg (x * y + y * z + z * x), sq_nonneg (x + y + z - Real.sqrt 3 * Real.sqrt (x * y + y * z + z * x))]
          linarith
        linarith
      linarith
    linarith
  
  have h_main : Real.sqrt (x ^ 2 + x * y + y ^ 2) + Real.sqrt (y ^ 2 + y * z + z ^ 2) + Real.sqrt (z ^ 2 + z * x + x ^ 2) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
    have h₆ : Real.sqrt (x ^ 2 + x * y + y ^ 2) + Real.sqrt (y ^ 2 + y * z + z ^ 2) + Real.sqrt (z ^ 2 + z * x + x ^ 2) ≥ Real.sqrt 3 * (x + y + z) := by
      linarith [h₄]
    have h₇ : Real.sqrt 3 * (x + y + z) ≥ 3 * Real.sqrt (x * y + y * z + z * x) := by
      linarith [h₅]
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_125 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 + 8 * a * b * c / ((a + b) * (b + c) * (c + a)) ≥ 2 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c h
  have h_main : 1 + 8 * a * b * c / ((a + b) * (b + c) * (c + a)) ≥ 2 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h₀ : 0 < a := by linarith
    have h₁ : 0 < b := by linarith
    have h₂ : 0 < c := by linarith
    have h₃ : 0 < a * b := by positivity
    have h₄ : 0 < b * c := by positivity
    have h₅ : 0 < c * a := by positivity
    have h₆ : 0 < a * b * c := by positivity
    have h₇ : 0 < a * b * c * a := by positivity
    have h₈ : 0 < a * b * c * b := by positivity
    have h₉ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * c),
      sq_nonneg (a ^ 2 * b - a ^ 2 * c), sq_nonneg (b ^ 2 * a - b ^ 2 * c), sq_nonneg (c ^ 2 * a - c ^ 2 * b),
      mul_nonneg h₃.le (sq_nonneg (a - b)), mul_nonneg h₄.le (sq_nonneg (b - c)), mul_nonneg h₅.le (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₂ h₀,
      mul_pos (mul_pos h₀ h₁) (mul_pos h₁ h₂), mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₀),
      mul_pos (mul_pos h₂ h₀) (mul_pos h₀ h₁)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_128 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ≥ (a * b + b * c + c * a) ^ 3 := by
  have h_main : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ≥ (a * b + b * c + c * a) ^ 3 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 ≤ a * b := by positivity
    have h₂ : 0 ≤ b * c := by positivity
    have h₃ : 0 ≤ c * a := by positivity
    have h₄ : 0 ≤ a * b * c := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a)),
      mul_nonneg (sq_nonneg (b * c - c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (c * a - a * b)) (sq_nonneg (a * b - b * c)),
      mul_nonneg (sq_nonneg (a * b + b * c + c * a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a * b + b * c + c * a)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (a * b + b * c + c * a)) (sq_nonneg (c - a))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_134 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a + b) / (a + b + 2 * c) + (b + c) / (b + c + 2 * a) + (c + a) / (c + a + 2 * b) + 2 * (a * b + b * c + c * a) / (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ≤ 13 / 6 := by
  have h_main : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a + b) / (a + b + 2 * c) + (b + c) / (b + c + 2 * a) + (c + a) / (c + a + 2 * b) + 2 * (a * b + b * c + c * a) / (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ≤ 13 / 6 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)),
      mul_nonneg h₃.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (c + a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_567_135 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → ((a + b) / b) ^ 2 + ((b + c) / c) ^ 2 + ((c + a) / a) ^ 2 ≥ 8 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 4 := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 < b * c := by positivity
  have h₆ : 0 < c * a := by positivity
  have h₇ : 0 < a * b + b * c + c * a := by positivity
  have h₈ : ((a + b) / b) ^ 2 + ((b + c) / c) ^ 2 + ((c + a) / a) ^ 2 ≥ 8 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 4 := by
    have h₉ : 0 < a * b * c := by positivity
    have h₁₀ : 0 < a ^ 2 := by positivity
    have h₁₁ : 0 < b ^ 2 := by positivity
    have h₁₂ : 0 < c ^ 2 := by positivity
    have h₁₃ : 0 < a * b ^ 2 := by positivity
    have h₁₄ : 0 < b * c ^ 2 := by positivity
    have h₁₅ : 0 < c * a ^ 2 := by positivity
    have h₁₆ : 0 < a ^ 2 * b := by positivity
    have h₁₇ : 0 < b ^ 2 * c := by positivity
    have h₁₈ : 0 < c ^ 2 * a := by positivity
    have h₁₉ : 0 < a ^ 2 * b ^ 2 := by positivity
    have h₂₀ : 0 < b ^ 2 * c ^ 2 := by positivity
    have h₂₁ : 0 < c ^ 2 * a ^ 2 := by positivity
    -- Use the division inequality to clear denominators
    have h₂₂ : ((a + b) / b) ^ 2 + ((b + c) / c) ^ 2 + ((c + a) / a) ^ 2 ≥ 8 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 4 := by
      field_simp [h₁.ne', h₂.ne', h₃.ne', h₇.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to handle the inequality
      nlinarith [sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c),
        sq_nonneg (a ^ 2 * c - a * b * c), sq_nonneg (b ^ 2 * a - a * b * c), sq_nonneg (c ^ 2 * b - a * b * c),
        mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁, mul_pos (sq_pos_of_pos h₁) h₂, mul_pos (sq_pos_of_pos h₂) h₃,
        mul_pos (sq_pos_of_pos h₃) h₁, mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
        mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
    exact h₂₂
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_136 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a * b / (c * (c + a)) + b * c / (a * (a + b)) + c * a / (b * (b + c)) ≥ a / (a + b) + b / (b + c) + c / (c + a) := by
  intro a b c h
  have h_main : a * b / (c * (c + a)) + b * c / (a * (a + b)) + c * a / (b * (b + c)) ≥ a / (a + b) + b / (b + c) + c / (c + a) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a ^ 2 := by positivity
    have h₉ : 0 < b ^ 2 := by positivity
    have h₁₀ : 0 < c ^ 2 := by positivity
    have h₁₁ : 0 < a * b ^ 2 := by positivity
    have h₁₂ : 0 < b * c ^ 2 := by positivity
    have h₁₃ : 0 < c * a ^ 2 := by positivity
    have h₁₄ : 0 < a ^ 2 * b := by positivity
    have h₁₅ : 0 < b ^ 2 * c := by positivity
    have h₁₆ : 0 < c ^ 2 * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * b * (a - b)), sq_nonneg (b * c * (b - c)), sq_nonneg (c * a * (c - a)),
      sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
      sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c),
      sq_nonneg (a * b * c * (a - b)), sq_nonneg (a * b * c * (b - c)), sq_nonneg (a * b * c * (c - a))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_147 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3 → a * b + b * c + c * a ≤ a * b * c + 2 := by
  intro a b c h
  have h_main : a * b + b * c + c * a ≤ a * b * c + 2 := by
    rcases h with ⟨ha, hb, hc, h⟩
    have h₁ : 0 < a * b := by positivity
    have h₂ : 0 < b * c := by positivity
    have h₃ : 0 < c * a := by positivity
    have h₄ : 0 < a * b * c := by positivity
    -- Use non-linear arithmetic to prove the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 3)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_149 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a * b + b * c + c * a) ^ 3 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a + b + c) ^ 3 := by
  intro a b c h
  have h_main : (a * b + b * c + c * a) ^ 3 ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a + b + c) ^ 3 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b * c * a := by positivity
    have h₉ : 0 < a * b * c * b := by positivity
    have h₁₀ : 0 < a * b * c * c := by positivity
    -- Use `nlinarith` to handle the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₄.le (sq_nonneg (a - b)), mul_nonneg h₅.le (sq_nonneg (b - c)),
      mul_nonneg h₆.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a)),
      mul_nonneg (sq_nonneg (b * c - c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (c * a - a * b)) (sq_nonneg (a * b - b * c)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_151 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a * b * c / (a ^ 3 + b ^ 3 + c ^ 3) + (a ^ 2 + b ^ 2 + c ^ 2) / (a * c + a * b + b * c) ≥ 4 / 3 := by
  intro a b c h
  have h_main : a * b * c / (a ^ 3 + b ^ 3 + c ^ 3) + (a ^ 2 + b ^ 2 + c ^ 2) / (a * c + a * b + b * c) ≥ 4 / 3 := by
    rcases h with ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b * c := by positivity
    have h₂ : 0 < a * b := by positivity
    have h₃ : 0 < a * c := by positivity
    have h₄ : 0 < b * c := by positivity
    have h₅ : 0 < a * b * c := by positivity
    have h₆ : 0 < a * b * c * a := by positivity
    have h₇ : 0 < a * b * c * b := by positivity
    have h₈ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_nonneg h₂.le (sq_nonneg (a - b)), mul_nonneg h₃.le (sq_nonneg (a - c)),
      mul_nonneg h₄.le (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - c)),
      mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)),
      mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (a + c - b)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_158 : ∀ (x y z k : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < k → (x ^ 2 + y ^ 2) / (z + k) + (y ^ 2 + z ^ 2) / (x + k) + (z ^ 2 + x ^ 2) / (y + k) ≥ 3 / 2 * (x + y + z - k) := by
  have h_main : ∀ (x y z k : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < k → (x ^ 2 + y ^ 2) / (z + k) + (y ^ 2 + z ^ 2) / (x + k) + (z ^ 2 + x ^ 2) / (y + k) ≥ 3 / 2 * (x + y + z - k) := by
    intro x y z k h
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have hz : 0 < z := by linarith
    have hk : 0 < k := by linarith
    have h₁ : 0 < x * y := mul_pos hx hy
    have h₂ : 0 < y * z := mul_pos hy hz
    have h₃ : 0 < z * x := mul_pos hz hx
    have h₄ : 0 < x * k := mul_pos hx hk
    have h₅ : 0 < y * k := mul_pos hy hk
    have h₆ : 0 < z * k := mul_pos hz hk
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - k), sq_nonneg (y - k), sq_nonneg (z - k),
      mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)),
      mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (z - x)),
      mul_nonneg (sq_nonneg (z - x)) (sq_nonneg (x - y)),
      mul_nonneg (sq_nonneg (x - k)) (sq_nonneg (y - k)),
      mul_nonneg (sq_nonneg (y - k)) (sq_nonneg (z - k)),
      mul_nonneg (sq_nonneg (z - k)) (sq_nonneg (x - k))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_159 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a * b + b * c + c * a ≤ a ^ 4 + b ^ 4 + c ^ 4 + 3 / 4 := by
  intro a b c h
  have h₁ : a ^ 4 + 1 / 4 ≥ a ^ 2 := by
    have h₁₁ : a ^ 4 - a ^ 2 + 1 / 4 ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2)]
    linarith
  
  have h₂ : b ^ 4 + 1 / 4 ≥ b ^ 2 := by
    have h₂₁ : b ^ 4 - b ^ 2 + 1 / 4 ≥ 0 := by
      nlinarith [sq_nonneg (b ^ 2 - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (b + 1 / 2)]
    linarith
  
  have h₃ : c ^ 4 + 1 / 4 ≥ c ^ 2 := by
    have h₃₁ : c ^ 4 - c ^ 2 + 1 / 4 ≥ 0 := by
      nlinarith [sq_nonneg (c ^ 2 - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (c + 1 / 2)]
    linarith
  
  have h₄ : a ^ 4 + b ^ 4 + c ^ 4 + 3 / 4 ≥ a ^ 2 + b ^ 2 + c ^ 2 := by
    linarith
  
  have h₅ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₅₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₆ : a * b + b * c + c * a ≤ a ^ 4 + b ^ 4 + c ^ 4 + 3 / 4 := by
    linarith
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_162 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 3 → a + a * b + 2 * a * b * c ≤ 9 / 2 := by
  intro a b c h
  have h₁ : a + a * b + 2 * a * b * c ≤ 9 / 2 := by
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    have h₄ : 0 ≤ c := by linarith
    have h₅ : a + b + c = 3 := by linarith
    by_cases h₆ : a ≤ 7 / 2
    · -- Case: a ≤ 7/2
      have h₇ : a + a * b + 2 * a * b * c ≤ 9 / 2 := by
        have h₇₁ : 0 ≤ a * b := by positivity
        have h₇₂ : 0 ≤ b * c := by positivity
        have h₇₃ : 0 ≤ a * b * c := by positivity
        have h₇₄ : 0 ≤ 2 * a * b * c := by positivity
        have h₇₅ : a + a * b + 2 * a * b * c = a + a * b * (1 + 2 * c) := by ring
        rw [h₇₅]
        have h₇₆ : c = 3 - a - b := by linarith
        rw [h₇₆]
        have h₇₇ : a + a * b * (1 + 2 * (3 - a - b)) ≤ 9 / 2 := by
          nlinarith [sq_nonneg (2 * a - 3), sq_nonneg (a - 3), sq_nonneg (b - (7 - 2 * a) / 4),
            mul_nonneg h₂ h₃, mul_nonneg h₃ h₄, mul_nonneg h₂ h₄,
            mul_nonneg (sub_nonneg.mpr h₆) h₂, mul_nonneg (sub_nonneg.mpr h₆) h₃]
        linarith
      exact h₇
    · -- Case: a > 7/2
      have h₇ : a + a * b + 2 * a * b * c ≤ 9 / 2 := by
        have h₇₁ : 0 ≤ a * b := by positivity
        have h₇₂ : 0 ≤ b * c := by positivity
        have h₇₃ : 0 ≤ a * b * c := by positivity
        have h₇₄ : 0 ≤ 2 * a * b * c := by positivity
        have h₇₅ : b ≤ 1 / 2 := by
          nlinarith
        have h₇₆ : c ≤ 1 / 2 := by
          nlinarith
        have h₇₇ : a + a * b + 2 * a * b * c ≤ 2 * a := by
          nlinarith [mul_nonneg h₂ h₃, mul_nonneg h₂ h₄, mul_nonneg h₃ h₄]
        have h₇₈ : 2 * a ≤ 9 / 2 := by
          nlinarith
        linarith
      exact h₇
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_167 : ∀ (a b c : ℝ), (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ 4 / 7 * (a + b + c) ^ 4 := by
  have h_main : ∀ (a b c : ℝ), (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥ 4 / 7 * (a + b + c) ^ 4 := by
    intro a b c
    nlinarith [sq_nonneg ((a + b) ^ 2 - (b + c) ^ 2), sq_nonneg ((b + c) ^ 2 - (c + a) ^ 2), sq_nonneg ((c + a) ^ 2 - (a + b) ^ 2),
      sq_nonneg ((a + b + c) ^ 2), sq_nonneg ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2),
      sq_nonneg ((a + b - 2 * c) ^ 2), sq_nonneg ((b + c - 2 * a) ^ 2), sq_nonneg ((c + a - 2 * b) ^ 2),
      sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_169 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a - b) ^ 2 / c ^ 2 + (b - c) ^ 2 / a ^ 2 + (c - a) ^ 2 / b ^ 2 ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (3 * a ^ 2 * b ^ 2 * c ^ 2) := by
  intro a b c h
  have h_main : 3 * ((a - b) ^ 2 * a ^ 2 * b ^ 2 + (b - c) ^ 2 * b ^ 2 * c ^ 2 + (c - a) ^ 2 * c ^ 2 * a ^ 2) ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b * c * a := by positivity
    have h₉ : 0 < a * b * c * b := by positivity
    have h₁₀ : 0 < a * b * c * c := by positivity
    -- Use non-linear arithmetic to prove the inequality
    nlinarith [sq_nonneg ((a - b) * a * b - (b - c) * b * c), sq_nonneg ((b - c) * b * c - (c - a) * c * a), sq_nonneg ((c - a) * c * a - (a - b) * a * b),
      sq_nonneg ((a - b) * a * b + (b - c) * b * c), sq_nonneg ((b - c) * b * c + (c - a) * c * a), sq_nonneg ((c - a) * c * a + (a - b) * a * b),
      mul_nonneg (sq_nonneg (a * b * c)) (sq_nonneg ((a - b) * (b - c) * (c - a))),
      mul_nonneg (sq_nonneg (a * b * c)) (sq_nonneg ((a - b) * a * b)),
      mul_nonneg (sq_nonneg (a * b * c)) (sq_nonneg ((b - c) * b * c)),
      mul_nonneg (sq_nonneg (a * b * c)) (sq_nonneg ((c - a) * c * a))]
  
  have h_final : (a - b) ^ 2 / c ^ 2 + (b - c) ^ 2 / a ^ 2 + (c - a) ^ 2 / b ^ 2 ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (3 * a ^ 2 * b ^ 2 * c ^ 2) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a ^ 2 := by positivity
    have h₉ : 0 < b ^ 2 := by positivity
    have h₁₀ : 0 < c ^ 2 := by positivity
    have h₁₁ : 0 < a ^ 2 * b ^ 2 := by positivity
    have h₁₂ : 0 < b ^ 2 * c ^ 2 := by positivity
    have h₁₃ : 0 < c ^ 2 * a ^ 2 := by positivity
    have h₁₄ : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by positivity
    have h₁₅ : 0 < a ^ 2 * b ^ 2 * c ^ 2 * 3 := by positivity
    -- Use the main inequality to prove the final result
    have h₁₆ : 3 * ((a - b) ^ 2 * a ^ 2 * b ^ 2 + (b - c) ^ 2 * b ^ 2 * c ^ 2 + (c - a) ^ 2 * c ^ 2 * a ^ 2) ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 := by
      exact h_main
    have h₁₇ : (a - b) ^ 2 / c ^ 2 + (b - c) ^ 2 / a ^ 2 + (c - a) ^ 2 / b ^ 2 ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (3 * a ^ 2 * b ^ 2 * c ^ 2) := by
      have h₁₈ : (a - b) ^ 2 / c ^ 2 + (b - c) ^ 2 / a ^ 2 + (c - a) ^ 2 / b ^ 2 = ((a - b) ^ 2 * a ^ 2 * b ^ 2 + (b - c) ^ 2 * b ^ 2 * c ^ 2 + (c - a) ^ 2 * c ^ 2 * a ^ 2) / (a ^ 2 * b ^ 2 * c ^ 2) := by
        field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne', h₅.ne', h₆.ne', h₇.ne', h₈.ne', h₉.ne', h₁₀.ne', h₁₁.ne', h₁₂.ne', h₁₃.ne', h₁₄.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne', h₅.ne', h₆.ne', h₇.ne', h₈.ne', h₉.ne', h₁₀.ne', h₁₁.ne', h₁₂.ne', h₁₃.ne', h₁₄.ne']
        <;> ring
      rw [h₁₈]
      have h₁₉ : ((a - b) ^ 2 * a ^ 2 * b ^ 2 + (b - c) ^ 2 * b ^ 2 * c ^ 2 + (c - a) ^ 2 * c ^ 2 * a ^ 2) / (a ^ 2 * b ^ 2 * c ^ 2) ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (3 * a ^ 2 * b ^ 2 * c ^ 2) := by
        rw [ge_iff_le]
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [h₁₆]
      exact h₁₉
    exact h₁₇
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_175 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 3 → a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 3 * a * b * c ≤ 12 := by
  intro a b c h
  have h₁ : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 3 * a * b * c ≤ 12 := by
    have h₂ : a + b + c = 3 := by linarith
    have h₃ : 0 ≤ a := by linarith
    have h₄ : 0 ≤ b := by linarith
    have h₅ : 0 ≤ c := by linarith
    have h₆ : 0 ≤ a * b := by positivity
    have h₇ : 0 ≤ b * c := by positivity
    have h₈ : 0 ≤ c * a := by positivity
    have h₉ : 0 ≤ a * b * c := by positivity
    -- Use non-linear arithmetic to prove the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₃ h₄, mul_nonneg h₄ h₅, mul_nonneg h₅ h₃,
      mul_nonneg (sq_nonneg (a - b)) h₅, mul_nonneg (sq_nonneg (b - c)) h₃,
      mul_nonneg (sq_nonneg (c - a)) h₄, mul_nonneg (sq_nonneg (a - b)) h₄,
      mul_nonneg (sq_nonneg (b - c)) h₅, mul_nonneg (sq_nonneg (c - a)) h₃]
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_182 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3 → a / (4 - a) + b / (4 - b) + c / (4 - c) ≤ 1 := by
  intro a b c h
  have h_main : a / (4 - a) + b / (4 - b) + c / (4 - c) ≤ 1 := by
    have h₁ : 0 ≤ a := by linarith
    have h₂ : 0 ≤ b := by linarith
    have h₃ : 0 ≤ c := by linarith
    have h₄ : a ^ 2 + b ^ 2 + c ^ 2 = 3 := by linarith
    have h₅ : a ≤ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have h₆ : b ≤ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have h₇ : c ≤ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have h₈ : 4 - a > 0 := by nlinarith
    have h₉ : 4 - b > 0 := by nlinarith
    have h₁₀ : 4 - c > 0 := by nlinarith
    have h₁₁ : a / (4 - a) + b / (4 - b) + c / (4 - c) ≤ 1 := by
      -- Use the fact that each term is non-negative and the sum of squares is 3
      field_simp [h₈, h₉, h₁₀]
      rw [div_le_one (by positivity), ← sub_nonneg]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_nonneg h₁ (sub_nonneg.mpr h₅), mul_nonneg h₂ (sub_nonneg.mpr h₆),
        mul_nonneg h₃ (sub_nonneg.mpr h₇),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    exact h₁₁
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_567_189 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ ((a - b) * (b - c) * (c - a)) ^ 2 := by
  intro a b c h
  have h₁ : (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - c * a),
      sq_nonneg (a * b - b ^ 2), sq_nonneg (b * c - c ^ 2), sq_nonneg (c * a - a ^ 2),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), h.1, h.2.1, h.2.2,
      mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1,
      mul_pos (sq_pos_of_pos h.1) (sq_pos_of_pos h.2.1), mul_pos (sq_pos_of_pos h.2.1) (sq_pos_of_pos h.2.2),
      mul_pos (sq_pos_of_pos h.2.2) (sq_pos_of_pos h.1)]
  
  have h₂ : a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a := by
    have h₂₁ : a ^ 3 + a ^ 2 * b + b ^ 3 + b ^ 2 * c + c ^ 3 + c ^ 2 * a ≥ a * b ^ 2 + b * c ^ 2 + c * a ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1,
        mul_pos (sq_pos_of_pos h.1) (sq_pos_of_pos h.2.1),
        mul_pos (sq_pos_of_pos h.2.1) (sq_pos_of_pos h.2.2),
        mul_pos (sq_pos_of_pos h.2.2) (sq_pos_of_pos h.1)]
    linarith [h₂₁]
  
  have h₃ : (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ (a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a) ^ 2 := by
    have h₃₁ : a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a := by
      exact h₂
    have h₃₂ : a ^ 3 + b ^ 3 + c ^ 3 ≥ 0 := by
      linarith [pow_pos h.1 3, pow_pos h.2.1 3, pow_pos h.2.2 3]
    have h₃₃ : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
      linarith
    have h₃₄ : (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ (a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a) ^ 2 := by
      have h₃₅ : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
        linarith
      have h₃₆ : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a ≥ -(a ^ 3 + b ^ 3 + c ^ 3) := by
        -- Prove the lower bound using non-negativity and sum of squares
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1,
          mul_pos (sq_pos_of_pos h.1) (sq_pos_of_pos h.2.1),
          mul_pos (sq_pos_of_pos h.2.1) (sq_pos_of_pos h.2.2),
          mul_pos (sq_pos_of_pos h.2.2) (sq_pos_of_pos h.1)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1,
        mul_pos (sq_pos_of_pos h.1) (sq_pos_of_pos h.2.1),
        mul_pos (sq_pos_of_pos h.2.1) (sq_pos_of_pos h.2.2),
        mul_pos (sq_pos_of_pos h.2.2) (sq_pos_of_pos h.1)]
    exact h₃₄
  
  have h₄ : (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ (a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a) ^ 2 := by
    linarith
  
  have h₅ : ((a - b) * (b - c) * (c - a)) ^ 2 = (a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a) ^ 2 := by
    have h₅₁ : (a - b) * (b - c) * (c - a) = a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a := by
      ring_nf
      <;>
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1]
    rw [h₅₁]
    <;>
    ring_nf
    <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1]
  
  have h₆ : (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ ((a - b) * (b - c) * (c - a)) ^ 2 := by
    rw [h₅]
    <;> linarith
  
  linarith

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_211 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → Real.sqrt ((a + 2 * b) / (a + 2 * c)) + Real.sqrt ((b + 2 * c) / (b + 2 * a)) + Real.sqrt ((c + 2 * a) / (c + 2 * b)) ≥ 3 := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a + b + c := by linarith
  have h₅ : Real.sqrt ((a + 2 * b) / (a + 2 * c)) ≥ (a + 2 * b) / (a + b + c) := by
    have h₅₁ : 0 < a + 2 * b := by linarith
    have h₅₂ : 0 < a + 2 * c := by linarith
    have h₅₃ : 0 < a + b + c := by linarith
    have h₅₄ : 0 < (a + 2 * b) / (a + 2 * c) := by positivity
    have h₅₅ : ((a + 2 * b) / (a + b + c)) ^ 2 ≤ (a + 2 * b) / (a + 2 * c) := by
      have h₅₅₁ : 0 < a + 2 * b := by linarith
      have h₅₅₂ : 0 < a + b + c := by linarith
      have h₅₅₃ : 0 < a + 2 * c := by linarith
      field_simp [h₅₅₁.ne', h₅₅₂.ne', h₅₅₃.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (b - c)]
    have h₅₆ : Real.sqrt ((a + 2 * b) / (a + 2 * c)) ≥ (a + 2 * b) / (a + b + c) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h₅₆
  
  have h₆ : Real.sqrt ((b + 2 * c) / (b + 2 * a)) ≥ (b + 2 * c) / (a + b + c) := by
    have h₆₁ : 0 < b + 2 * c := by linarith
    have h₆₂ : 0 < b + 2 * a := by linarith
    have h₆₃ : 0 < a + b + c := by linarith
    have h₆₄ : 0 < (b + 2 * c) / (b + 2 * a) := by positivity
    have h₆₅ : ((b + 2 * c) / (a + b + c)) ^ 2 ≤ (b + 2 * c) / (b + 2 * a) := by
      have h₆₅₁ : 0 < b + 2 * c := by linarith
      have h₆₅₂ : 0 < a + b + c := by linarith
      have h₆₅₃ : 0 < b + 2 * a := by linarith
      field_simp [h₆₅₁.ne', h₆₅₂.ne', h₆₅₃.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (c - a)]
    have h₆₆ : Real.sqrt ((b + 2 * c) / (b + 2 * a)) ≥ (b + 2 * c) / (a + b + c) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h₆₆
  
  have h₇ : Real.sqrt ((c + 2 * a) / (c + 2 * b)) ≥ (c + 2 * a) / (a + b + c) := by
    have h₇₁ : 0 < c + 2 * a := by linarith
    have h₇₂ : 0 < c + 2 * b := by linarith
    have h₇₃ : 0 < a + b + c := by linarith
    have h₇₄ : 0 < (c + 2 * a) / (c + 2 * b) := by positivity
    have h₇₅ : ((c + 2 * a) / (a + b + c)) ^ 2 ≤ (c + 2 * a) / (c + 2 * b) := by
      have h₇₅₁ : 0 < c + 2 * a := by linarith
      have h₇₅₂ : 0 < a + b + c := by linarith
      have h₇₅₃ : 0 < c + 2 * b := by linarith
      field_simp [h₇₅₁.ne', h₇₅₂.ne', h₇₅₃.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a - b)]
    have h₇₆ : Real.sqrt ((c + 2 * a) / (c + 2 * b)) ≥ (c + 2 * a) / (a + b + c) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h₇₆
  
  have h₈ : Real.sqrt ((a + 2 * b) / (a + 2 * c)) + Real.sqrt ((b + 2 * c) / (b + 2 * a)) + Real.sqrt ((c + 2 * a) / (c + 2 * b)) ≥ 3 := by
    have h₈₁ : Real.sqrt ((a + 2 * b) / (a + 2 * c)) + Real.sqrt ((b + 2 * c) / (b + 2 * a)) + Real.sqrt ((c + 2 * a) / (c + 2 * b)) ≥ (a + 2 * b) / (a + b + c) + (b + 2 * c) / (a + b + c) + (c + 2 * a) / (a + b + c) := by
      linarith
    have h₈₂ : (a + 2 * b) / (a + b + c) + (b + 2 * c) / (a + b + c) + (c + 2 * a) / (a + b + c) = 3 := by
      have h₈₂₁ : (a + 2 * b) / (a + b + c) + (b + 2 * c) / (a + b + c) + (c + 2 * a) / (a + b + c) = ((a + 2 * b) + (b + 2 * c) + (c + 2 * a)) / (a + b + c) := by
        field_simp [add_assoc]
        <;> ring_nf
        <;> field_simp [h₄.ne']
        <;> ring_nf
      rw [h₈₂₁]
      have h₈₂₂ : (a + 2 * b) + (b + 2 * c) + (c + 2 * a) = 3 * (a + b + c) := by ring
      rw [h₈₂₂]
      have h₈₂₃ : (3 * (a + b + c)) / (a + b + c) = 3 := by
        field_simp [h₄.ne']
      rw [h₈₂₃]
    linarith
  
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_220 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 3 / (a ^ 2 + b ^ 2) + b ^ 3 / (b ^ 2 + c ^ 2) + c ^ 3 / (c ^ 2 + a ^ 2) ≥ (b + c) / 2 + c * a ^ 2 / (c ^ 2 + a ^ 2) := by
  intro a b c h
  have h_main : a ^ 3 / (a ^ 2 + b ^ 2) ≥ (2 * a - b) / 2 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < a ^ 2 + b ^ 2 := by positivity
    -- Use the fact that the denominator is positive to simplify the inequality
    have h₄ : 0 < a ^ 2 + b ^ 2 := by positivity
    -- Prove the inequality by cross-multiplying and simplifying
    field_simp [h₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to verify the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - b / 2), sq_nonneg (a + b / 2), mul_nonneg h₁.le h₂.le, mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (a - b)), mul_nonneg h₁.le (sq_nonneg (a + b / 2)), mul_nonneg h₂.le (sq_nonneg (a + b / 2))]
  
  have h_main₂ : b ^ 3 / (b ^ 2 + c ^ 2) ≥ (2 * b - c) / 2 := by
    have h₁ : 0 < b := by linarith
    have h₂ : 0 < c := by linarith
    have h₃ : 0 < b ^ 2 + c ^ 2 := by positivity
    have h₄ : 0 < b ^ 2 + c ^ 2 := by positivity
    -- Use the fact that the denominator is positive to simplify the inequality
    have h₅ : 0 < b ^ 2 + c ^ 2 := by positivity
    -- Prove the inequality by cross-multiplying and simplifying
    field_simp [h₅.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to verify the inequality
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - c / 2), sq_nonneg (b + c / 2), mul_nonneg h₁.le h₂.le, mul_nonneg h₁.le (sq_nonneg (b - c)), mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₁.le (sq_nonneg (b + c / 2)), mul_nonneg h₂.le (sq_nonneg (b + c / 2))]
  
  have h_main₃ : c ^ 3 / (c ^ 2 + a ^ 2) ≥ (2 * c - a) / 2 := by
    have h₁ : 0 < c := by linarith
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < c ^ 2 + a ^ 2 := by positivity
    -- Use the fact that the denominator is positive to simplify the inequality
    have h₄ : 0 < c ^ 2 + a ^ 2 := by positivity
    -- Prove the inequality by cross-multiplying and simplifying
    field_simp [h₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to verify the inequality
    nlinarith [sq_nonneg (c - a), sq_nonneg (c - a / 2), sq_nonneg (c + a / 2), mul_nonneg h₁.le h₂.le, mul_nonneg h₁.le (sq_nonneg (c - a)), mul_nonneg h₂.le (sq_nonneg (c - a)), mul_nonneg h₁.le (sq_nonneg (c + a / 2)), mul_nonneg h₂.le (sq_nonneg (c + a / 2))]
  
  have h_sum : a ^ 3 / (a ^ 2 + b ^ 2) + b ^ 3 / (b ^ 2 + c ^ 2) + c ^ 3 / (c ^ 2 + a ^ 2) ≥ (a + b + c) / 2 := by
    have h₁ : a ^ 3 / (a ^ 2 + b ^ 2) + b ^ 3 / (b ^ 2 + c ^ 2) + c ^ 3 / (c ^ 2 + a ^ 2) ≥ (2 * a - b) / 2 + (2 * b - c) / 2 + (2 * c - a) / 2 := by
      linarith [h_main, h_main₂, h_main₃]
    have h₂ : (2 * a - b) / 2 + (2 * b - c) / 2 + (2 * c - a) / 2 = (a + b + c) / 2 := by
      ring
    linarith
  
  have h_final : (a + b + c) / 2 ≥ (b + c) / 2 + c * a ^ 2 / (c ^ 2 + a ^ 2) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < c := by linarith
    have h₃ : 0 < c ^ 2 + a ^ 2 := by positivity
    have h₄ : 0 < c ^ 2 + a ^ 2 := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < a ^ 2 := by positivity
    have h₇ : 0 < c ^ 2 := by positivity
    -- Use the fact that the denominator is positive to simplify the inequality
    have h₈ : (a + b + c) / 2 ≥ (b + c) / 2 + c * a ^ 2 / (c ^ 2 + a ^ 2) := by
      -- Prove the inequality by cross-multiplying and simplifying
      field_simp
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - b), sq_nonneg (b - c), mul_nonneg h₁.le h₂.le,
        mul_nonneg h₁.le h₆.le, mul_nonneg h₂.le h₆.le, mul_nonneg h₁.le (sq_nonneg (a - c)),
        mul_nonneg h₂.le (sq_nonneg (a - c)), mul_nonneg h₁.le (sq_nonneg (b - c)),
        mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₁.le (sq_nonneg (c - a)),
        mul_nonneg h₂.le (sq_nonneg (c - a))]
    linarith
  
  have h_final_main : a ^ 3 / (a ^ 2 + b ^ 2) + b ^ 3 / (b ^ 2 + c ^ 2) + c ^ 3 / (c ^ 2 + a ^ 2) ≥ (b + c) / 2 + c * a ^ 2 / (c ^ 2 + a ^ 2) := by
    linarith [h_sum, h_final]
  
  linarith [h_final_main]

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_227 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 6 → (11 + a ^ 2) * (11 + b ^ 2) * (11 + c ^ 2) + 120 * a * b * c ≥ 4320 := by
  intro a b c h
  have h₁ : 0 ≤ a := by linarith
  have h₂ : 0 ≤ b := by linarith
  have h₃ : 0 ≤ c := by linarith
  have h₄ : a + b + c = 6 := by linarith
  have h₅ : a * b * c ≥ 0 := by
    have h₅₁ : 0 ≤ a * b := by positivity
    have h₅₂ : 0 ≤ a * b * c := by positivity
    linarith
  have h₆ : (a * b + b * c + c * a) ≤ 12 := by
    have h₆₁ : (a + b + c) ^ 2 = 36 := by
      rw [h₄]
      <;> norm_num
    have h₆₂ : 0 ≤ a * b := by positivity
    have h₆₃ : 0 ≤ b * c := by positivity
    have h₆₄ : 0 ≤ c * a := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h₇ : 11 * (a * b + b * c + c * a) ^ 2 - 242 * (a * b + b * c + c * a) + 1367 + (a * b * c) ^ 2 - 12 * (a * b * c) ≥ 0 := by
    have h₇₁ : a * b + b * c + c * a ≤ 12 := h₆
    have h₇₂ : 0 ≤ a * b + b * c + c * a := by
      nlinarith [h₁, h₂, h₃]
    have h₇₃ : 0 ≤ a * b * c := by positivity
    have h₇₄ : (a * b + b * c + c * a) ≥ 0 := by positivity
    have h₇₅ : (a * b * c) ^ 2 - 12 * (a * b * c) ≥ -36 := by
      nlinarith [sq_nonneg (a * b * c - 6)]
    have h₇₆ : 11 * (a * b + b * c + c * a) ^ 2 - 242 * (a * b + b * c + c * a) + 1367 ≥ 36 := by
      nlinarith [sq_nonneg (a * b + b * c + c * a - 11)]
    nlinarith [sq_nonneg (a * b + b * c + c * a - 11)]
  have h₈ : (11 + a ^ 2) * (11 + b ^ 2) * (11 + c ^ 2) + 120 * a * b * c ≥ 4320 := by
    have h₈₁ : (11 + a ^ 2) * (11 + b ^ 2) * (11 + c ^ 2) + 120 * a * b * c = 5687 - 242 * (a * b + b * c + c * a) + 11 * (a * b + b * c + c * a) ^ 2 - 12 * (a * b * c) + (a * b * c) ^ 2 := by
      have h₈₂ : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by
        ring
      have h₈₃ : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 = (a * b + b * c + c * a) ^ 2 - 2 * (a * b * c) * (a + b + c) := by
        ring
      have h₈₄ : (11 + a ^ 2) * (11 + b ^ 2) * (11 + c ^ 2) = 1331 + 121 * (a ^ 2 + b ^ 2 + c ^ 2) + 11 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + (a * b * c) ^ 2 := by
        ring
      rw [h₈₄, h₈₂, h₈₃, h₄]
      ring
      <;>
      nlinarith
    rw [h₈₁]
    nlinarith [h₇]
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_231 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ≥ (a * b + b * c + c * a) ^ 3 := by
  have h_main : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ≥ (a * b + b * c + c * a) ^ 3 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 ≤ a * b := by positivity
    have h₂ : 0 ≤ b * c := by positivity
    have h₃ : 0 ≤ c * a := by positivity
    have h₄ : 0 ≤ a * b * c := by positivity
    have h₅ : 0 ≤ a * b * c * a := by positivity
    have h₆ : 0 ≤ a * b * c * b := by positivity
    have h₇ : 0 ≤ a * b * c * c := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁ (sq_nonneg (a - b)), mul_nonneg h₂ (sq_nonneg (b - c)), mul_nonneg h₃ (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a)),
      mul_nonneg (sq_nonneg (b * c - c * a)) (sq_nonneg (c * a - a * b)),
      mul_nonneg (sq_nonneg (c * a - a * b)) (sq_nonneg (a * b - b * c))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_233 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 9 * (a * b + a * c + b * c) := by
  intro a b c h
  have h_main : (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 9 * (a * b + a * c + b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      mul_nonneg h.1.le h.2.1.le, mul_nonneg h.2.1.le h.2.2.le, mul_nonneg h.2.2.le h.1.le,
      sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * b * c - 1),
      sq_nonneg (a * b + b * c + c * a - a * b * c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_234 : ∀ (x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y * z = 1 → x ^ 2 / (1 + y) + y ^ 2 / (1 + z) + z ^ 2 / (1 + x) ≥ 3 / 2 := by
  intro x y z h
  have h_main : x ^ 2 / (1 + y) + y ^ 2 / (1 + z) + z ^ 2 / (1 + x) ≥ 3 / 2 := by
    rcases h with ⟨hx, hy, hz, h⟩
    have h₁ : 0 < x * y := by positivity
    have h₂ : 0 < x * z := by positivity
    have h₃ : 0 < y * z := by positivity
    field_simp [add_comm]
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_le_mul_of_nonneg_left (sq_nonneg (x - 1)) hy.le,
      mul_le_mul_of_nonneg_left (sq_nonneg (y - 1)) hz.le,
      mul_le_mul_of_nonneg_left (sq_nonneg (z - 1)) hx.le,
      mul_le_mul_of_nonneg_right (sq_nonneg (x - 1)) hz.le,
      mul_le_mul_of_nonneg_right (sq_nonneg (y - 1)) hx.le,
      mul_le_mul_of_nonneg_right (sq_nonneg (z - 1)) hy.le]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_244 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / (a * (b + 1)) + 1 / (b * (c + 1)) + 1 / (c * (a + 1)) ≥ 3 / (1 + a * b * c) := by
  intro a b c h
  have h_main : 1 / (a * (b + 1)) + 1 / (b * (c + 1)) + 1 / (c * (a + 1)) ≥ 3 / (1 + a * b * c) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < a * c := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b * c * a := by positivity
    have h₉ : 0 < a * b * c * b := by positivity
    have h₁₀ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
      sq_nonneg (a * b * c - a), sq_nonneg (a * b * c - b), sq_nonneg (a * b * c - c),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₁.le) (sub_nonneg.mpr h₂.le),
      mul_nonneg (sub_nonneg.mpr h₂.le) (sub_nonneg.mpr h₃.le),
      mul_nonneg (sub_nonneg.mpr h₁.le) (sub_nonneg.mpr h₃.le)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_257 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 2 / (b + c) + b ^ 2 / (a + c) + c ^ 2 / (a + b) ≥ 3 / 2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c h
  have h_main : a ^ 2 / (b + c) + b ^ 2 / (a + c) + c ^ 2 / (a + b) ≥ 3 / 2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a^2 * b - b^2 * a), sq_nonneg (a^2 * c - c^2 * a), sq_nonneg (b^2 * c - c^2 * b),
      sq_nonneg (a^2 * b - a^2 * c), sq_nonneg (b^2 * a - b^2 * c), sq_nonneg (c^2 * a - c^2 * b),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)),
      mul_nonneg h₃.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
      mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
      mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_259 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a * (a + c) / (b * (b + c)) + b * (b + a) / (c * (c + a)) + c * (c + b) / (a * (a + b)) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) := by
  intro a b c h
  have h_main : a * (a + c) / (b * (b + c)) + b * (b + a) / (c * (c + a)) + c * (c + b) / (a * (a + b)) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b * c * a := by positivity
    have h₉ : 0 < a * b * c * b := by positivity
    have h₁₀ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
      sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c),
      sq_nonneg (a * b * c * (a - b)), sq_nonneg (a * b * c * (b - c)), sq_nonneg (a * b * c * (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
      mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
      mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_262 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) + (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) + (c ^ 2 - c * a + a ^ 2) * (a ^ 2 - a * b + b ^ 2) ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
  intro a b c h
  have h_main : (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) + (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) + (c ^ 2 - c * a + a ^ 2) * (a ^ 2 - a * b + b ^ 2) ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1,
      mul_pos (sq_pos_of_pos h.1) (sq_pos_of_pos h.2.1), mul_pos (sq_pos_of_pos h.2.1) (sq_pos_of_pos h.2.2),
      mul_pos (sq_pos_of_pos h.2.2) (sq_pos_of_pos h.1),
      mul_pos (mul_pos h.1 h.2.1) (mul_pos h.2.1 h.2.2), mul_pos (mul_pos h.2.1 h.2.2) (mul_pos h.2.2 h.1),
      mul_pos (mul_pos h.2.2 h.1) (mul_pos h.1 h.2.1),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
      sq_nonneg (a * b - a * c), sq_nonneg (b * c - a * b), sq_nonneg (c * a - b * c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_264 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 12 * (a + b) * (b + c) * (c + a) / (a + b + c) ^ 3 ≥ 41 / 9 := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b + b * c + c * a := by
    nlinarith [mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
  have h₅ : 0 < a + b + c := by linarith
  have h₆ : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + 12 * (a + b) * (b + c) * (c + a) / (a + b + c) ^ 3 ≥ 41 / 9 := by
    have h₇ : 0 < a * b := by positivity
    have h₈ : 0 < b * c := by positivity
    have h₉ : 0 < c * a := by positivity
    have h₁₀ : 0 < a * b * c := by positivity
    have h₁₁ : 0 < a * b * c * a := by positivity
    have h₁₂ : 0 < a * b * c * b := by positivity
    have h₁₃ : 0 < a * b * c * c := by positivity
    field_simp [h₄.ne', h₅.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
      mul_nonneg (sq_nonneg (a - b)) h₃.le, mul_nonneg (sq_nonneg (b - c)) h₁.le,
      mul_nonneg (sq_nonneg (c - a)) h₂.le, mul_nonneg (sq_nonneg (a - b)) h₂.le,
      mul_nonneg (sq_nonneg (b - c)) h₃.le, mul_nonneg (sq_nonneg (c - a)) h₁.le,
      mul_nonneg (sq_nonneg (a + b + c)) h₁.le, mul_nonneg (sq_nonneg (a + b + c)) h₂.le,
      mul_nonneg (sq_nonneg (a + b + c)) h₃.le, mul_nonneg (sq_nonneg (a - b + c)) h₁.le,
      mul_nonneg (sq_nonneg (a + b - c)) h₂.le, mul_nonneg (sq_nonneg (a - b - c)) h₃.le]
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_265 : ∀ (a b c : ℝ), a * b + a * c + b * c ≥ 0 → (a + b + c) ^ 6 ≥ 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + a * c + b * c) ^ 2 := by
  intro a b c h
  have h₁ : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by
    ring_nf
    <;>
    linarith
  
  have h₂ : (a + b + c) ^ 6 ≥ 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + a * c + b * c) ^ 2 := by
    have h₃ : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
      linarith
    have h₄ : (a + b + c) ^ 6 = ((a + b + c) ^ 2) ^ 3 := by ring
    rw [h₄]
    have h₅ : (a + b + c) ^ 2 ≥ 0 := by nlinarith
    have h₆ : (a * b + a * c + b * c) ≥ 0 := h
    have h₇ : ((a + b + c) ^ 2) ^ 3 ≥ 27 * ((a + b + c) ^ 2 - 2 * (a * b + a * c + b * c)) * (a * b + a * c + b * c) ^ 2 := by
      -- Use the AM-GM inequality to prove the required inequality
      have h₇₁ : 0 ≤ (a * b + a * c + b * c) := h₆
      have h₇₂ : 0 ≤ (a + b + c) ^ 2 := by nlinarith
      have h₇₃ : 0 ≤ ((a + b + c) ^ 2) ^ 3 := by positivity
      -- Use non-linear arithmetic to prove the inequality
      nlinarith [sq_nonneg ((a + b + c) ^ 2 - 3 * (a * b + a * c + b * c)), sq_nonneg ((a + b + c) ^ 2 + 6 * (a * b + a * c + b * c)),
        sq_nonneg ((a + b + c) ^ 2 - 6 * (a * b + a * c + b * c)), mul_nonneg h₇₁ (sq_nonneg ((a + b + c) ^ 2)),
        mul_nonneg h₇₁ (sq_nonneg ((a + b + c) ^ 2 - 6 * (a * b + a * c + b * c))),
        mul_nonneg h₇₁ (sq_nonneg ((a + b + c) ^ 2 - 3 * (a * b + a * c + b * c)))]
    have h₈ : 27 * ((a + b + c) ^ 2 - 2 * (a * b + a * c + b * c)) * (a * b + a * c + b * c) ^ 2 = 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + a * c + b * c) ^ 2 := by
      rw [h₃]
      <;> ring
    linarith
  
  exact h₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_ineq_27817  : ∀ (x y z : ℝ), 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z → (x + y + z) ^ 3 ≥ 3 * (x * y + y * z + z * x) * Real.sqrt (3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by
  intro x y z h
  have h₁ : 0 ≤ x * y := by nlinarith
  have h₂ : 0 ≤ y * z := by nlinarith
  have h₃ : 0 ≤ z * x := by nlinarith
  have h₄ : 0 ≤ x * y * z := by nlinarith
  have h₅ : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by nlinarith
  have h₆ : 0 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by nlinarith
  have h₇ : 0 ≤ Real.sqrt (3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by positivity
  -- Use the fact that the square of the square root is the original expression
  have h₈ : (Real.sqrt (3 * (x ^ 2 + y ^ 2 + z ^ 2))) ^ 2 = 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    rw [Real.sq_sqrt] <;> nlinarith
  -- Use nlinarith to prove the inequality
  nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    Real.sq_sqrt (show 0 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) by nlinarith),
    sq_nonneg (x + y + z - Real.sqrt (3 * (x ^ 2 + y ^ 2 + z ^ 2))),
    sq_nonneg (x * y + y * z + z * x - Real.sqrt (3 * (x ^ 2 + y ^ 2 + z ^ 2))),
    sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_269 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / 2 + (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ≥ a / (b + c) + b / (c + a) + c / (a + b) := by
  intro a b c h
  have h_main : 1 / 2 + (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) ≥ a / (b + c) + b / (c + a) + c / (a + b) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 0 < a * b * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)),
      mul_nonneg h₃.le (sq_nonneg (c - a)), mul_nonneg h₁.le (sq_nonneg (a - c)),
      mul_nonneg h₂.le (sq_nonneg (b - a)), mul_nonneg h₃.le (sq_nonneg (c - b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
      mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_272 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 2 / ((a + b) * (a + c)) + b ^ 2 / ((b + c) * (b + a)) + c ^ 2 / ((c + a) * (c + b)) ≥ 3 / 4 := by
  have h_main : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 2 / ((a + b) * (a + c)) + b ^ 2 / ((b + c) * (b + a)) + c ^ 2 / ((c + a) * (c + b)) ≥ 3 / 4 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    field_simp [add_comm]
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - c * a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_278 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 1 → 2 * a * b * c * (a + b + c) ≤ 2 * (a + b + c) ^ 2 + 1 := by
  intro a b c h
  have h_main : 2 * a * b * c * (a + b + c) ≤ 2 * (a + b + c) ^ 2 + 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2.1, mul_pos h.2.2.1 h.1,
      sq_nonneg (a + b + c - 3 * a * b * c),
      sq_nonneg (a * b + b * c + c * a - 1 / 3),
      sq_nonneg (a * b * c - 1 / (3 * Real.sqrt 3))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem p567_288 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ (a + b + c) / (2 * (a * b + b * c + c * a)) + 3 / (a + b + c) := by
  have h_main : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ (a + b + c) / (2 * (a * b + b * c + c * a)) + 3 / (a + b + c) := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    have h₄ : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
    have h₅ : 0 < a * b * c * a := by positivity
    have h₆ : 0 < a * b * c * b := by positivity
    have h₇ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - c * a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_567_293 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 → 1 / (b * c + a + 1 / a) + 1 / (a * c + b + 1 / b) + 1 / (a * b + c + 1 / c) ≤ 27 / 3 := by
  intro a b c h
  have h₁ : a + 1 / a ≥ 2 := by
    have h₁₀ : 0 < a := by linarith
    have h₁₁ : a + 1 / a - 2 = (1 - a)^2 / a := by
      field_simp [h₁₀.ne']
      <;> ring
      <;> field_simp [h₁₀.ne']
      <;> ring
    have h₁₂ : (1 - a)^2 / a ≥ 0 := by
      apply div_nonneg
      · nlinarith
      · linarith
    linarith
  
  have h₂ : b + 1 / b ≥ 2 := by
    have h₂₀ : 0 < b := by linarith
    have h₂₁ : b + 1 / b - 2 = (1 - b)^2 / b := by
      field_simp [h₂₀.ne']
      <;> ring
      <;> field_simp [h₂₀.ne']
      <;> ring
    have h₂₂ : (1 - b)^2 / b ≥ 0 := by
      apply div_nonneg
      · nlinarith
      · linarith
    linarith
  
  have h₃ : c + 1 / c ≥ 2 := by
    have h₃₀ : 0 < c := by linarith
    have h₃₁ : c + 1 / c - 2 = (1 - c)^2 / c := by
      field_simp [h₃₀.ne']
      <;> ring
      <;> field_simp [h₃₀.ne']
      <;> ring
    have h₃₂ : (1 - c)^2 / c ≥ 0 := by
      apply div_nonneg
      · nlinarith
      · linarith
    linarith
  
  have h₄ : b * c + a + 1 / a ≥ 2 := by
    have h₄₁ : b * c + a + 1 / a ≥ a + 1 / a := by
      -- Since b * c ≥ 0, we can ignore it in the inequality.
      have h₄₂ : b * c ≥ 0 := by
        nlinarith
      nlinarith
    -- Using the given inequality h₁: a + 1 / a ≥ 2 and h₄₁, we conclude the proof.
    nlinarith
  
  have h₅ : a * c + b + 1 / b ≥ 2 := by
    have h₅₁ : a * c + b + 1 / b ≥ b + 1 / b := by
      have h₅₂ : a * c ≥ 0 := by nlinarith
      nlinarith
    nlinarith
  
  have h₆ : a * b + c + 1 / c ≥ 2 := by
    have h₆₁ : a * b + c + 1 / c ≥ c + 1 / c := by
      have h₆₂ : a * b ≥ 0 := by nlinarith
      nlinarith
    nlinarith
  
  have h₇ : 1 / (b * c + a + 1 / a) ≤ 1 / 2 := by
    have h₇₁ : 0 < b * c + a + 1 / a := by
      have h₇₂ : 0 < a := by linarith
      have h₇₃ : 0 < b * c := by nlinarith
      have h₇₄ : 0 < 1 / a := by positivity
      positivity
    -- Use the fact that the denominator is at least 2 to bound the reciprocal
    have h₇₂ : b * c + a + 1 / a ≥ 2 := by linarith
    have h₇₃ : 1 / (b * c + a + 1 / a) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₇₃
  
  have h₈ : 1 / (a * c + b + 1 / b) ≤ 1 / 2 := by
    have h₈₁ : 0 < a * c + b + 1 / b := by
      have h₈₂ : 0 < b := by linarith
      have h₈₃ : 0 < a * c := by nlinarith
      have h₈₄ : 0 < 1 / b := by positivity
      positivity
    -- Use the fact that the denominator is at least 2 to bound the reciprocal
    have h₈₂ : a * c + b + 1 / b ≥ 2 := by linarith
    have h₈₃ : 1 / (a * c + b + 1 / b) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₈₃
  
  have h₉ : 1 / (a * b + c + 1 / c) ≤ 1 / 2 := by
    have h₉₁ : 0 < a * b + c + 1 / c := by
      have h₉₂ : 0 < c := by linarith
      have h₉₃ : 0 < a * b := by nlinarith
      have h₉₄ : 0 < 1 / c := by positivity
      positivity
    -- Use the fact that the denominator is at least 2 to bound the reciprocal
    have h₉₂ : a * b + c + 1 / c ≥ 2 := by linarith
    have h₉₃ : 1 / (a * b + c + 1 / c) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₉₃
  
  have h₁₀ : 1 / (b * c + a + 1 / a) + 1 / (a * c + b + 1 / b) + 1 / (a * b + c + 1 / c) ≤ 3 / 2 := by
    linarith
  
  have h₁₁ : (3 : ℝ) / 2 ≤ 27 / 3 := by norm_num
  
  have h₁₂ : 1 / (b * c + a + 1 / a) + 1 / (a * c + b + 1 / b) + 1 / (a * b + c + 1 / c) ≤ 27 / 3 := by
    linarith
  
  exact h₁₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_567_298 : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a + b + c + d = 4 → 1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ 1 / 3 := by
  have h_main : ∀ (x : ℝ), 0 < x → x ≤ 4 → 1 / (11 + x ^ 2) ≤ 7 / 72 - x / 72 := by
    intro x hx hx'
    have h₁ : 0 < 11 + x ^ 2 := by nlinarith
    have h₂ : (x - 1) ^ 2 * (x - 5) ≤ 0 := by
      have h₃ : x ≤ 4 := hx'
      have h₄ : 0 < x := hx
      have h₅ : (x - 1) ^ 2 ≥ 0 := by nlinarith
      have h₆ : x - 5 ≤ 0 := by nlinarith
      nlinarith
    have h₃ : 1 / (11 + x ^ 2) ≤ 7 / 72 - x / 72 := by
      have h₄ : (7 - x) * (11 + x ^ 2) ≥ 72 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5)]
      have h₅ : 1 / (11 + x ^ 2) ≤ 7 / 72 - x / 72 := by
        have h₆ : 0 < 11 + x ^ 2 := by nlinarith
        field_simp at h₄ ⊢
        rw [div_le_div_iff] <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5)]
      exact h₅
    exact h₃
  
  have h_final : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a + b + c + d = 4 → 1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ 1 / 3 := by
    intro a b c d h
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < d := by linarith
    have h₅ : a + b + c + d = 4 := by linarith
    have h₆ : a ≤ 4 := by
      nlinarith [h₁, h₂, h₃, h₄, h₅]
    have h₇ : b ≤ 4 := by
      nlinarith [h₁, h₂, h₃, h₄, h₅]
    have h₈ : c ≤ 4 := by
      nlinarith [h₁, h₂, h₃, h₄, h₅]
    have h₉ : d ≤ 4 := by
      nlinarith [h₁, h₂, h₃, h₄, h₅]
    have h₁₀ : 1 / (11 + a ^ 2) ≤ 7 / 72 - a / 72 := h_main a h₁ h₆
    have h₁₁ : 1 / (11 + b ^ 2) ≤ 7 / 72 - b / 72 := h_main b h₂ h₇
    have h₁₂ : 1 / (11 + c ^ 2) ≤ 7 / 72 - c / 72 := h_main c h₃ h₈
    have h₁₃ : 1 / (11 + d ^ 2) ≤ 7 / 72 - d / 72 := h_main d h₄ h₉
    have h₁₄ : 1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ (7 / 72 - a / 72) + (7 / 72 - b / 72) + (7 / 72 - c / 72) + (7 / 72 - d / 72) := by
      linarith
    have h₁₅ : (7 / 72 - a / 72) + (7 / 72 - b / 72) + (7 / 72 - c / 72) + (7 / 72 - d / 72) = 28 / 72 - (a + b + c + d) / 72 := by ring
    have h₁₆ : 28 / 72 - (a + b + c + d) / 72 = 28 / 72 - 4 / 72 := by rw [h₅] <;> ring
    have h₁₇ : 28 / 72 - 4 / 72 = 24 / 72 := by ring
    have h₁₈ : 24 / 72 = 1 / 3 := by norm_num
    have h₁₉ : (7 / 72 - a / 72) + (7 / 72 - b / 72) + (7 / 72 - c / 72) + (7 / 72 - d / 72) = 1 / 3 := by
      linarith
    have h₂₀ : 1 / (11 + a ^ 2) + 1 / (11 + b ^ 2) + 1 / (11 + c ^ 2) + 1 / (11 + d ^ 2) ≤ 1 / 3 := by
      linarith
    exact h₂₀
  
  exact h_final
