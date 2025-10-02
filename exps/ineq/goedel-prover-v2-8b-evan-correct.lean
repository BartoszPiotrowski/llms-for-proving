
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_1_2_left : ∀ (a b c : ℝ), a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  have h_main : ∀ (a b c : ℝ), a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    intro a b c
    have h1 : 0 ≤ (a - b) ^ 2 := by
      -- Prove that the square of any real number is non-negative.
      nlinarith [sq_nonneg (a - b)]
    have h2 : 0 ≤ (b - c) ^ 2 := by
      -- Prove that the square of any real number is non-negative.
      nlinarith [sq_nonneg (b - c)]
    have h3 : 0 ≤ (c - a) ^ 2 := by
      -- Prove that the square of any real number is non-negative.
      nlinarith [sq_nonneg (c - a)]
    -- Combine the inequalities to prove the desired result.
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_1_2_right : ∀ (a b c : ℝ), a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
  intro a b c
  have h_main : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - c * a), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a * b + b * c + c * a - a ^ 2 - b ^ 2 - c ^ 2)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_exercise_1_3 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
  intro a b c h
  have h_main : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
    cases' le_total a b with h₁ h₁ <;> cases' le_total b c with h₂ h₂ <;> cases' le_total c a with h₃ h₃ <;>
      simp_all [mul_assoc] <;>
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_nonneg h.1 (sq_nonneg (a - b)), mul_nonneg h.2.1 (sq_nonneg (b - c)),
        mul_nonneg h.2.2 (sq_nonneg (c - a)), mul_nonneg h.1 (sq_nonneg (a - c)),
        mul_nonneg h.2.1 (sq_nonneg (b - a)), mul_nonneg h.2.2 (sq_nonneg (c - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_exercise_1_4_left : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
  have h_main : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 3 * a ^ 5 + b ^ 5 + c ^ 5 ≥ 5 * a ^ 3 * b * c := by
      -- Prove that 3a^5 + b^5 + c^5 ≥ 5a^3bc using AM-GM inequality
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
        sq_nonneg (a ^ 2 - 2 * a * b + b ^ 2), sq_nonneg (a ^ 2 - 2 * a * c + c ^ 2), sq_nonneg (b ^ 2 - 2 * b * c + c ^ 2),
        mul_nonneg ha (sq_nonneg (a - b)), mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hb (sq_nonneg (b - c)),
        mul_nonneg hb (sq_nonneg (b - a)), mul_nonneg hc (sq_nonneg (c - a)), mul_nonneg hc (sq_nonneg (c - b))]
    have h₂ : 3 * b ^ 5 + c ^ 5 + a ^ 5 ≥ 5 * b ^ 3 * c * a := by
      -- Prove that 3b^5 + c^5 + a^5 ≥ 5b^3ca using AM-GM inequality
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - a ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
        sq_nonneg (b ^ 2 - 2 * b * c + c ^ 2), sq_nonneg (b ^ 2 - 2 * b * a + a ^ 2), sq_nonneg (c ^ 2 - 2 * c * a + a ^ 2),
        mul_nonneg hb (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (b - a)), mul_nonneg hc (sq_nonneg (c - a)),
        mul_nonneg hc (sq_nonneg (c - b)), mul_nonneg ha (sq_nonneg (a - b)), mul_nonneg ha (sq_nonneg (a - c))]
    have h₃ : 3 * c ^ 5 + a ^ 5 + b ^ 5 ≥ 5 * c ^ 3 * a * b := by
      -- Prove that 3c^5 + a^5 + b^5 ≥ 5c^3ab using AM-GM inequality
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - b ^ 2),
        sq_nonneg (c ^ 2 - 2 * c * a + a ^ 2), sq_nonneg (c ^ 2 - 2 * c * b + b ^ 2), sq_nonneg (a ^ 2 - 2 * a * b + b ^ 2),
        mul_nonneg hc (sq_nonneg (c - a)), mul_nonneg hc (sq_nonneg (c - b)), mul_nonneg ha (sq_nonneg (a - b)),
        mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hb (sq_nonneg (b - a)), mul_nonneg hb (sq_nonneg (b - c))]
    -- Combine the inequalities to get the final result
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      mul_nonneg ha (sq_nonneg (a - b)), mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hb (sq_nonneg (b - c)),
      mul_nonneg hb (sq_nonneg (b - a)), mul_nonneg hc (sq_nonneg (c - a)), mul_nonneg hc (sq_nonneg (c - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_exercise_1_4_right : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a * b * c * (a * b + b * c + c * a) := by
  have h_main : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a * b * c * (a * b + b * c + c * a) := by
    intro a b c ⟨ha, hb, hc⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha,
      sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
      sq_nonneg (a^2 - a * b), sq_nonneg (b^2 - b * c), sq_nonneg (c^2 - c * a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg a) (sq_nonneg b), mul_nonneg (sq_nonneg b) (sq_nonneg c),
      mul_nonneg (sq_nonneg c) (sq_nonneg a), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg a),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg b), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_1_7 : ∀ (a b c : ℝ), a * b * c = 1 → a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c := by
  have h_main : ∀ (a b c : ℝ), a * b * c = 1 → a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c := by
    intro a b c h
    have h₁ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c := by
      -- Use non-linear arithmetic to prove the inequality
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1)]
    exact h₁
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_practice_problem_1 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 7 + b ^ 7 + c ^ 7 ≥ a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3 := by
  intro a b c h
  have h_main : a ^ 7 + b ^ 7 + c ^ 7 ≥ a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3 := by
    have h₁ : 4 * a ^ 7 + 3 * b ^ 7 ≥ 7 * a ^ 4 * b ^ 3 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - 2 * a * b + b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a ^ 3 - 2 * a ^ 2 * b + a * b ^ 2), sq_nonneg (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3), mul_nonneg h.1 (sq_nonneg (a ^ 2 - b ^ 2)), mul_nonneg h.1 (sq_nonneg (a ^ 2 - 2 * a * b + b ^ 2)), mul_nonneg h.1 (sq_nonneg (a ^ 2 + b ^ 2)), mul_nonneg h.1 (sq_nonneg (a ^ 3 - b ^ 3)), mul_nonneg h.1 (sq_nonneg (a ^ 3 - 2 * a ^ 2 * b + a * b ^ 2)), mul_nonneg h.1 (sq_nonneg (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)), mul_nonneg h.2.1 (sq_nonneg (a ^ 2 - b ^ 2)), mul_nonneg h.2.1 (sq_nonneg (a ^ 2 - 2 * a * b + b ^ 2)), mul_nonneg h.2.1 (sq_nonneg (a ^ 2 + b ^ 2)), mul_nonneg h.2.1 (sq_nonneg (a ^ 3 - b ^ 3)), mul_nonneg h.2.1 (sq_nonneg (a ^ 3 - 2 * a ^ 2 * b + a * b ^ 2)), mul_nonneg h.2.1 (sq_nonneg (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3))]
    have h₂ : 4 * b ^ 7 + 3 * c ^ 7 ≥ 7 * b ^ 4 * c ^ 3 := by
      nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - 2 * b * c + c ^ 2), sq_nonneg (b ^ 2 + c ^ 2), sq_nonneg (b ^ 3 - c ^ 3), sq_nonneg (b ^ 3 - 2 * b ^ 2 * c + b * c ^ 2), sq_nonneg (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3), mul_nonneg h.2.1 (sq_nonneg (b ^ 2 - c ^ 2)), mul_nonneg h.2.1 (sq_nonneg (b ^ 2 - 2 * b * c + c ^ 2)), mul_nonneg h.2.1 (sq_nonneg (b ^ 2 + c ^ 2)), mul_nonneg h.2.1 (sq_nonneg (b ^ 3 - c ^ 3)), mul_nonneg h.2.1 (sq_nonneg (b ^ 3 - 2 * b ^ 2 * c + b * c ^ 2)), mul_nonneg h.2.1 (sq_nonneg (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3)), mul_nonneg h.2.2 (sq_nonneg (b ^ 2 - c ^ 2)), mul_nonneg h.2.2 (sq_nonneg (b ^ 2 - 2 * b * c + c ^ 2)), mul_nonneg h.2.2 (sq_nonneg (b ^ 2 + c ^ 2)), mul_nonneg h.2.2 (sq_nonneg (b ^ 3 - c ^ 3)), mul_nonneg h.2.2 (sq_nonneg (b ^ 3 - 2 * b ^ 2 * c + b * c ^ 2)), mul_nonneg h.2.2 (sq_nonneg (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3))]
    have h₃ : 4 * c ^ 7 + 3 * a ^ 7 ≥ 7 * c ^ 4 * a ^ 3 := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c ^ 2 - 2 * c * a + a ^ 2), sq_nonneg (c ^ 2 + a ^ 2), sq_nonneg (c ^ 3 - a ^ 3), sq_nonneg (c ^ 3 - 2 * c ^ 2 * a + c * a ^ 2), sq_nonneg (c ^ 3 + c ^ 2 * a + c * a ^ 2 + a ^ 3), mul_nonneg h.2.2 (sq_nonneg (c ^ 2 - a ^ 2)), mul_nonneg h.2.2 (sq_nonneg (c ^ 2 - 2 * c * a + a ^ 2)), mul_nonneg h.2.2 (sq_nonneg (c ^ 2 + a ^ 2)), mul_nonneg h.2.2 (sq_nonneg (c ^ 3 - a ^ 3)), mul_nonneg h.2.2 (sq_nonneg (c ^ 3 - 2 * c ^ 2 * a + c * a ^ 2)), mul_nonneg h.2.2 (sq_nonneg (c ^ 3 + c ^ 2 * a + c * a ^ 2 + a ^ 3)), mul_nonneg h.1 (sq_nonneg (c ^ 2 - a ^ 2)), mul_nonneg h.1 (sq_nonneg (c ^ 2 - 2 * c * a + a ^ 2)), mul_nonneg h.1 (sq_nonneg (c ^ 2 + a ^ 2)), mul_nonneg h.1 (sq_nonneg (c ^ 3 - a ^ 3)), mul_nonneg h.1 (sq_nonneg (c ^ 3 - 2 * c ^ 2 * a + c * a ^ 2)), mul_nonneg h.1 (sq_nonneg (c ^ 3 + c ^ 2 * a + c * a ^ 2 + a ^ 3))]
    -- Combine the inequalities to get the final result
    nlinarith [sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (b ^ 3 - c ^ 3), sq_nonneg (c ^ 3 - a ^ 3),
      mul_nonneg h.1 (sq_nonneg (a - b)), mul_nonneg h.1 (sq_nonneg (b - c)), mul_nonneg h.1 (sq_nonneg (c - a)),
      mul_nonneg h.2.1 (sq_nonneg (a - b)), mul_nonneg h.2.1 (sq_nonneg (b - c)), mul_nonneg h.2.1 (sq_nonneg (c - a)),
      mul_nonneg h.2.2 (sq_nonneg (a - b)), mul_nonneg h.2.2 (sq_nonneg (b - c)), mul_nonneg h.2.2 (sq_nonneg (c - a))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_practice_problem_4 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ 1 / a + 1 / b + 1 / c = 1 → (a + 1) * (b + 1) * (c + 1) ≥ 64 := by
  intro a b c h
  have h_main : (a + 1) * (b + 1) * (c + 1) ≥ 64 := by
    rcases h with ⟨ha, hb, hc, h⟩
    have h₁ : 0 < a * b * c := by positivity
    have h₂ : 0 < a * b := by positivity
    have h₃ : 0 < a * c := by positivity
    have h₄ : 0 < b * c := by positivity
    field_simp [ha.ne', hb.ne', hc.ne'] at h
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (b * c - a * c),
      mul_self_nonneg (a * b + a * c + b * c - 3 * a * b * c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_2_4_left : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / a + 1 / b + 1 / c ≥ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  intro a b c h
  have h_main : 1 / a + 1 / b + 1 / c ≥ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
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

theorem evan_example_2_4_right : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c) := by
  intro a b c h
  have h_main : 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to prove the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (b * c - a * c),
      sq_nonneg (a * b + b * c + a * c - 3 * a * b * c),
      sq_nonneg (a * b + b * c + a * c - 3 * a * b * c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_2_7 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (b + c - a) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (c + a - b) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (a + b - c) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5 := by
  have h_main : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (b + c - a) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (c + a - b) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (a + b - c) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    field_simp [add_assoc]
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a^2 * b - b^2 * a), sq_nonneg (b^2 * c - c^2 * b), sq_nonneg (c^2 * a - a^2 * c),
      sq_nonneg (a^2 * b - a^2 * c), sq_nonneg (b^2 * c - b^2 * a), sq_nonneg (c^2 * a - c^2 * b),
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

theorem evan_example_3_5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 27 / (2 * (a + b + c) ^ 2) := by
  intro a b c h
  have h_main : 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 27 / (2 * (a + b + c) ^ 2) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b * c * a := by positivity
    have h₉ : 0 < a * b * c * b := by positivity
    have h₁₀ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
      sq_nonneg (a ^ 2 - a * b), sq_nonneg (a ^ 2 - a * c), sq_nonneg (b ^ 2 - a * b),
      sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - a * c), sq_nonneg (c ^ 2 - b * c),
      sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_problem_4_1 : ∀ (a b c : ℝ), a + b + c = 3 → Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ Real.sqrt 3 := by
  have h_main : ∀ (a b c : ℝ), a + b + c = 3 → Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ Real.sqrt 3 := by
    intro a b c h
    have h₁ : Real.sqrt (a ^ 2 + a * b + b ^ 2) ≥ Real.sqrt 3 / 2 * (a + b) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (a - b), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg 3, sq_nonneg (a + b - Real.sqrt 3)]
    have h₂ : Real.sqrt (b ^ 2 + b * c + c ^ 2) ≥ Real.sqrt 3 / 2 * (b + c) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (b - c), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg 3, sq_nonneg (b + c - Real.sqrt 3)]
    have h₃ : Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ Real.sqrt 3 / 2 * (c + a) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (c - a), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg 3, sq_nonneg (c + a - Real.sqrt 3)]
    have h₄ : Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ Real.sqrt 3 / 2 * ((a + b) + (b + c) + (c + a)) := by
      linarith [h₁, h₂, h₃]
    have h₅ : Real.sqrt 3 / 2 * ((a + b) + (b + c) + (c + a)) = Real.sqrt 3 / 2 * (2 * (a + b + c)) := by
      ring_nf
      <;>
      nlinarith
    have h₆ : Real.sqrt 3 / 2 * (2 * (a + b + c)) = Real.sqrt 3 * (a + b + c) := by
      ring_nf
      <;>
      nlinarith
    have h₇ : Real.sqrt 3 * (a + b + c) = Real.sqrt 3 * 3 := by
      rw [h]
    have h₈ : Real.sqrt 3 * 3 ≥ Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    nlinarith
  exact h_main
