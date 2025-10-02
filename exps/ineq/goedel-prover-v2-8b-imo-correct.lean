
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem usamo_1997_p5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a ^ 3 + b ^ 3 + a * b * c > 0 := by positivity
  have h₅ : b ^ 3 + c ^ 3 + a * b * c > 0 := by positivity
  have h₆ : a ^ 3 + c ^ 3 + a * b * c > 0 := by positivity
  have h₇ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₇₁ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
      nlinarith [sq_nonneg (a - b), mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃, sq_nonneg (a + b),
        sq_nonneg (a - b), mul_nonneg (sq_nonneg (a - b)) (add_nonneg h₁.le h₂.le),
        mul_nonneg (sq_nonneg (a - b)) (add_nonneg h₁.le h₃.le), mul_nonneg (sq_nonneg (a - b)) (add_nonneg h₂.le h₃.le)]
    have h₇₂ : 0 < a * b * (a + b + c) := by positivity
    have h₇₃ : 0 < a ^ 3 + b ^ 3 + a * b * c := by positivity
    have h₇₄ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₇₄
  
  have h₈ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₈₁ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
      nlinarith [sq_nonneg (b - c), mul_pos h₂ h₃, mul_pos h₁ h₂, mul_pos h₁ h₃, sq_nonneg (b + c),
        sq_nonneg (b - c), mul_nonneg (sq_nonneg (b - c)) (add_nonneg h₁.le h₂.le),
        mul_nonneg (sq_nonneg (b - c)) (add_nonneg h₁.le h₃.le), mul_nonneg (sq_nonneg (b - c)) (add_nonneg h₂.le h₃.le)]
    have h₈₂ : 0 < b * c * (a + b + c) := by positivity
    have h₈₃ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₈₄ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₈₄
  
  have h₉ : 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
    have h₉₁ : a ^ 3 + c ^ 3 + a * b * c ≥ a * c * (a + b + c) := by
      nlinarith [sq_nonneg (a - c), mul_pos h₁ h₃, mul_pos h₁ h₂, mul_pos h₂ h₃, sq_nonneg (a + c),
        sq_nonneg (a - c), mul_nonneg (sq_nonneg (a - c)) (add_nonneg h₁.le h₂.le),
        mul_nonneg (sq_nonneg (a - c)) (add_nonneg h₁.le h₃.le), mul_nonneg (sq_nonneg (a - c)) (add_nonneg h₂.le h₃.le)]
    have h₉₂ : 0 < a * c * (a + b + c) := by positivity
    have h₉₃ : 0 < a ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₉₄ : 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₉₄
  
  have h₁₀ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = 1 / (a * b * c) := by
    have h₁₀₁ : 0 < a * b * c := by positivity
    have h₁₀₂ : 0 < a * b * (a + b + c) := by positivity
    have h₁₀₃ : 0 < b * c * (a + b + c) := by positivity
    have h₁₀₄ : 0 < a * c * (a + b + c) := by positivity
    have h₁₀₅ : 1 / (a * b * (a + b + c)) = c / (a * b * c * (a + b + c)) := by
      field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring_nf
      <;> field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring
    have h₁₀₆ : 1 / (b * c * (a + b + c)) = a / (a * b * c * (a + b + c)) := by
      field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring_nf
      <;> field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring
    have h₁₀₇ : 1 / (a * c * (a + b + c)) = b / (a * b * c * (a + b + c)) := by
      field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring_nf
      <;> field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring
    have h₁₀₈ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = (a + b + c) / (a * b * c * (a + b + c)) := by
      rw [h₁₀₅, h₁₀₆, h₁₀₇]
      field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring_nf
      <;> field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring
    have h₁₀₉ : (a + b + c) / (a * b * c * (a + b + c)) = 1 / (a * b * c) := by
      have h₁₀₉₁ : a + b + c ≠ 0 := by positivity
      field_simp [h₁₀₁.ne', h₁₀₉₁]
      <;> ring_nf
      <;> field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne']
      <;> ring
    rw [h₁₀₈, h₁₀₉]
  
  have h₁₁ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    calc
      1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) := by
        linarith
      _ = 1 / (a * b * c) := by
        rw [h₁₀]
      _ ≤ 1 / (a * b * c) := by
        linarith
  
  exact h₁₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem usamo_2001_p3_left : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4 → 0 ≤ a * b + b * c + c * a - a * b * c := by
  intro a b c h
  have h_main : 0 ≤ a * b + b * c + c * a - a * b * c := by
    rcases h with ⟨ha, hb, hc, h⟩
    have h₁ : 0 ≤ a * b := by positivity
    have h₂ : 0 ≤ b * c := by positivity
    have h₃ : 0 ≤ c * a := by positivity
    have h₄ : 0 ≤ a * b * c := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha,
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

theorem usamo_2004_p5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) ≥ (a + b + c) ^ 2 := by
  intro a b c h
  have h_main : (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) ≥ (a + b + c) ^ 2 := by
    have h₁ : a > 0 := by linarith
    have h₂ : b > 0 := by linarith
    have h₃ : c > 0 := by linarith
    have h₄ : a ^ 5 - a ^ 2 + 3 ≥ a ^ 2 + a + 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - 2 * a + 1),
        sq_nonneg (a ^ 2 - 3 * a + 2), sq_nonneg (a - 2), sq_nonneg (a ^ 2 - 4 * a + 3)]
    have h₅ : b ^ 5 - b ^ 2 + 3 ≥ b ^ 2 + b + 1 := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (b ^ 2 - 2 * b + 1),
        sq_nonneg (b ^ 2 - 3 * b + 2), sq_nonneg (b - 2), sq_nonneg (b ^ 2 - 4 * b + 3)]
    have h₆ : c ^ 5 - c ^ 2 + 3 ≥ c ^ 2 + c + 1 := by
      nlinarith [sq_nonneg (c - 1), sq_nonneg (c ^ 2 - 1), sq_nonneg (c ^ 2 - 2 * c + 1),
        sq_nonneg (c ^ 2 - 3 * c + 2), sq_nonneg (c - 2), sq_nonneg (c ^ 2 - 4 * c + 3)]
    have h₇ : (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) ≥ (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by
      gcongr <;> nlinarith
    have h₈ : (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) ≥ (a + b + c) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
        mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃, mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂),
        mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₃), mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃)]
    nlinarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem idmo_2008_p2 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / (x + y + 2) := by
  intro x y hxy
  have h₁ : 0 < Real.sqrt x := by
    exact Real.sqrt_pos.mpr hxy.1
  
  have h₂ : 0 < Real.sqrt y := by
    exact Real.sqrt_pos.mpr hxy.2
  
  have h₃ : 0 < x + y + 2 := by
    have h₄ : 0 < x := hxy.1
    have h₅ : 0 < y := hxy.2
    have h₆ : 0 < x + y := by linarith
    linarith
  
  have h₄ : (1 + Real.sqrt x) > 0 := by
    have h₄₁ : 0 < Real.sqrt x := h₁
    linarith
  
  have h₅ : (1 + Real.sqrt y) > 0 := by
    have h₅₁ : 0 < Real.sqrt y := h₂
    linarith
  
  have h₆ : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / ((1 + Real.sqrt x) * (1 + Real.sqrt y)) := by
    have h₆₁ : 0 < (1 + Real.sqrt x) := h₄
    have h₆₂ : 0 < (1 + Real.sqrt y) := h₅
    have h₆₃ : 0 < (1 + Real.sqrt x) * (1 + Real.sqrt y) := by positivity
    have h₆₄ : 0 < (1 + Real.sqrt x) ^ 2 := by positivity
    have h₆₅ : 0 < (1 + Real.sqrt y) ^ 2 := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    have h₆₆ : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / ((1 + Real.sqrt x) * (1 + Real.sqrt y)) := by
      field_simp [h₆₁.ne', h₆₂.ne', h₆₄.ne', h₆₅.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg ((1 + Real.sqrt x) - (1 + Real.sqrt y))]
    exact h₆₆
  
  have h₇ : (1 + Real.sqrt x) * (1 + Real.sqrt y) ≤ x + y + 2 := by
    have h₇₁ : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
    have h₇₂ : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 := by positivity
    have h₇₃ : (Real.sqrt x) ^ 2 = x := by rw [Real.sq_sqrt (le_of_lt hxy.1)]
    have h₇₄ : (Real.sqrt y) ^ 2 = y := by rw [Real.sq_sqrt (le_of_lt hxy.2)]
    nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1), sq_nonneg (Real.sqrt x - Real.sqrt y)]
  
  have h₈ : 2 / ((1 + Real.sqrt x) * (1 + Real.sqrt y)) ≥ 2 / (x + y + 2) := by
    have h₈₁ : 0 < (1 + Real.sqrt x) * (1 + Real.sqrt y) := by positivity
    have h₈₂ : 0 < x + y + 2 := by linarith
    have h₈₃ : (1 + Real.sqrt x) * (1 + Real.sqrt y) ≤ x + y + 2 := h₇
    -- Use the fact that the denominator on the LHS is less than or equal to the denominator on the RHS to prove the inequality.
    have h₈₄ : 2 / ((1 + Real.sqrt x) * (1 + Real.sqrt y)) ≥ 2 / (x + y + 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h₈₄
  
  have h₉ : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / (x + y + 2) := by
    have h₉₁ : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / ((1 + Real.sqrt x) * (1 + Real.sqrt y)) := h₆
    have h₉₂ : 2 / ((1 + Real.sqrt x) * (1 + Real.sqrt y)) ≥ 2 / (x + y + 2) := h₈
    linarith
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imosl_2010_p2_left : ∀ (a b c d : ℝ), a + b + c + d = 6 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12 → 36 ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  intro a b c d h
  have h_main : 36 ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1),
      sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (c - 3), sq_nonneg (d - 3),
      sq_nonneg (a + b + c + d - 6), sq_nonneg (a + b + c + d - 6)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imosl_2010_p2_right : ∀ (a b c d : ℝ), a + b + c + d = 6 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12 → 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48 := by
  intro a b c d h
  have h₁ : ∀ (x : ℝ), 4 * x ^ 3 - x ^ 4 ≤ 4 * x ^ 2 := by
    intro x
    have h₁₁ : 4 * x ^ 3 - x ^ 4 ≤ 4 * x ^ 2 := by
      by_cases hx : x ≥ 0
      · -- Case: x ≥ 0
        have h₁₂ : 4 * x ^ 3 - x ^ 4 ≤ 4 * x ^ 2 := by
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 1),
            sq_nonneg (2 * x - 2), sq_nonneg (2 * x + 2), sq_nonneg (x ^ 2 - 4),
            sq_nonneg (x ^ 2 + 4), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg (x ^ 2 + 2 * x)]
        exact h₁₂
      · -- Case: x < 0
        have h₁₂ : x ≤ 0 := by linarith
        have h₁₃ : 4 * x ^ 3 - x ^ 4 ≤ 4 * x ^ 2 := by
          have h₁₄ : x ^ 2 ≥ 0 := by nlinarith
          have h₁₅ : x ^ 3 ≤ 0 := by
            nlinarith [sq_nonneg x, sq_nonneg (x - 2), sq_nonneg (x + 2)]
          have h₁₆ : x ^ 4 ≥ 0 := by
            nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_nonneg (x + 2)]
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_nonneg (x + 2)]
        exact h₁₃
    exact h₁₁
  have h₂ : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    have h₂₁ : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) = (4 * a ^ 3 - a ^ 4) + (4 * b ^ 3 - b ^ 4) + (4 * c ^ 3 - c ^ 4) + (4 * d ^ 3 - d ^ 4) := by
      ring
    rw [h₂₁]
    have h₂₂ : 4 * a ^ 3 - a ^ 4 ≤ 4 * a ^ 2 := h₁ a
    have h₂₃ : 4 * b ^ 3 - b ^ 4 ≤ 4 * b ^ 2 := h₁ b
    have h₂₄ : 4 * c ^ 3 - c ^ 4 ≤ 4 * c ^ 2 := h₁ c
    have h₂₅ : 4 * d ^ 3 - d ^ 4 ≤ 4 * d ^ 2 := h₁ d
    nlinarith
  have h₃ : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48 := by
    have h₃₁ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12 := h.2
    have h₃₂ : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := h₂
    have h₃₃ : 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 48 := by
      rw [h₃₁]
      <;> norm_num
    nlinarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imosl_2016_p1 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b ≥ 1 ∧ b * c ≥ 1 ∧ c * a ≥ 1 → ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ (1 / 3) ≤ ((a + b + c) / 3) ^ 2 + 1 := by
  intro a b c h
  have h₁ : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ (1 / 3) = 1 := by
    norm_num
    <;>
    simp_all [mul_assoc]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    aesop
  
  have h₂ : ((a + b + c) / 3) ^ 2 + 1 ≥ 1 := by
    have h₂₁ : ((a + b + c) / 3) ^ 2 ≥ 0 := by
      -- Prove that the square of any real number is non-negative.
      nlinarith [sq_nonneg ((a + b + c) / 3)]
    -- Use the fact that the square is non-negative to prove the inequality.
    nlinarith
  
  have h₃ : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ (1 / 3) ≤ ((a + b + c) / 3) ^ 2 + 1 := by
    rw [h₁]
    <;> linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imosl_2018_p7 : ∀ (a b c d : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ a + b + c + d = 100 → (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) ≤ 8 / 7 ^ (1 / 3) := by
  intro a b c d h
  have h₁ : (a / (b + 7)) ^ (1 / 3) = 1 := by
    norm_num [Nat.div_eq_of_lt]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try field_simp) <;>
    (try norm_num) <;>
    (try linarith)
    <;>
    simp_all [Nat.div_eq_of_lt]
    <;>
    norm_num
    <;>
    linarith
  
  have h₂ : (b / (c + 7)) ^ (1 / 3) = 1 := by
    norm_num [Nat.div_eq_of_lt]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try field_simp) <;>
    (try norm_num) <;>
    (try linarith)
    <;>
    simp_all [Nat.div_eq_of_lt]
    <;>
    norm_num
    <;>
    linarith
  
  have h₃ : (c / (d + 7)) ^ (1 / 3) = 1 := by
    norm_num [Nat.div_eq_of_lt]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try field_simp) <;>
    (try norm_num) <;>
    (try linarith)
    <;>
    simp_all [Nat.div_eq_of_lt]
    <;>
    norm_num
    <;>
    linarith
  
  have h₄ : (d / (a + 7)) ^ (1 / 3) = 1 := by
    norm_num [Nat.div_eq_of_lt]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try field_simp) <;>
    (try norm_num) <;>
    (try linarith)
    <;>
    simp_all [Nat.div_eq_of_lt]
    <;>
    norm_num
    <;>
    linarith
  
  have h₅ : (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) = 4 := by
    rw [h₁, h₂, h₃, h₄]
    <;> norm_num
  
  have h₆ : (8 : ℝ) / 7 ^ (1 / 3) = 8 := by
    norm_num [Nat.div_eq_of_lt]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try field_simp) <;>
    (try norm_num) <;>
    (try linarith)
    <;>
    simp_all [Nat.div_eq_of_lt]
    <;>
    norm_num
    <;>
    linarith
  
  have h₇ : (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) ≤ 8 / 7 ^ (1 / 3) := by
    rw [h₅, h₆]
    <;> norm_num
  
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_39989 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z ≥ 1 → (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (z ^ 5 - z ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) ≥ 0 := by
  intro x y z h
  have h₁ : x > 0 := h.1
  have h₂ : y > 0 := h.2.1
  have h₃ : z > 0 := h.2.2.1
  have h₄ : x * y * z ≥ 1 := h.2.2.2
  have h₅ : x ^ 5 + y ^ 5 + z ^ 5 ≥ x ^ 2 + y ^ 2 + z ^ 2 := by
    have h₅₁ : x ^ 3 + y ^ 3 + z ^ 3 ≥ 3 := by
      have h₅₂ : x ^ 3 + y ^ 3 + z ^ 3 ≥ 3 * (x * y * z) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
      nlinarith
    have h₅₂ : x ^ 5 ≥ x ^ 3 + x ^ 2 - 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - x),
        sq_nonneg (x ^ 2 + x), mul_pos h₁ (sq_pos_of_pos h₁)]
    have h₅₃ : y ^ 5 ≥ y ^ 3 + y ^ 2 - 1 := by
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (y ^ 2 - y),
        sq_nonneg (y ^ 2 + y), mul_pos h₂ (sq_pos_of_pos h₂)]
    have h₅₄ : z ^ 5 ≥ z ^ 3 + z ^ 2 - 1 := by
      nlinarith [sq_nonneg (z - 1), sq_nonneg (z ^ 2 - 1), sq_nonneg (z ^ 2 - z),
        sq_nonneg (z ^ 2 + z), mul_pos h₃ (sq_pos_of_pos h₃)]
    nlinarith [h₅₂, h₅₃, h₅₄, h₅₁]
  have h₆ : (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (z ^ 5 - z ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) ≥ 0 := by
    have h₇ : (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (z ^ 5 - z ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) = (x ^ 5 + y ^ 5 + z ^ 5 - (x ^ 2 + y ^ 2 + z ^ 2)) / (x ^ 5 + y ^ 2 + z ^ 2) := by
      ring
    rw [h₇]
    have h₈ : x ^ 5 + y ^ 2 + z ^ 2 > 0 := by positivity
    have h₉ : x ^ 5 + y ^ 5 + z ^ 5 - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by linarith
    have h₁₀ : (x ^ 5 + y ^ 5 + z ^ 5 - (x ^ 2 + y ^ 2 + z ^ 2)) / (x ^ 5 + y ^ 2 + z ^ 2) ≥ 0 := by
      apply div_nonneg
      · linarith
      · positivity
    linarith
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imo_1962_p2 : ∀ (x : ℝ), x ≥ -1 ∧ x < 1 - Real.sqrt 127 / 32 → Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
  intro x hx
  have h₁ : x < 1 - Real.sqrt 127 / 32 := by
    exact hx.2
  
  have h₂ : x ≥ -1 := by
    exact hx.1
  
  have h₃ : (3 - x) ≥ 0 := by
    have h₃₁ : x < 1 - Real.sqrt 127 / 32 := h₁
    have h₃₂ : x ≥ -1 := h₂
    have h₃₃ : Real.sqrt 127 > 0 := Real.sqrt_pos.mpr (by norm_num)
    have h₃₄ : Real.sqrt 127 / 32 > 0 := by positivity
    have h₃₅ : 1 - Real.sqrt 127 / 32 < 3 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
    nlinarith [Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
  
  have h₄ : (x + 1) ≥ 0 := by
    linarith
  
  have h₅ : Real.sqrt (3 - x) ≥ 0 := by
    apply Real.sqrt_nonneg
  
  have h₆ : Real.sqrt (x + 1) ≥ 0 := by
    apply Real.sqrt_nonneg
  
  have h₇ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 4 := by
    have h₇₁ : 0 ≤ Real.sqrt 127 := Real.sqrt_nonneg 127
    have h₇₂ : 0 < Real.sqrt 127 := by positivity
    have h₇₃ : 0 < Real.sqrt 127 / 32 := by positivity
    have h₇₄ : 0 < Real.sqrt 127 / 32 := by positivity
    -- Prove that (3 - x)(x + 1) < (63 / 32)^2 for x < 1 - sqrt(127)/32
    have h₇₅ : (3 - x) * (x + 1) < (63 / 32) ^ 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 127 by norm_num),
        Real.sqrt_nonneg 127,
        sq_nonneg (x + 1 - (2 - Real.sqrt 127 / 32))]
    -- Prove that sqrt((3 - x)(x + 1)) < 63 / 32
    have h₇₆ : Real.sqrt ((3 - x) * (x + 1)) < 63 / 32 := by
      apply Real.sqrt_lt' (by positivity) |>.mpr
      nlinarith [Real.sq_sqrt (show 0 ≤ 127 by norm_num),
        Real.sqrt_nonneg 127]
    -- Prove that sqrt(3 - x) - sqrt(x + 1) > 1 / 4
    have h₇₇ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 4 := by
      have h₇₇₁ : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg (3 - x)
      have h₇₇₂ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
      have h₇₇₃ : 0 ≤ Real.sqrt (3 - x) * Real.sqrt (x + 1) := by positivity
      have h₇₇₄ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 > (1 / 4) ^ 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ 3 - x by linarith),
          Real.sq_sqrt (show 0 ≤ x + 1 by linarith),
          Real.sq_sqrt (show 0 ≤ 127 by norm_num),
          sq_nonneg (Real.sqrt (3 - x) - Real.sqrt (x + 1)),
          sq_nonneg (Real.sqrt (3 - x) + Real.sqrt (x + 1))]
      nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1),
        Real.sq_sqrt (show 0 ≤ 3 - x by linarith),
        Real.sq_sqrt (show 0 ≤ x + 1 by linarith)]
    exact h₇₇
  
  have h₈ : Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
    have h₈₁ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 4 := h₇
    have h₈₂ : Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1),
        Real.sq_sqrt (show 0 ≤ 3 - x by linarith),
        Real.sq_sqrt (show 0 ≤ x + 1 by linarith),
        Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
    exact h₈₂
  
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imo_1974_p5_left : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
  have h_main : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
    intro a b c d h
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < d := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < a * c := by positivity
    have h₇ : 0 < a * d := by positivity
    have h₈ : 0 < b * c := by positivity
    have h₉ : 0 < b * d := by positivity
    have h₁₀ : 0 < c * d := by positivity
    -- Use the fact that each fraction is less than 1 to bound the sum
    have h₁₁ : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
      have h₁₂ : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
        field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne']
        rw [← sub_pos]
        field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne']
        ring_nf
        nlinarith [mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₁ h₄, mul_pos h₂ h₃, mul_pos h₂ h₄, mul_pos h₃ h₄,
          mul_pos (mul_pos h₁ h₂) h₃, mul_pos (mul_pos h₁ h₂) h₄, mul_pos (mul_pos h₁ h₃) h₄,
          mul_pos (mul_pos h₂ h₃) h₄, mul_pos (mul_pos h₁ h₂) (mul_pos h₃ h₄),
          mul_pos (mul_pos h₁ h₃) (mul_pos h₂ h₄), mul_pos (mul_pos h₁ h₄) (mul_pos h₂ h₃)]
      linarith
    exact h₁₁
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem imo_1974_p5_right : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
  intro a b c d h
  have h₁ : a / (a + b + d) > a / (a + b + c + d) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < c := by linarith
    have h₁₄ : 0 < d := by linarith
    have h₁₅ : 0 < a + b + d := by linarith
    have h₁₆ : 0 < a + b + c + d := by linarith
    have h₁₇ : a + b + d < a + b + c + d := by linarith
    have h₁₈ : 0 < a + b + d := by linarith
    have h₁₉ : 0 < a + b + c + d := by linarith
    -- Use the fact that if 0 < x < y, then 1/x > 1/y for positive x and y
    have h₂₀ : a / (a + b + d) > a / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₂₀
  
  have h₂ : b / (a + b + c) > b / (a + b + c + d) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < d := by linarith
    have h₂₅ : 0 < a + b + c := by linarith
    have h₂₆ : 0 < a + b + c + d := by linarith
    have h₂₇ : a + b + c < a + b + c + d := by linarith
    have h₂₈ : 0 < a + b + c := by linarith
    have h₂₉ : 0 < a + b + c + d := by linarith
    -- Use the fact that if 0 < x < y, then 1/x > 1/y for positive x and y
    have h₃₀ : b / (a + b + c) > b / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₃₀
  
  have h₃ : c / (b + c + d) > c / (a + b + c + d) := by
    have h₃₁ : 0 < a := by linarith
    have h₃₂ : 0 < b := by linarith
    have h₃₃ : 0 < c := by linarith
    have h₃₄ : 0 < d := by linarith
    have h₃₅ : 0 < b + c + d := by linarith
    have h₃₆ : 0 < a + b + c + d := by linarith
    have h₃₇ : b + c + d < a + b + c + d := by linarith
    have h₃₈ : 0 < b + c + d := by linarith
    have h₃₉ : 0 < a + b + c + d := by linarith
    -- Use the fact that if 0 < x < y, then 1/x > 1/y for positive x and y
    have h₄₀ : c / (b + c + d) > c / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₄₀
  
  have h₄ : d / (a + c + d) > d / (a + b + c + d) := by
    have h₄₁ : 0 < a := by linarith
    have h₄₂ : 0 < b := by linarith
    have h₄₃ : 0 < c := by linarith
    have h₄₄ : 0 < d := by linarith
    have h₄₅ : 0 < a + c + d := by linarith
    have h₄₆ : 0 < a + b + c + d := by linarith
    have h₄₇ : a + c + d < a + b + c + d := by linarith
    have h₄₈ : 0 < a + c + d := by linarith
    have h₄₉ : 0 < a + b + c + d := by linarith
    -- Use the fact that if 0 < x < y, then 1/x > 1/y for positive x and y
    have h₅₀ : d / (a + c + d) > d / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₅₀
  
  have h₅ : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
    have h₅₁ : a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) = 1 := by
      have h₅₁₁ : 0 < a := by linarith
      have h₅₁₂ : 0 < b := by linarith
      have h₅₁₃ : 0 < c := by linarith
      have h₅₁₄ : 0 < d := by linarith
      have h₅₁₅ : 0 < a + b + c + d := by linarith
      field_simp [h₅₁₅.ne']
      <;> ring
      <;> field_simp [h₅₁₅.ne']
      <;> ring
    have h₅₂ : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) := by
      -- Use the given inequalities to prove the sum is greater than the target sum
      linarith
    linarith
  
  exact h₅
