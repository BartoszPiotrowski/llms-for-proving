
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_left : ∀ (a b : ℝ), a < 0 ∧ b < 0 → a * b > 0 := by
  intro a b h
  have h₁ : a * b > 0 := by
    have h₂ : a < 0 := h.1
    have h₃ : b < 0 := h.2
    -- Use the property that the product of two negative numbers is positive.
    have h₄ : a * b > 0 := by
      -- Multiply the inequalities a < 0 and b < 0
      nlinarith
    exact h₄
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_ii_left : ∀ (a b : ℝ), a < 0 ∧ b > 0 → a * b < 0 := by
  intro a b h
  have h_main : a * b < 0 := by
    have h₁ : a < 0 := h.1
    have h₂ : b > 0 := h.2
    -- Use the fact that if a is negative and b is positive, then a * b is negative.
    have h₃ : a * b < 0 := by
      -- Use the property of multiplication by a negative number.
      nlinarith
    exact h₃
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_iii : ∀ (a b c : ℝ), a < b ∧ b < c → a < c := by
  intro a b c h
  have h₁ : a < b := h.1
  have h₂ : b < c := h.2
  have h₃ : a < c := by
    -- Using the transitivity of the < relation, we can directly conclude that a < c.
    linarith
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_iv : ∀ (a b c d : ℝ), a < b ∧ c < d → a + c < b + d := by
  intro a b c d h
  have h₁ : a + c < b + c := by
    -- Add c to both sides of the inequality a < b
    linarith [h.1]
    <;> linarith [h.2]
    <;> linarith
  
  have h₂ : b + c < b + d := by
    -- Add b to both sides of the inequality c < d
    linarith [h.2]
    <;> linarith [h.1]
    <;> linarith
  
  have h_main : a + c < b + d := by
    -- Use the transitivity of the < relation to combine the inequalities a + c < b + c and b + c < b + d
    linarith
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_v : ∀ (a b : ℝ), a < b → -b < -a := by
  intro a b h
  have h₁ : -b < -a := by
    linarith
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_vi : ∀ (a : ℝ), a > 0 → 1 / a > 0 := by
  intro a ha
  have h_main : 1 / a > 0 := by
    -- We need to show that 1 / a > 0 given a > 0.
    have h₁ : 0 < a := ha
    -- Since a > 0, 1 / a is positive.
    have h₂ : 0 < 1 / a := by
      -- Use the fact that the reciprocal of a positive number is positive.
      apply div_pos
      · -- 1 > 0
        norm_num
      · -- a > 0
        exact h₁
    -- The result follows directly from the above steps.
    exact h₂
  -- The main result follows from the above steps.
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_vii : ∀ (a : ℝ), a < 0 → 1 / a < 0 := by
  have h_main : ∀ (a : ℝ), a < 0 → 1 / a < 0 := by
    intro a ha
    have h₁ : 1 / a < 0 := by
      -- Prove that the reciprocal of a negative number is negative.
      have h₂ : a < 0 := ha
      have h₃ : 1 / a < 0 := by
        -- Use the fact that the reciprocal of a negative number is negative.
        apply div_neg_of_pos_of_neg
        · -- Prove that 1 > 0
          norm_num
        · -- Prove that a < 0
          linarith
      exact h₃
    exact h₁
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_viii : ∀ (a b : ℝ), a > 0 ∧ b > 0 → a / b > 0 := by
  intro a b h
  have h₁ : a / b > 0 := by
    have h₂ : a > 0 := h.1
    have h₃ : b > 0 := h.2
    have h₄ : a / b > 0 := by
      -- Use the fact that both a and b are positive to prove that a / b is positive.
      apply div_pos h₂ h₃
    exact h₄
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_xi : ∀ (a : ℝ), 0 < a ∧ a < 1 → a ^ 2 < a := by
  intro a h
  have h_main : a ^ 2 < a := by
    have h₁ : 0 < a := h.1
    have h₂ : a < 1 := h.2
    have h₃ : a ^ 2 < a := by
      -- Use the fact that a < 1 and a > 0 to show a^2 < a
      nlinarith
    exact h₃
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_6 : ∀ (a b c : ℝ), |a| + |b| + |c| - |a + b| - |b + c| - |c + a| + |a + b + c| ≥ 0 := by
  intro a b c
  have h_main : |a| + |b| + |c| - |a + b| - |b + c| - |c + a| + |a + b + c| ≥ 0 := by
    cases' le_total 0 (a + b + c) with h h <;>
    cases' le_total 0 (a + b) with h₁ h₁ <;>
    cases' le_total 0 (b + c) with h₂ h₂ <;>
    cases' le_total 0 (c + a) with h₃ h₃ <;>
    cases' le_total 0 a with h₄ h₄ <;>
    cases' le_total 0 b with h₅ h₅ <;>
    cases' le_total 0 c with h₆ h₆ <;>
    simp_all only [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
    (try { linarith }) <;>
    (try { nlinarith }) <;>
    (try {
      cases' le_total 0 (a + b + c) with h₇ h₇ <;>
      simp_all only [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
      nlinarith
    }) <;>
    (try {
      cases' le_total 0 (a + b + c) with h₇ h₇ <;>
      cases' le_total 0 (a + b) with h₈ h₈ <;>
      cases' le_total 0 (b + c) with h₉ h₉ <;>
      cases' le_total 0 (c + a) with h₁₀ h₁₀ <;>
      simp_all only [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
      nlinarith
    })
    <;>
    nlinarith
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_1_left : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → 0 ≤ (b - a) / (1 - a * b) := by
  intro a b h
  have h₁ : 0 ≤ a * b := by
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    nlinarith
  
  have h₂ : a * b ≤ 1 := by
    have h₃ : a ≤ 1 := by linarith
    have h₄ : b ≤ 1 := by linarith
    have h₅ : 0 ≤ a := by linarith
    have h₆ : 0 ≤ b := by linarith
    nlinarith [mul_nonneg h₅ h₆, h₃, h₄]
  
  have h₃ : 1 - a * b ≥ 0 := by
    have h₄ : a * b ≤ 1 := by linarith
    nlinarith
  
  have h₄ : b - a ≥ 0 := by
    have h₅ : a ≤ b := by linarith
    have h₆ : 0 ≤ b - a := by linarith
    linarith
  
  have h₅ : 0 ≤ (b - a) / (1 - a * b) := by
    -- Use the fact that the denominator is non-negative and the numerator is non-negative to conclude the fraction is non-negative.
    have h₆ : 1 - a * b ≥ 0 := by linarith
    have h₇ : b - a ≥ 0 := by linarith
    have h₈ : (b - a) / (1 - a * b) ≥ 0 := by
      -- Use the division inequality to conclude the fraction is non-negative.
      apply div_nonneg h₇ h₆
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_1_right : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → (b - a) / (1 - a * b) ≤ 1 := by
  intro a b h
  have h₁ : (b - a) / (1 - a * b) ≤ 1 := by
    by_cases h₂ : a = 1
    · -- Case a = 1
      have h₃ : b = 1 := by
        linarith [h.1, h.2.1, h.2.2]
      rw [h₃, h₂]
      norm_num
    · -- Case a < 1
      have h₃ : a < 1 := by
        by_contra h₄
        have h₅ : a ≥ 1 := by linarith
        have h₆ : a = 1 := by linarith
        contradiction
      have h₄ : 1 - a * b > 0 := by
        by_contra h₅
        have h₆ : 1 - a * b ≤ 0 := by linarith
        have h₇ : a * b ≥ 1 := by linarith
        have h₈ : a ≥ 0 := by linarith
        have h₉ : b ≤ 1 := by linarith
        have h₁₀ : a * b ≤ a := by
          nlinarith
        have h₁₁ : a ≥ 1 := by
          nlinarith
        have h₁₂ : a < 1 := by
          linarith
        linarith
      have h₅ : (a + 1 : ℝ) > 0 := by nlinarith
      have h₆ : (b - 1 : ℝ) ≤ 0 := by nlinarith
      have h₇ : (a + 1 : ℝ) * (b - 1 : ℝ) ≤ 0 := by
        nlinarith
      have h₈ : a * b + b - a - 1 ≤ 0 := by
        nlinarith
      have h₉ : b - a ≤ 1 - a * b := by
        nlinarith
      have h₁₀ : (b - a) / (1 - a * b) ≤ 1 := by
        rw [div_le_one (by linarith)]
        nlinarith
      exact h₁₀
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_2_left : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → 0 ≤ a / (1 + b) + b / (1 + a) := by
  intro a b h
  have h₁ : 0 ≤ a / (1 + b) + b / (1 + a) := by
    have h₂ : 0 ≤ a := by linarith
    have h₃ : a ≤ b := by linarith
    have h₄ : b ≤ 1 := by linarith
    have h₅ : 0 ≤ b := by linarith
    have h₆ : 0 ≤ 1 + b := by linarith
    have h₇ : 0 ≤ 1 + a := by linarith
    have h₈ : 0 < 1 + b := by linarith
    have h₉ : 0 < 1 + a := by linarith
    have h₁₀ : 0 ≤ a * (1 + a) := by nlinarith
    have h₁₁ : 0 ≤ b * (1 + b) := by nlinarith
    have h₁₂ : 0 ≤ a * (1 + a) + b * (1 + b) := by nlinarith
    have h₁₃ : 0 ≤ a / (1 + b) + b / (1 + a) := by
      have h₁₄ : 0 ≤ a / (1 + b) := by
        apply div_nonneg
        · nlinarith
        · nlinarith
      have h₁₅ : 0 ≤ b / (1 + a) := by
        apply div_nonneg
        · nlinarith
        · nlinarith
      nlinarith
    exact h₁₃
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_2_right : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → a / (1 + b) + b / (1 + a) ≤ 1 := by
  intro a b h
  have h_main : a / (1 + b) + b / (1 + a) ≤ 1 := by
    have h₁ : 0 ≤ a := by linarith
    have h₂ : a ≤ b := by linarith
    have h₃ : b ≤ 1 := by linarith
    have h₄ : 0 ≤ b := by linarith
    have h₅ : 0 ≤ a * b := by positivity
    have h₆ : 0 ≤ 1 + a := by linarith
    have h₇ : 0 ≤ 1 + b := by linarith
    have h₈ : 0 < 1 + a := by linarith
    have h₉ : 0 < 1 + b := by linarith
    field_simp
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
      mul_nonneg h₁ (sub_nonneg.mpr h₂), mul_nonneg (sub_nonneg.mpr h₂) h₄,
      mul_nonneg (sub_nonneg.mpr h₃) h₁, mul_nonneg (sub_nonneg.mpr h₃) h₄]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_3_left : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → 0 ≤ a * b ^ 2 - b * a ^ 2 := by
  intro a b h
  have h_main : 0 ≤ a * b ^ 2 - b * a ^ 2 := by
    have h₁ : a * b ^ 2 - b * a ^ 2 = a * b * (b - a) := by
      ring
    rw [h₁]
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    have h₄ : b - a ≥ 0 := by linarith
    have h₅ : 0 ≤ a * b := by nlinarith
    have h₆ : 0 ≤ a * b * (b - a) := by
      -- Since a, b, and (b - a) are all non-negative, their product is non-negative.
      nlinarith
    nlinarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_3_right : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → a * b ^ 2 - b * a ^ 2 ≤ 1 / 4 := by
  have h_main : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → a * b ^ 2 - b * a ^ 2 ≤ 1 / 4 := by
    intro a b h
    have h₁ : a * b ^ 2 - b * a ^ 2 ≤ 1 / 4 := by
      cases' le_total a b with hab hab <;>
      cases' le_total 0 a with ha ha <;>
      cases' le_total a (1 / 2) with ha₂ ha₂ <;>
      nlinarith [sq_nonneg (b - a), sq_nonneg (b - 1 / 2), sq_nonneg (a - 1 / 2),
        mul_nonneg (sub_nonneg.mpr h.2.1) (sub_nonneg.mpr h.2.2),
        mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2.1),
        mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2.2),
        mul_nonneg (sub_nonneg.mpr h.2.1) (sub_nonneg.mpr h.2.2),
        mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h.2.1),
        mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h.2.2),
        mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr h.1),
        mul_nonneg (sub_nonneg.mpr ha₂) (sub_nonneg.mpr h.2.1),
        mul_nonneg (sub_nonneg.mpr ha₂) (sub_nonneg.mpr h.2.2),
        mul_nonneg (sub_nonneg.mpr ha₂) (sub_nonneg.mpr h.1)]
    exact h₁
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_9 : ∀ (a b x y : ℝ), a ≥ b ∧ x ≥ y → a * x + b * y ≥ a * y + b * x := by
  intro a b x y h
  have h₁ : a - b ≥ 0 := by
    linarith [h.1]

  have h₂ : x - y ≥ 0 := by
    linarith [h.2]

  have h₃ : (a - b) * (x - y) ≥ 0 := by
    -- Use the fact that the product of two non-negative numbers is non-negative.
    nlinarith

  have h₄ : a * x + b * y - (a * y + b * x) = (a - b) * (x - y) := by
    -- Use algebraic manipulation to show the equality.
    ring
    <;>
    (try norm_num)
    <;>
    (try linarith)
    <;>
    (try nlinarith)

  have h₅ : a * x + b * y ≥ a * y + b * x := by
    have h₅₁ : a * x + b * y - (a * y + b * x) ≥ 0 := by
      -- Use the fact that the difference is non-negative.
      linarith
    -- Use the fact that the difference is non-negative to conclude the inequality.
    linarith

  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_11 : ∀ (a b c d : ℝ), a + d = b + c → (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0 := by
  intro a b c d h
  have h₁ : d = b + c - a := by
    have h₁ : a + d = b + c := h
    linarith
  
  have h₂ : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b)^2 := by
    rw [h₁]
    ring_nf
    <;>
    (try nlinarith) <;>
    (try ring_nf) <;>
    (try linarith) <;>
    (try nlinarith) <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]) <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
  
  have h₃ : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0 := by
    rw [h₂]
    have h₄ : 2 * (a - b) ^ 2 ≥ 0 := by
      -- Use the fact that the square of any real number is non-negative.
      have h₅ : (a - b) ^ 2 ≥ 0 := by nlinarith
      nlinarith
    linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_12 : ∀ (a b c d : ℝ), a < b ∧ b < c ∧ c < d → (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 > 0 := by
  intro a b c d h
  have h₁ : a < b := by
    linarith [h.1]
  
  have h₂ : b < c := by
    linarith [h.2.1]
  
  have h₃ : c < d := by
    linarith [h.2.2]
  
  have h₄ : a < d := by
    linarith [h₁, h₂, h₃]
  
  have h₅ : (a - b) ^ 2 > 0 := by
    have h₅₁ : a - b ≠ 0 := by
      intro h₅₁
      linarith
    have h₅₂ : (a - b) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h₅₁
    exact h₅₂
  
  have h₆ : (b - c) ^ 2 > 0 := by
    have h₆₁ : b - c ≠ 0 := by
      intro h₆₁
      linarith
    have h₆₂ : (b - c) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h₆₁
    exact h₆₂
  
  have h₇ : (c - d) ^ 2 > 0 := by
    have h₇₁ : c - d ≠ 0 := by
      intro h₇₁
      linarith
    have h₇₂ : (c - d) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h₇₁
    exact h₇₂
  
  have h₈ : (d - a) ^ 2 > 0 := by
    have h₈₁ : d - a ≠ 0 := by
      intro h₈₁
      linarith
    have h₈₂ : (d - a) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h₈₁
    exact h₈₂
  
  have h₉ : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 > 0 := by
    -- Use the fact that the sum of positive numbers is positive
    have h₉₁ : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 > 0 := by
      -- Use linear arithmetic to prove the sum is positive
      have h₉₂ : 0 < (a - b) ^ 2 := h₅
      have h₉₃ : 0 < (b - c) ^ 2 := h₆
      have h₉₄ : 0 < (c - d) ^ 2 := h₇
      have h₉₅ : 0 < (d - a) ^ 2 := h₈
      -- Sum of positive numbers is positive
      linarith
    exact h₉₁
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_am_gm_inequality : ∀ (a b : ℝ), a ≥ 0 ∧ b ≥ 0 → (a + b) / 2 ≥ Real.sqrt (a * b) := by
  intro a b h
  have h_main : (a + b) / 2 ≥ Real.sqrt (a * b) := by
    have h₁ : 0 ≤ a := by linarith
    have h₂ : 0 ≤ b := by linarith
    have h₃ : 0 ≤ a * b := by positivity
    have h₄ : Real.sqrt (a * b) ≤ (a + b) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (Real.sqrt a - Real.sqrt b),
          Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
          sq_nonneg (Real.sqrt a + Real.sqrt b), sq_nonneg (Real.sqrt a - Real.sqrt b),
          sq_nonneg (a - b)]
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_18 : ∀ (x : ℝ), x ≥ 0 → 1 + x ≥ 2 * Real.sqrt x := by
  intro x hx
  have h_main : 1 + x ≥ 2 * Real.sqrt x := by
    have h₁ : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h₂ : 0 ≤ x := hx
    nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith),
      sq_nonneg (Real.sqrt x - 1),
      sq_nonneg (Real.sqrt x - x)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_19 : ∀ (x : ℝ), x > 0 → x + 1 / x ≥ 2 := by
  intro x hx
  have h₁ : x + 1 / x - 2 ≥ 0 := by
    have h₂ : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
      have h₃ : x ≠ 0 := by linarith
      field_simp [h₃]
      ring
      <;> field_simp [h₃]
      <;> ring
    rw [h₂]
    have h₃ : 0 < x := hx
    have h₄ : (x - 1) ^ 2 / x ≥ 0 := by
      apply div_nonneg
      · -- Prove that (x - 1)^2 ≥ 0
        nlinarith [sq_nonneg (x - 1)]
      · -- Prove that x > 0 implies x ≥ 0
        linarith
    exact h₄
  
  have h₂ : x + 1 / x ≥ 2 := by
    have h₃ : x + 1 / x - 2 ≥ 0 := h₁
    linarith
  
  exact h₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_21 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 2 * (x ^ 2 + y ^ 2) ≥ (x + y) ^ 2 := by
  have h_main : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 2 * (x ^ 2 + y ^ 2) ≥ (x + y) ^ 2 := by
    intro x y h
    have h₁ : 0 < x := h.1
    have h₂ : 0 < y := h.2
    have h₃ : 0 < x * y := mul_pos h₁ h₂
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 2 * x), sq_nonneg (x + y - 2 * y)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_22 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 1 / x + 1 / y ≥ 4 / (x + y) := by
  intro x y h
  have h_main : 1 / x + 1 / y ≥ 4 / (x + y) := by
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < x + y := by linarith
    have h₄ : 0 < x * y := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 2 * x), sq_nonneg (x + y - 2 * y),
      sq_nonneg (2 * x - x - y), sq_nonneg (2 * y - x - y)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_23 : ∀ (a b x : ℝ), a > 0 ∧ b > 0 ∧ x > 0 → a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
  intro a b x h
  have h₁ : a > 0 := h.1
  have h₂ : b > 0 := h.2.1
  have h₃ : x > 0 := h.2.2
  have h₄ : a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
    have h₅ : 0 < a * x := by positivity
    have h₆ : 0 < b / x := by positivity
    have h₇ : 0 < a * b := by positivity
    have h₈ : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr h₇
    -- Use the AM-GM inequality to prove the desired inequality
    have h₉ : a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
      -- Use the fact that the square of the difference is non-negative
      have h₁₀ : 0 < a * x * (b / x) := by positivity
      have h₁₁ : a * x * (b / x) = a * b := by
        field_simp
        <;> ring
      have h₁₂ : a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
        -- Use the AM-GM inequality
        nlinarith [Real.sq_sqrt (le_of_lt h₇), sq_nonneg (a * x - b / x),
          sq_nonneg (a * x - Real.sqrt (a * b)), sq_nonneg (b / x - Real.sqrt (a * b))]
      exact h₁₂
    exact h₉
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_14609 (a b : ℝ) (h : 0 < b ∧ b ≤ a) : 1 / 8 * ((a - b) ^ 2 / a) ≤ (a + b) / 2 - Real.sqrt (a * b) := by
  have h₁ : a > 0 := by linarith
  
  have h₂ : (a + b) / 2 - Real.sqrt (a * b) = ((Real.sqrt a - Real.sqrt b) ^ 2) / 2 := by
    have h₂₁ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₂₂ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₂₃ : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg (a * b)
    have h₂₄ : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (by linarith)]
      <;> ring_nf
    have h₂₅ : (a + b) / 2 - Real.sqrt (a * b) = (a + b) / 2 - Real.sqrt a * Real.sqrt b := by rw [h₂₄]
    rw [h₂₅]
    have h₂₆ : ((Real.sqrt a - Real.sqrt b) ^ 2) / 2 = (a + b) / 2 - Real.sqrt a * Real.sqrt b := by
      have h₂₆₁ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
      nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
        sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a + Real.sqrt b)]
    linarith
  
  have h₃ : 1 / 8 * ((a - b) ^ 2 / a) = ((Real.sqrt a + Real.sqrt b) ^ 2 * (Real.sqrt a - Real.sqrt b) ^ 2) / (8 * a) := by
    have h₃₁ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₃₂ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₃₃ : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
      have h₃₃₁ : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
      have h₃₃₂ : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b
      have h₃₃₃ : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
      have h₃₃₄ : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
      nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
        mul_nonneg h₃₃₁ h₃₃₂]
    rw [h₃₃]
    <;> field_simp [h₁.ne']
    <;> ring_nf
    <;> field_simp [h₁.ne']
    <;> ring_nf
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
  
  have h₄ : 1 / 8 * ((a - b) ^ 2 / a) ≤ (a + b) / 2 - Real.sqrt (a * b) := by
    rw [h₂, h₃]
    have h₄₁ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₄₂ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₄₃ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
    have h₄₄ : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by positivity
    have h₄₅ : (Real.sqrt a + Real.sqrt b) ^ 2 * (Real.sqrt a - Real.sqrt b) ^ 2 / (8 * a) ≤ ((Real.sqrt a - Real.sqrt b) ^ 2) / 2 := by
      by_cases h₄₅₁ : Real.sqrt a - Real.sqrt b = 0
      · -- If sqrt(a) - sqrt(b) = 0, the inequality simplifies to 0 ≤ 0
        have h₄₅₂ : (Real.sqrt a - Real.sqrt b) ^ 2 = 0 := by
          nlinarith
        rw [h₄₅₂]
        norm_num
        <;> positivity
      · -- If sqrt(a) - sqrt(b) ≠ 0, we can simplify the inequality
        have h₄₅₃ : 0 < Real.sqrt a - Real.sqrt b := by
          by_contra h₄₅₄
          have h₄₅₅ : Real.sqrt a - Real.sqrt b ≤ 0 := by linarith
          have h₄₅₆ : Real.sqrt a ≤ Real.sqrt b := by linarith
          have h₄₅₇ : a ≤ b := by
            nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ a by linarith),
              Real.sq_sqrt (show 0 ≤ b by linarith)]
          have h₄₅₈ : b ≤ a := by linarith
          have h₄₅₉ : Real.sqrt a = Real.sqrt b := by
            nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ a by linarith),
              Real.sq_sqrt (show 0 ≤ b by linarith)]
          have h₄₅₁₀ : Real.sqrt a - Real.sqrt b = 0 := by linarith
          contradiction
          <;> linarith
        have h₄₅₄ : 0 < Real.sqrt a - Real.sqrt b := by linarith
        have h₄₅₅ : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 4 * a := by
          have h₄₅₅₁ : 0 ≤ a := by linarith
          have h₄₅₅₂ : 0 ≤ b := by linarith
          have h₄₅₅₃ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
          have h₄₅₅₄ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
          have h₄₅₅₅ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
          have h₄₅₅₆ : 0 ≤ a * b := by positivity
          have h₄₅₅₇ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
          -- Use the fact that the square of any real number is non-negative to prove the inequality.
          have h₄₅₅₈ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
          have h₄₅₅₉ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
          -- Use the fact that the square of any real number is non-negative to prove the inequality.
          have h₄₅₅₁₀ : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 4 * a := by
            nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
              sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a + Real.sqrt b),
              mul_self_nonneg (Real.sqrt a - 2 * Real.sqrt b), mul_self_nonneg (2 * Real.sqrt a - Real.sqrt b)]
          exact h₄₅₅₁₀
        have h₄₅₆ : ((Real.sqrt a + Real.sqrt b) ^ 2 * (Real.sqrt a - Real.sqrt b) ^ 2 / (8 * a)) ≤ ((Real.sqrt a - Real.sqrt b) ^ 2) / 2 := by
          have h₄₅₆₁ : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := by positivity
          have h₄₅₆₂ : 0 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by positivity
          have h₄₅₆₃ : 0 < a := by linarith
          have h₄₅₆₄ : 0 < 8 * a := by positivity
          have h₄₅₆₅ : (Real.sqrt a + Real.sqrt b) ^ 2 * (Real.sqrt a - Real.sqrt b) ^ 2 / (8 * a) ≤ ((Real.sqrt a - Real.sqrt b) ^ 2) / 2 := by
            rw [div_le_div_iff (by positivity) (by positivity)]
            nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith),
              mul_nonneg h₄₁ h₄₂, mul_nonneg (sq_nonneg (Real.sqrt a - Real.sqrt b)) (by positivity : (0 : ℝ) ≤ 2),
              mul_nonneg (sq_nonneg (Real.sqrt a - Real.sqrt b)) (by positivity : (0 : ℝ) ≤ 8 * a)]
          exact h₄₅₆₅
        exact h₄₅₆
    linarith
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_25_right : ∀ (a b : ℝ), 0 < b ∧ b ≤ a → (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := by
  intro a b h
  have h₁ : 0 < b := by
    linarith
  
  have h₂ : b ≤ a := by
    linarith
  
  have h₃ : 0 ≤ a * b := by
    nlinarith
  
  have h₄ : 0 ≤ Real.sqrt (a * b) := by
    apply Real.sqrt_nonneg
  
  have h₅ : (Real.sqrt (a * b)) ^ 2 = a * b := by
    rw [Real.sq_sqrt] <;> nlinarith
  
  have h_main : a ^ 2 - 6 * a * b - 3 * b ^ 2 + 8 * b * Real.sqrt (a * b) ≥ 0 := by
    have h₆ : 0 ≤ a := by linarith
    have h₇ : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg (a * b)
    have h₈ : 0 ≤ b * Real.sqrt (a * b) := by positivity
    -- We use the fact that the square of any real number is non-negative to prove the inequality.
    have h₉ : 0 ≤ a * b := by nlinarith
    have h₁₀ : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg (a * b)
    -- Use the fact that the square root of a product is less than or equal to the sum of the square roots.
    have h₁₁ : Real.sqrt (a * b) ≤ (a + b) / 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ a * b by nlinarith), sq_nonneg (a - b)]
    -- Use non-linear arithmetic to prove the main inequality.
    nlinarith [sq_nonneg (a - b), sq_nonneg (Real.sqrt (a * b) - b),
      sq_nonneg (Real.sqrt (a * b) - (a + b) / 2),
      Real.sq_sqrt (show 0 ≤ a * b by nlinarith),
      sq_nonneg (a - 3 * b), sq_nonneg (a + b - 4 * Real.sqrt (a * b))]
  
  have h_final : (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := by
    have h₆ : 0 < b := h₁
    have h₇ : b ≤ a := h₂
    have h₈ : 0 ≤ a * b := h₃
    have h₉ : 0 ≤ Real.sqrt (a * b) := h₄
    have h₁₀ : (Real.sqrt (a * b)) ^ 2 = a * b := h₅
    have h₁₁ : a ^ 2 - 6 * a * b - 3 * b ^ 2 + 8 * b * Real.sqrt (a * b) ≥ 0 := h_main
    have h₁₂ : 8 * b * ((a + b) / 2 - Real.sqrt (a * b)) ≤ (a - b) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (Real.sqrt (a * b) - b),
        sq_nonneg (Real.sqrt (a * b) - (a + b) / 2)]
    have h₁₃ : (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := by
      calc
        (a + b) / 2 - Real.sqrt (a * b) = (8 * b * ((a + b) / 2 - Real.sqrt (a * b))) / (8 * b) := by
          field_simp [h₆.ne']
          <;> ring_nf
          <;> field_simp [h₆.ne']
          <;> linarith
        _ ≤ ((a - b) ^ 2) / (8 * b) := by
          gcongr
          <;> nlinarith
        _ = 1 / 8 * ((a - b) ^ 2 / b) := by
          field_simp [h₆.ne']
          <;> ring_nf
          <;> field_simp [h₆.ne']
          <;> linarith
    exact h₁₃
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_27 : ∀ (x y z : ℝ), ¬ (x = y) ∧ ¬ (y = z) ∧ ¬ (x = z) → x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
  have h_main : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
    intro x y z
    have h₁ : 0 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    nlinarith [sq_nonneg (x - y + y - z + z - x), sq_nonneg (x - y - (y - z)), sq_nonneg (y - z - (z - x)), sq_nonneg (z - x - (x - y))]
  
  have h_final : ∀ (x y z : ℝ), ¬ (x = y) ∧ ¬ (y = z) ∧ ¬ (x = z) → x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
    intro x y z h
    have h₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := h_main x y z
    exact h₁
  
  intro x y z h
  have h₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := h_final x y z h
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_28 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x * y + y * z + z * x ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
  intro x y z h
  have h₁ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
    have h₁₁ : 0 ≤ y := by linarith
    have h₁₂ : 0 ≤ z := by linarith
    have h₁₃ : 0 ≤ y * z := by positivity
    have h₁₄ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ y * z by positivity), sq_nonneg (y - z)]
    exact h₁₄
  
  have h₂ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
    have h₂₁ : 0 ≤ z := by linarith
    have h₂₂ : 0 ≤ x := by linarith
    have h₂₃ : 0 ≤ z * x := by positivity
    have h₂₄ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ z * x by positivity), sq_nonneg (z - x)]
    exact h₂₄
  
  have h₃ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    have h₃₁ : 0 ≤ x := by linarith
    have h₃₂ : 0 ≤ y := by linarith
    have h₃₃ : 0 ≤ x * y := by positivity
    have h₃₄ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ x * y by positivity), sq_nonneg (x - y)]
    exact h₃₄
  
  have h₄ : x * Real.sqrt (y * z) ≤ x * ((y + z) / 2) := by
    have h₄₁ : 0 < x := by linarith
    have h₄₂ : Real.sqrt (y * z) ≤ (y + z) / 2 := h₁
    nlinarith [h₄₁, h₄₂]
  
  have h₅ : y * Real.sqrt (z * x) ≤ y * ((z + x) / 2) := by
    have h₅₁ : 0 < y := by linarith
    have h₅₂ : Real.sqrt (z * x) ≤ (z + x) / 2 := h₂
    nlinarith [h₅₁, h₅₂]
  
  have h₆ : z * Real.sqrt (x * y) ≤ z * ((x + y) / 2) := by
    have h₆₁ : 0 < z := by linarith
    have h₆₂ : Real.sqrt (x * y) ≤ (x + y) / 2 := h₃
    nlinarith [h₆₁, h₆₂]
  
  have h₇ : x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) ≤ x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) := by
    linarith [h₄, h₅, h₆]
  
  have h₈ : x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) = x * y + y * z + z * x := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try ring_nf at *) <;>
    (try nlinarith) <;>
    (try linarith)
    <;>
    (try nlinarith [h.1, h.2.1, h.2.2])
  
  have h₉ : x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) ≤ x * y + y * z + z * x := by
    linarith [h₇, h₈]
  
  have h₁₀ : x * y + y * z + z * x ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
    linarith [h₉]
  
  exact h₁₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_29 : ∀ (x y : ℝ), x ^ 2 + y ^ 2 + 1 ≥ x * y + x + y := by
  have h_main : ∀ (x y : ℝ), x ^ 2 + y ^ 2 + 1 ≥ x * y + x + y := by
    intro x y
    have h₁ : x ^ 2 + y ^ 2 + 1 - (x * y + x + y) = (x - y) ^ 2 / 2 + (x - 1) ^ 2 / 2 + (y - 1) ^ 2 / 2 := by
      ring_nf
      <;>
      field_simp
      <;>
      ring_nf
      <;>
      nlinarith
    have h₂ : (x - y) ^ 2 / 2 + (x - 1) ^ 2 / 2 + (y - 1) ^ 2 / 2 ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    nlinarith [h₁, h₂]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_30 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → 1 / x + 1 / y + 1 / z ≥ 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) := by
  have h_main : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → 1 / x + 1 / y + 1 / z ≥ 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) := by
    intro x y z ⟨hx, hy, hz⟩
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    have h₇ : 0 < Real.sqrt (x * y) := Real.sqrt_pos.mpr h₄
    have h₈ : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr h₅
    have h₉ : 0 < Real.sqrt (z * x) := Real.sqrt_pos.mpr h₆
    -- Use the fact that the square root of a product is the product of the square roots
    have h₁₀ : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
      rw [Real.sqrt_mul (le_of_lt h₁)]
    have h₁₁ : Real.sqrt (y * z) = Real.sqrt y * Real.sqrt z := by
      rw [Real.sqrt_mul (le_of_lt h₂)]
    have h₁₂ : Real.sqrt (z * x) = Real.sqrt z * Real.sqrt x := by
      rw [Real.sqrt_mul (le_of_lt h₃)]
    -- Use the fact that the reciprocal of the product is the product of the reciprocals
    have h₁₃ : 1 / Real.sqrt (x * y) = 1 / (Real.sqrt x * Real.sqrt y) := by rw [h₁₀]
    have h₁₄ : 1 / Real.sqrt (y * z) = 1 / (Real.sqrt y * Real.sqrt z) := by rw [h₁₁]
    have h₁₅ : 1 / Real.sqrt (z * x) = 1 / (Real.sqrt z * Real.sqrt x) := by rw [h₁₂]
    -- Use the fact that the reciprocal of the product is the product of the reciprocals
    have h₁₆ : 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) = 1 / (Real.sqrt x * Real.sqrt y) + 1 / (Real.sqrt y * Real.sqrt z) + 1 / (Real.sqrt z * Real.sqrt x) := by
      rw [h₁₃, h₁₄, h₁₅]
      <;> ring
    rw [h₁₆]
    have h₁₇ : 1 / x + 1 / y + 1 / z ≥ 1 / (Real.sqrt x * Real.sqrt y) + 1 / (Real.sqrt y * Real.sqrt z) + 1 / (Real.sqrt z * Real.sqrt x) := by
      have h₁₈ : 1 / (Real.sqrt x * Real.sqrt y) ≤ (1 / x + 1 / y) / 2 := by
        -- Use the AM-HM inequality to bound the term 1 / (sqrt x * sqrt y)
        have h₁₉ : 0 < Real.sqrt x := Real.sqrt_pos.mpr h₁
        have h₂₀ : 0 < Real.sqrt y := Real.sqrt_pos.mpr h₂
        have h₂₁ : 0 < Real.sqrt x * Real.sqrt y := by positivity
        field_simp [h₁₉.ne', h₂₀.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt (le_of_lt h₁), Real.sq_sqrt (le_of_lt h₂),
          sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1)]
      have h₂₂ : 1 / (Real.sqrt y * Real.sqrt z) ≤ (1 / y + 1 / z) / 2 := by
        -- Use the AM-HM inequality to bound the term 1 / (sqrt y * sqrt z)
        have h₂₃ : 0 < Real.sqrt y := Real.sqrt_pos.mpr h₂
        have h₂₄ : 0 < Real.sqrt z := Real.sqrt_pos.mpr h₃
        have h₂₅ : 0 < Real.sqrt y * Real.sqrt z := by positivity
        field_simp [h₂₃.ne', h₂₄.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt y - Real.sqrt z), Real.sq_sqrt (le_of_lt h₂), Real.sq_sqrt (le_of_lt h₃),
          sq_nonneg (Real.sqrt y - 1), sq_nonneg (Real.sqrt z - 1)]
      have h₂₆ : 1 / (Real.sqrt z * Real.sqrt x) ≤ (1 / z + 1 / x) / 2 := by
        -- Use the AM-HM inequality to bound the term 1 / (sqrt z * sqrt x)
        have h₂₇ : 0 < Real.sqrt z := Real.sqrt_pos.mpr h₃
        have h₂₈ : 0 < Real.sqrt x := Real.sqrt_pos.mpr h₁
        have h₂₉ : 0 < Real.sqrt z * Real.sqrt x := by positivity
        field_simp [h₂₇.ne', h₂₈.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt z - Real.sqrt x), Real.sq_sqrt (le_of_lt h₃), Real.sq_sqrt (le_of_lt h₁),
          sq_nonneg (Real.sqrt z - 1), sq_nonneg (Real.sqrt x - 1)]
      -- Combine the bounds to get the final result
      have h₃₀ : 1 / (Real.sqrt x * Real.sqrt y) + 1 / (Real.sqrt y * Real.sqrt z) + 1 / (Real.sqrt z * Real.sqrt x) ≤ (1 / x + 1 / y) / 2 + (1 / y + 1 / z) / 2 + (1 / z + 1 / x) / 2 := by
        linarith
      have h₃₁ : (1 / x + 1 / y) / 2 + (1 / y + 1 / z) / 2 + (1 / z + 1 / x) / 2 ≤ 1 / x + 1 / y + 1 / z := by
        ring_nf
        <;>
        (try norm_num) <;>
        (try nlinarith) <;>
        (try
          {
            apply le_of_sub_nonneg
            ring_nf
            positivity
          })
      linarith
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_32 : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * Real.sqrt (y ^ 2 + z ^ 2) + y * Real.sqrt (x ^ 2 + z ^ 2) := by
  have h_main : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * Real.sqrt (y ^ 2 + z ^ 2) + y * Real.sqrt (x ^ 2 + z ^ 2) := by
    intro x y z
    have h₁ : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
    have h₂ : 0 ≤ Real.sqrt (y ^ 2 + z ^ 2) := by positivity
    have h₃ : 0 ≤ Real.sqrt (x ^ 2 + z ^ 2) := by positivity
    have h₄ : 0 ≤ Real.sqrt (y ^ 2 + z ^ 2) * Real.sqrt (x ^ 2 + z ^ 2) := by positivity
    nlinarith [Real.sq_sqrt (show 0 ≤ y ^ 2 + z ^ 2 by positivity),
      Real.sq_sqrt (show 0 ≤ x ^ 2 + z ^ 2 by positivity),
      sq_nonneg (x - Real.sqrt (y ^ 2 + z ^ 2)),
      sq_nonneg (y - Real.sqrt (x ^ 2 + z ^ 2)),
      sq_nonneg (Real.sqrt (y ^ 2 + z ^ 2) - Real.sqrt (x ^ 2 + z ^ 2)),
      sq_nonneg (x * Real.sqrt (y ^ 2 + z ^ 2) - y * Real.sqrt (x ^ 2 + z ^ 2)),
      sq_nonneg (x * Real.sqrt (x ^ 2 + z ^ 2) - y * Real.sqrt (y ^ 2 + z ^ 2)),
      Real.sq_sqrt (show 0 ≤ y ^ 2 + z ^ 2 by positivity),
      Real.sq_sqrt (show 0 ≤ x ^ 2 + z ^ 2 by positivity),
      sq_nonneg (x - y),
      sq_nonneg (Real.sqrt (y ^ 2 + z ^ 2) - Real.sqrt (x ^ 2 + z ^ 2)),
      sq_nonneg (Real.sqrt (x ^ 2 + z ^ 2) - Real.sqrt (y ^ 2 + z ^ 2))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_33 : ∀ (x y : ℝ), x ^ 4 + y ^ 4 + 8 ≥ 8 * x * y := by
  intro x y
  have h_main : x ^ 4 + y ^ 4 + 8 ≥ 8 * x * y := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 2), sq_nonneg (x + y), sq_nonneg (x - y),
      sq_nonneg (x * y - 2), sq_nonneg (x ^ 2 - 2 * x * y + y ^ 2), sq_nonneg (x ^ 2 + 2 * x * y + y ^ 2),
      sq_nonneg (x ^ 2 - 4 * x * y + y ^ 2), sq_nonneg (x ^ 2 + 4 * x * y + y ^ 2), sq_nonneg (2 * x ^ 2 - 2 * y ^ 2),
      sq_nonneg (2 * x ^ 2 + 2 * y ^ 2), sq_nonneg (x ^ 2 - 3 * x * y + y ^ 2), sq_nonneg (x ^ 2 + 3 * x * y + y ^ 2),
      sq_nonneg (3 * x ^ 2 - 4 * x * y + y ^ 2), sq_nonneg (3 * x ^ 2 + 4 * x * y + y ^ 2)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_35 : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → a / b + b / c + c / d + d / a ≥ 4 := by
  intro a b c d h
  have h₁ : a / b + b / c ≥ 2 * Real.sqrt (a / c) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < c := by linarith
    have h₁₄ : 0 < a / b := by positivity
    have h₁₅ : 0 < b / c := by positivity
    have h₁₆ : 0 < a / c := by positivity
    have h₁₇ : 0 < a / b * (b / c) := by positivity
    have h₁₈ : a / b * (b / c) = a / c := by
      calc
        a / b * (b / c) = (a / b) * (b / c) := by ring
        _ = a / c := by field_simp <;> ring
        _ = a / c := by ring
    have h₁₉ : a / b + b / c ≥ 2 * Real.sqrt (a / c) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ a / c by positivity), sq_nonneg (a / b - b / c), sq_nonneg (a / b - Real.sqrt (a / c)), sq_nonneg (b / c - Real.sqrt (a / c))]
    exact h₁₉
  
  have h₂ : c / d + d / a ≥ 2 * Real.sqrt (c / a) := by
    have h₂₁ : 0 < c := by linarith
    have h₂₂ : 0 < d := by linarith
    have h₂₃ : 0 < a := by linarith
    have h₂₄ : 0 < c / d := by positivity
    have h₂₅ : 0 < d / a := by positivity
    have h₂₆ : 0 < c / a := by positivity
    have h₂₇ : 0 < c / d * (d / a) := by positivity
    have h₂₈ : c / d * (d / a) = c / a := by
      calc
        c / d * (d / a) = (c / d) * (d / a) := by ring
        _ = c / a := by field_simp <;> ring
        _ = c / a := by ring
    have h₂₉ : c / d + d / a ≥ 2 * Real.sqrt (c / a) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ c / a by positivity), sq_nonneg (c / d - d / a), sq_nonneg (c / d - Real.sqrt (c / a)), sq_nonneg (d / a - Real.sqrt (c / a))]
    exact h₂₉
  
  have h₃ : a / b + b / c + c / d + d / a ≥ 2 * Real.sqrt (a / c) + 2 * Real.sqrt (c / a) := by
    linarith [h₁, h₂]
  
  have h₄ : Real.sqrt (a / c) + Real.sqrt (c / a) ≥ 2 := by
    have h₄₁ : 0 < a := by linarith
    have h₄₂ : 0 < c := by linarith
    have h₄₃ : 0 < a / c := by positivity
    have h₄₄ : 0 < c / a := by positivity
    have h₄₅ : Real.sqrt (a / c) > 0 := by positivity
    have h₄₆ : Real.sqrt (c / a) > 0 := by positivity
    have h₄₇ : Real.sqrt (a / c) * Real.sqrt (c / a) = 1 := by
      have h₄₇₁ : Real.sqrt (a / c) * Real.sqrt (c / a) = Real.sqrt ((a / c) * (c / a)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h₄₇₁]
      have h₄₇₂ : (a / c : ℝ) * (c / a) = 1 := by
        field_simp
        <;> ring_nf
        <;> linarith
      rw [h₄₇₂]
      <;> simp [Real.sqrt_one]
    nlinarith [sq_nonneg (Real.sqrt (a / c) - Real.sqrt (c / a)), h₄₇]
  
  have h₅ : 2 * Real.sqrt (a / c) + 2 * Real.sqrt (c / a) ≥ 4 := by
    have h₅₁ : Real.sqrt (a / c) + Real.sqrt (c / a) ≥ 2 := h₄
    linarith
  
  have h₆ : a / b + b / c + c / d + d / a ≥ 4 := by
    linarith [h₃, h₅]
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_39 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ (1 + a) * (1 + b) * (1 + c) = 8 → a * b * c ≤ 1 := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : (1 + a) * (1 + b) * (1 + c) = 8 := by linarith
  have h₅ : a * b * c ≤ 1 := by
    have h₅₁ : 0 < a * b := by positivity
    have h₅₂ : 0 < a * b * c := by positivity
    have h₅₃ : 0 < a * b * c * (a * b) := by positivity
    -- Use non-linear arithmetic to prove the inequality
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a * b * c - 1)]
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_41 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c) := by
  intro a b c h
  have h_main : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg h.1 h.2.1, mul_nonneg h.2.1 h.2.2, mul_nonneg h.1 h.2.2,
      mul_nonneg (sq_nonneg (a - b)) h.2.2, mul_nonneg (sq_nonneg (b - c)) h.1,
      mul_nonneg (sq_nonneg (c - a)) h.2.1, mul_nonneg (sq_nonneg (a * b - b * c)) h.2.2,
      mul_nonneg (sq_nonneg (b * c - c * a)) h.1, mul_nonneg (sq_nonneg (c * a - a * b)) h.2.1]
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_42 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
  intro a b c h
  have h₁ : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≥ 3 * a * b * c := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < c := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < c * a := by positivity
    have h₈ : 0 < a * b * c := by positivity
    have h₉ : 0 < a ^ 2 * b := by positivity
    have h₁₀ : 0 < b ^ 2 * c := by positivity
    have h₁₁ : 0 < c ^ 2 * a := by positivity
    have h₁₂ : 0 < a * b * c * a := by positivity
    have h₁₃ : 0 < a * b * c * b := by positivity
    have h₁₄ : 0 < a * b * c * c := by positivity
    -- Use nlinarith to prove the inequality using AM-GM
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_pos h₂ h₃, mul_pos h₃ h₄, mul_pos h₄ h₂,
      mul_pos (mul_pos h₂ h₃) h₄, mul_pos (mul_pos h₃ h₄) h₂, mul_pos (mul_pos h₄ h₂) h₃]
  
  have h₂ : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≥ 3 * a * b * c := by
    have h₃ : 0 < a := by linarith
    have h₄ : 0 < b := by linarith
    have h₅ : 0 < c := by linarith
    have h₆ : 0 < a * b := by positivity
    have h₇ : 0 < b * c := by positivity
    have h₈ : 0 < c * a := by positivity
    have h₉ : 0 < a * b * c := by positivity
    have h₁₀ : 0 < a * b ^ 2 := by positivity
    have h₁₁ : 0 < b * c ^ 2 := by positivity
    have h₁₂ : 0 < c * a ^ 2 := by positivity
    have h₁₃ : 0 < a * b * c * a := by positivity
    have h₁₄ : 0 < a * b * c * b := by positivity
    have h₁₅ : 0 < a * b * c * c := by positivity
    -- Use nlinarith to prove the inequality using AM-GM
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_pos h₃ h₄, mul_pos h₄ h₅, mul_pos h₅ h₃,
      mul_pos (mul_pos h₃ h₄) h₅, mul_pos (mul_pos h₄ h₅) h₃, mul_pos (mul_pos h₅ h₃) h₄]
  
  have h₃ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ (3 * a * b * c) * (3 * a * b * c) := by
    have h₄ : 0 < a := by linarith
    have h₅ : 0 < b := by linarith
    have h₆ : 0 < c := by linarith
    have h₇ : 0 < a * b := by positivity
    have h₈ : 0 < b * c := by positivity
    have h₉ : 0 < c * a := by positivity
    have h₁₀ : 0 < a * b * c := by positivity
    have h₁₁ : 0 < a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by positivity
    have h₁₂ : 0 < a * b ^ 2 + b * c ^ 2 + c * a ^ 2 := by positivity
    -- Use the fact that both factors are positive to multiply the inequalities
    have h₁₃ : 0 < (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by positivity
    have h₁₄ : 0 < (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) := by positivity
    have h₁₅ : 0 < (3 * a * b * c) := by positivity
    -- Use the fact that the product of the inequalities is the desired result
    have h₁₆ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ (3 * a * b * c) * (3 * a * b * c) := by
      nlinarith [h₁, h₂, mul_nonneg (le_of_lt h₁₁) (le_of_lt h₁₂),
        mul_nonneg (le_of_lt h₁₅) (le_of_lt h₁₅)]
    exact h₁₆
  
  have h₄ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
    have h₅ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ (3 * a * b * c) * (3 * a * b * c) := h₃
    have h₆ : (3 * a * b * c) * (3 * a * b * c) = 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
      ring
    linarith
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_50 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h₁ : a > 0 := by exact h.1
  have h₂ : b > 0 := by exact h.2.1
  have h₃ : c > 0 := by exact h.2.2
  have h₄ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    have h₄₁ : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    have h₄₂ : 0 ≤ a + b := by linarith
    have h₄₃ : 0 ≤ (a + b) * (a - b) ^ 2 := by positivity
    have h₄₄ : a ^ 3 + b ^ 3 - a * b * (a + b) = (a + b) * (a - b) ^ 2 := by
      ring_nf
      <;> nlinarith
    nlinarith
  
  have h₅ : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
    have h₅₁ : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
    have h₅₂ : 0 ≤ b + c := by linarith
    have h₅₃ : 0 ≤ (b + c) * (b - c) ^ 2 := by positivity
    have h₅₄ : b ^ 3 + c ^ 3 - b * c * (b + c) = (b + c) * (b - c) ^ 2 := by
      ring_nf
      <;> nlinarith
    nlinarith
  
  have h₆ : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := by
    have h₆₁ : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
    have h₆₂ : 0 ≤ c + a := by linarith
    have h₆₃ : 0 ≤ (c + a) * (c - a) ^ 2 := by positivity
    have h₆₄ : c ^ 3 + a ^ 3 - c * a * (c + a) = (c + a) * (c - a) ^ 2 := by
      ring_nf
      <;> nlinarith
    nlinarith
  
  have h₇ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    nlinarith [h₄]
  
  have h₈ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    nlinarith [h₅]
  
  have h₉ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    nlinarith [h₆]
  
  have h₁₀ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₁₀₁ : 0 < a * b * (a + b + c) := by positivity
    have h₁₀₂ : 0 < a ^ 3 + b ^ 3 + a * b * c := by
      nlinarith [pow_pos h₁ 3, pow_pos h₂ 3, mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃]
    have h₁₀₃ : a * b * (a + b + c) ≤ a ^ 3 + b ^ 3 + a * b * c := by
      nlinarith [h₇]
    exact one_div_le_one_div_of_le (by positivity) h₁₀₃
  
  have h₁₁ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₁₁₁ : 0 < b * c * (a + b + c) := by positivity
    have h₁₁₂ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₁₁₃ : b * c * (a + b + c) ≤ b ^ 3 + c ^ 3 + a * b * c := by
      nlinarith [h₈]
    exact one_div_le_one_div_of_le (by positivity) h₁₁₃
  
  have h₁₂ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    have h₁₂₁ : 0 < c * a * (a + b + c) := by positivity
    have h₁₂₂ : 0 < c ^ 3 + a ^ 3 + a * b * c := by positivity
    have h₁₂₃ : c * a * (a + b + c) ≤ c ^ 3 + a ^ 3 + a * b * c := by
      nlinarith [h₉]
    exact one_div_le_one_div_of_le (by positivity) h₁₂₃
  
  have h₁₃ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
    linarith [h₁₀, h₁₁, h₁₂]
  
  have h₁₄ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    have h₁₄₁ : 0 < a * b * c := by positivity
    have h₁₄₂ : 0 < a * b * (a + b + c) := by positivity
    have h₁₄₃ : 0 < b * c * (a + b + c) := by positivity
    have h₁₄₄ : 0 < c * a * (a + b + c) := by positivity
    have h₁₄₅ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = (a + b + c) / (a * b * c * (a + b + c)) := by
      have h₁₄₅₁ : 1 / (a * b * (a + b + c)) = c / (a * b * c * (a + b + c)) := by
        field_simp
        <;> ring
        <;> field_simp
        <;> ring
      have h₁₄₅₂ : 1 / (b * c * (a + b + c)) = a / (a * b * c * (a + b + c)) := by
        field_simp
        <;> ring
        <;> field_simp
        <;> ring
      have h₁₄₅₃ : 1 / (c * a * (a + b + c)) = b / (a * b * c * (a + b + c)) := by
        field_simp
        <;> ring
        <;> field_simp
        <;> ring
      rw [h₁₄₅₁, h₁₄₅₂, h₁₄₅₃]
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    have h₁₄₆ : (a + b + c) / (a * b * c * (a + b + c)) = 1 / (a * b * c) := by
      have h₁₄₆₁ : a + b + c > 0 := by positivity
      have h₁₄₆₂ : a * b * c > 0 := by positivity
      have h₁₄₆₃ : a * b * c * (a + b + c) > 0 := by positivity
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h₁₄₅, h₁₄₆]
    <;> ring
  
  have h₁₅ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    calc
      1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
        exact h₁₃
      _ = 1 / (a * b * c) := by
        rw [h₁₄]
      _ ≤ 1 / (a * b * c) := by
        linarith
  
  exact h₁₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_53 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) ≥ 3 / 4 := by
  intro a b c h
  have h_main : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) ≥ 3 / 4 := by
    rcases h with ⟨ha, hb, hc, h⟩
    have h₁ : 0 < a * b := by positivity
    have h₂ : 0 < a * c := by positivity
    have h₃ : 0 < b * c := by positivity
    field_simp [ha.ne', hb.ne', hc.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (b - 1)),
      mul_nonneg (sq_nonneg (b - 1)) (sq_nonneg (c - 1)),
      mul_nonneg (sq_nonneg (c - 1)) (sq_nonneg (a - 1)),
      mul_le_mul_of_nonneg_right (sq_nonneg (a - 1)) (le_of_lt hb),
      mul_le_mul_of_nonneg_right (sq_nonneg (b - 1)) (le_of_lt hc),
      mul_le_mul_of_nonneg_right (sq_nonneg (c - 1)) (le_of_lt ha),
      mul_le_mul_of_nonneg_left (sq_nonneg (a - 1)) (le_of_lt hc),
      mul_le_mul_of_nonneg_left (sq_nonneg (b - 1)) (le_of_lt ha),
      mul_le_mul_of_nonneg_left (sq_nonneg (c - 1)) (le_of_lt hb)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_54 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 → a * b * c ≥ 8 := by
  intro a b c h
  have h_main : a * b * c ≥ 8 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < a * c := by positivity
    have h₇ : 0 < b * c := by positivity
    have h₈ : 0 < a * b * c := by positivity
    field_simp [h₁, h₂, h₃, add_comm] at h₄
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃,
      sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c),
      sq_nonneg (a * c - b * c),
      mul_pos (mul_pos h₁ h₂) h₃,
      mul_pos (mul_pos h₁ h₃) h₂,
      mul_pos (mul_pos h₂ h₃) h₁]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_55 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 2 * a * b / (a + b) + 2 * b * c / (b + c) + 2 * c * a / (c + a) ≤ a + b + c := by
  have h_main : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 2 * a * b / (a + b) + 2 * b * c / (b + c) + 2 * c * a / (c + a) ≤ a + b + c := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 2 * a * b / (a + b) ≤ (a + b) / 2 := by
      -- Prove that 2 * a * b / (a + b) ≤ (a + b) / 2
      have h₁ : 0 < a + b := by linarith
      have h₂ : 0 < a * b := by positivity
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    have h₂ : 2 * b * c / (b + c) ≤ (b + c) / 2 := by
      -- Prove that 2 * b * c / (b + c) ≤ (b + c) / 2
      have h₁ : 0 < b + c := by linarith
      have h₂ : 0 < b * c := by positivity
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
    have h₃ : 2 * c * a / (c + a) ≤ (c + a) / 2 := by
      -- Prove that 2 * c * a / (c + a) ≤ (c + a) / 2
      have h₁ : 0 < c + a := by linarith
      have h₂ : 0 < c * a := by positivity
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
    -- Sum the inequalities to get the final result
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_57 : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → (x + y + z) ^ 2 / 3 ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
  intro x y z h
  have h_main : (x + y + z) ^ 2 / 3 ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
    have h₁ : x ≥ 0 := h.1
    have h₂ : y ≥ 0 := h.2.1
    have h₃ : z ≥ 0 := h.2.2
    have h₄ : 0 ≤ x * y := by positivity
    have h₅ : 0 ≤ y * z := by positivity
    have h₆ : 0 ≤ z * x := by positivity
    have h₇ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (y - z), sq_nonneg (y + z)]
    have h₈ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (z - x), sq_nonneg (z + x)]
    have h₉ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    have h₁₀ : x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) ≤ x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) := by
      nlinarith [h₇, h₈, h₉, mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁]
    have h₁₁ : x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) ≤ (x + y + z) ^ 2 / 3 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z),
        sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y)]
    nlinarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_58 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x ^ 4 + y ^ 4 + z ^ 2 ≥ Real.sqrt 8 * x * y * z := by
  intro x y z h
  have h₁ : x > 0 := by linarith
  have h₂ : y > 0 := by linarith
  have h₃ : z > 0 := by linarith
  have h₄ : x ^ 4 + y ^ 4 ≥ 2 * x ^ 2 * y ^ 2 := by
    have h₄₁ : 0 ≤ (x ^ 2 - y ^ 2) ^ 2 := by positivity
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  
  have h₅ : x ^ 4 + y ^ 4 + z ^ 2 ≥ 2 * x ^ 2 * y ^ 2 + z ^ 2 := by
    linarith
  
  have h₆ : 4 * x ^ 4 * y ^ 4 + z ^ 4 ≥ 4 * x ^ 2 * y ^ 2 * z ^ 2 := by
    have h₆₁ : 0 ≤ (2 * x ^ 2 * y ^ 2 - z ^ 2) ^ 2 := by positivity
    have h₆₂ : (2 * x ^ 2 * y ^ 2 - z ^ 2) ^ 2 ≥ 0 := by linarith
    nlinarith [sq_nonneg (2 * x ^ 2 * y ^ 2 - z ^ 2)]
  
  have h₇ : (2 * x ^ 2 * y ^ 2 + z ^ 2) ^ 2 ≥ 8 * x ^ 2 * y ^ 2 * z ^ 2 := by
    have h₇₁ : (2 * x ^ 2 * y ^ 2 + z ^ 2) ^ 2 = 4 * x ^ 4 * y ^ 4 + z ^ 4 + 4 * x ^ 2 * y ^ 2 * z ^ 2 := by
      ring
    rw [h₇₁]
    nlinarith [h₆]
  
  have h₈ : (x ^ 4 + y ^ 4 + z ^ 2) ^ 2 ≥ 8 * x ^ 2 * y ^ 2 * z ^ 2 := by
    have h₈₁ : (x ^ 4 + y ^ 4 + z ^ 2) ^ 2 ≥ (2 * x ^ 2 * y ^ 2 + z ^ 2) ^ 2 := by
      have h₈₂ : x ^ 4 + y ^ 4 + z ^ 2 ≥ 2 * x ^ 2 * y ^ 2 + z ^ 2 := by linarith
      have h₈₃ : 2 * x ^ 2 * y ^ 2 + z ^ 2 ≥ 0 := by positivity
      have h₈₄ : x ^ 4 + y ^ 4 + z ^ 2 ≥ 0 := by positivity
      nlinarith [sq_nonneg (x ^ 4 + y ^ 4 + z ^ 2 - (2 * x ^ 2 * y ^ 2 + z ^ 2))]
    nlinarith [h₇]
  
  have h₉ : x ^ 4 + y ^ 4 + z ^ 2 ≥ Real.sqrt 8 * x * y * z := by
    have h₉₁ : 0 < Real.sqrt 8 := by positivity
    have h₉₂ : 0 < x * y * z := by positivity
    have h₉₃ : 0 < x * y := by positivity
    have h₉₄ : 0 < x * y * z := by positivity
    have h₉₅ : (Real.sqrt 8 * x * y * z) ^ 2 = 8 * x ^ 2 * y ^ 2 * z ^ 2 := by
      have h₉₅₁ : (Real.sqrt 8 * x * y * z) ^ 2 = (Real.sqrt 8) ^ 2 * (x * y * z) ^ 2 := by ring
      rw [h₉₅₁]
      have h₉₅₂ : (Real.sqrt 8) ^ 2 = 8 := by
        rw [Real.sq_sqrt (by positivity)]
      rw [h₉₅₂]
      <;> ring_nf
      <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
      <;> ring_nf
    have h₉₆ : (x ^ 4 + y ^ 4 + z ^ 2) ^ 2 ≥ (Real.sqrt 8 * x * y * z) ^ 2 := by
      rw [h₉₅]
      exact h₈
    have h₉₇ : x ^ 4 + y ^ 4 + z ^ 2 ≥ 0 := by positivity
    have h₉₈ : Real.sqrt 8 * x * y * z ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show 0 ≤ 8 by norm_num)]
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_60 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
  intro a b c h
  have h_main : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h.1.le (sq_nonneg (a - b)), mul_nonneg h.2.1.le (sq_nonneg (b - c)),
      mul_nonneg h.2.2.le (sq_nonneg (c - a)),
      mul_nonneg h.1.le (sq_nonneg (a - c)), mul_nonneg h.2.1.le (sq_nonneg (b - a)),
      mul_nonneg h.2.2.le (sq_nonneg (c - b)), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2, mul_pos h.2.2 h.1,
      sq_nonneg (a + b - 2 * c), sq_nonneg (b + c - 2 * a), sq_nonneg (c + a - 2 * b)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_61 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → a ^ 3 + b ^ 3 + c ^ 3 + (a * b) ^ 3 + (b * c) ^ 3 + (c * a) ^ 3 ≥ 2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
  intro a b c h
  have h_main : a ^ 3 + b ^ 3 + c ^ 3 + (a * b) ^ 3 + (b * c) ^ 3 + (c * a) ^ 3 ≥ 2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (b - 1)),
      mul_nonneg (sq_nonneg (b - 1)) (sq_nonneg (c - 1)), mul_nonneg (sq_nonneg (c - 1)) (sq_nonneg (a - 1)),
      mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2.1, mul_pos h.2.2.1 h.1, sq_nonneg (a * b - 1), sq_nonneg (b * c - 1),
      sq_nonneg (c * a - 1), mul_nonneg (sq_nonneg (a * b - 1)) (sq_nonneg (b * c - 1)),
      mul_nonneg (sq_nonneg (b * c - 1)) (sq_nonneg (c * a - 1)), mul_nonneg (sq_nonneg (c * a - 1)) (sq_nonneg (a * b - 1))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_62 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ b / a + c / b + a / c := by
  intro a b c h
  have h_main : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ b / a + c / b + a / c := by
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
    nlinarith [sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c),
      sq_nonneg (a ^ 2 * c - a * b * c), sq_nonneg (b ^ 2 * a - a * b * c), sq_nonneg (c ^ 2 * b - a * b * c),
      mul_nonneg (sq_nonneg (a * c - b * a)) (sq_nonneg (b * a - c * b)),
      mul_nonneg (sq_nonneg (b * a - c * b)) (sq_nonneg (c * b - a * c)),
      mul_nonneg (sq_nonneg (c * b - a * c)) (sq_nonneg (a * c - b * a)),
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

theorem radmila_exercise_1_63 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c) := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b * c := by positivity
  have h₅ : 0 < a * b := by positivity
  have h₆ : 0 < a * c := by positivity
  have h₇ : 0 < b * c := by positivity
  have h_main : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2 ≥ a * b * c * (a + b + c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - a * c), sq_nonneg (a * c - a * b),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₁ h₃, sq_nonneg (a - b), sq_nonneg (b - c),
      sq_nonneg (c - a)]
  
  have h_final : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c) := by
    have h₈ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 = (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      have h₈₁ : 1 / a ^ 2 = b ^ 2 * c ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) := by
        field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
      have h₈₂ : 1 / b ^ 2 = a ^ 2 * c ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) := by
        field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
      have h₈₃ : 1 / c ^ 2 = a ^ 2 * b ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) := by
        field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
      have h₈₄ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 = b ^ 2 * c ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) + a ^ 2 * c ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) + a ^ 2 * b ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) := by
        rw [h₈₁, h₈₂, h₈₃]
      rw [h₈₄]
      have h₈₅ : b ^ 2 * c ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) + a ^ 2 * c ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) + a ^ 2 * b ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) = (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) / (a ^ 2 * b ^ 2 * c ^ 2) := by
        field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
        <;> ring
      rw [h₈₅]
    rw [h₈]
    have h₉ : (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) / (a ^ 2 * b ^ 2 * c ^ 2) ≥ (a + b + c) / (a * b * c) := by
      have h₉₁ : (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) ≥ a * b * c * (a + b + c) := by
        linarith
      have h₉₂ : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by positivity
      have h₉₃ : 0 < a * b * c := by positivity
      have h₉₄ : (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) / (a ^ 2 * b ^ 2 * c ^ 2) ≥ (a + b + c) / (a * b * c) := by
        rw [ge_iff_le]
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [h_main, mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₁ h₃,
          mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₁ h₃),
          mul_pos (mul_pos h₁ h₃) (mul_pos h₁ h₂)]
      exact h₉₄
    linarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_69 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → a * b + b * c + c * a ≤ 1 / 3 := by
  have h_main : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → a * b + b * c + c * a ≤ 1 / 3 := by
    intro a b c h
    have h₁ : a + b + c = 1 := h.2.2.2
    have h₂ : a * b + b * c + c * a ≤ 1 / 3 := by
      have h₃ : (a + b + c) ^ 2 = 1 := by
        rw [h₁]
        <;> ring
      have h₄ : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) = 1 := by
        nlinarith
      have h₅ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    exact h₂
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_73_1 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) < 5 := by
  intro a b c h
  have h₁ : ∀ (x : ℝ), x > 0 → Real.sqrt (4 * x + 1) < 2 * x + 1 := by
    intro x hx
    have h₂ : 0 < x := hx
    have h₃ : 0 < 2 * x + 1 := by linarith
    have h₄ : 0 < 4 * x + 1 := by linarith
    have h₅ : 0 < Real.sqrt (4 * x + 1) := Real.sqrt_pos.mpr (by linarith)
    have h₆ : Real.sqrt (4 * x + 1) < 2 * x + 1 := by
      have h₇ : Real.sqrt (4 * x + 1) < 2 * x + 1 := by
        have h₈ : (2 * x + 1 : ℝ) > 0 := by linarith
        have h₉ : (Real.sqrt (4 * x + 1)) ^ 2 = 4 * x + 1 := by
          rw [Real.sq_sqrt] <;> linarith
        nlinarith [sq_nonneg (2 * x + 1 - Real.sqrt (4 * x + 1))]
      exact h₇
    exact h₆
  have h₂ : Real.sqrt (4 * a + 1) < 2 * a + 1 := by
    have h₃ : a > 0 := h.1
    have h₄ : Real.sqrt (4 * a + 1) < 2 * a + 1 := h₁ a h₃
    exact h₄
  have h₃ : Real.sqrt (4 * b + 1) < 2 * b + 1 := by
    have h₄ : b > 0 := h.2.1
    have h₅ : Real.sqrt (4 * b + 1) < 2 * b + 1 := h₁ b h₄
    exact h₅
  have h₄ : Real.sqrt (4 * c + 1) < 2 * c + 1 := by
    have h₅ : c > 0 := h.2.2.1
    have h₆ : Real.sqrt (4 * c + 1) < 2 * c + 1 := h₁ c h₅
    exact h₆
  have h₅ : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) < 5 := by
    have h₆ : a + b + c = 1 := h.2.2.2
    linarith
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_73_2 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) ≤ Real.sqrt 21 := by
  intro a b c h
  have h₁ : 0 ≤ Real.sqrt (4 * a + 1) := by
    apply Real.sqrt_nonneg

  have h₂ : 0 ≤ Real.sqrt (4 * b + 1) := by
    apply Real.sqrt_nonneg

  have h₃ : 0 ≤ Real.sqrt (4 * c + 1) := by
    apply Real.sqrt_nonneg

  have h₄ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ^ 2 ≤ 21 := by
    have h₅ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ^ 2 ≤ 3 * ((Real.sqrt (4 * a + 1)) ^ 2 + (Real.sqrt (4 * b + 1)) ^ 2 + (Real.sqrt (4 * c + 1)) ^ 2) := by
      nlinarith [sq_nonneg (Real.sqrt (4 * a + 1) - Real.sqrt (4 * b + 1)), sq_nonneg (Real.sqrt (4 * b + 1) - Real.sqrt (4 * c + 1)), sq_nonneg (Real.sqrt (4 * c + 1) - Real.sqrt (4 * a + 1))]
    have h₆ : (Real.sqrt (4 * a + 1)) ^ 2 + (Real.sqrt (4 * b + 1)) ^ 2 + (Real.sqrt (4 * c + 1)) ^ 2 = (4 * a + 1) + (4 * b + 1) + (4 * c + 1) := by
      have h₇ : (Real.sqrt (4 * a + 1)) ^ 2 = 4 * a + 1 := by
        rw [Real.sq_sqrt] <;> linarith
      have h₈ : (Real.sqrt (4 * b + 1)) ^ 2 = 4 * b + 1 := by
        rw [Real.sq_sqrt] <;> linarith
      have h₉ : (Real.sqrt (4 * c + 1)) ^ 2 = 4 * c + 1 := by
        rw [Real.sq_sqrt] <;> linarith
      linarith
    have h₇ : (Real.sqrt (4 * a + 1)) ^ 2 + (Real.sqrt (4 * b + 1)) ^ 2 + (Real.sqrt (4 * c + 1)) ^ 2 = 7 := by
      rw [h₆]
      linarith
    nlinarith

  have h₅ : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) ≤ Real.sqrt 21 := by
    have h₆ : 0 ≤ Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) := by
      linarith
    have h₇ : 0 ≤ Real.sqrt 21 := Real.sqrt_nonneg 21
    have h₈ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ^ 2 ≤ 21 := h₄
    have h₉ : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) ≤ Real.sqrt 21 := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.sq_sqrt (show 0 ≤ 21 by norm_num)]
    exact h₉
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_5_8_1 : ∀ (a b : ℝ), a ≥ 0 ∧ b ≥ 0 → (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
  intro a b h
  have h_main : (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
    have h₁ : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    have h₄ : 0 ≤ a ^ 2 + b ^ 2 := by nlinarith
    have h₅ : 0 ≤ (a ^ 2 + b ^ 2) / 2 := by positivity
    have h₆ : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
      nlinarith [sq_nonneg (a - b)]
    have h₇ : (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    exact h₇
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_77_1 : ∀ (a b : ℝ), a > 0 ∧ b > 0 ∧ a + b = 1 → (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  intro a b h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : a + b = 1 := by linarith
  have h₄ : a * b ≤ 1 / 4 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
  have h₅ : 0 < a * b := by positivity
  have h₆ : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 = 5 - 2 * (a * b) + 1 / (a * b) ^ 2 - 2 / (a * b) := by
    have h₆₁ : (a + 1 / a) ^ 2 = a ^ 2 + 2 + 1 / a ^ 2 := by
      have h₆₁₁ : a ≠ 0 := by linarith
      field_simp [h₆₁₁]
      <;> ring_nf
      <;> field_simp [h₆₁₁]
      <;> ring_nf
      <;> nlinarith
    have h₆₂ : (b + 1 / b) ^ 2 = b ^ 2 + 2 + 1 / b ^ 2 := by
      have h₆₂₁ : b ≠ 0 := by linarith
      field_simp [h₆₂₁]
      <;> ring_nf
      <;> field_simp [h₆₂₁]
      <;> ring_nf
      <;> nlinarith
    have h₆₃ : a ^ 2 + b ^ 2 = 1 - 2 * (a * b) := by
      nlinarith
    have h₆₄ : 1 / a ^ 2 + 1 / b ^ 2 = (1 - 2 * (a * b)) / (a * b) ^ 2 := by
      have h₆₄₁ : a ≠ 0 := by linarith
      have h₆₄₂ : b ≠ 0 := by linarith
      have h₆₄₃ : a * b ≠ 0 := by positivity
      field_simp [h₆₄₁, h₆₄₂, h₆₄₃]
      <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
    calc
      (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 = (a ^ 2 + 2 + 1 / a ^ 2) + (b ^ 2 + 2 + 1 / b ^ 2) := by rw [h₆₁, h₆₂]
      _ = (a ^ 2 + b ^ 2) + (1 / a ^ 2 + 1 / b ^ 2) + 4 := by ring
      _ = (1 - 2 * (a * b)) + ((1 - 2 * (a * b)) / (a * b) ^ 2) + 4 := by rw [h₆₃, h₆₄]
      _ = 5 - 2 * (a * b) + 1 / (a * b) ^ 2 - 2 / (a * b) := by
        have h₆₅ : a * b ≠ 0 := by positivity
        field_simp [h₆₅]
        <;> ring_nf
        <;> field_simp [h₆₅]
        <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]
      _ = 5 - 2 * (a * b) + 1 / (a * b) ^ 2 - 2 / (a * b) := by rfl
  
  have h₇ : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
    rw [h₆]
    have h₈ : 0 < a * b := by positivity
    have h₉ : a * b ≤ 1 / 4 := by linarith
    have h₁₀ : 0 < (a * b) ^ 2 := by positivity
    have h₁₁ : 0 < (a * b) ^ 3 := by positivity
    have h₁₂ : 0 < (a * b) ^ 4 := by positivity
    have h₁₃ : 5 - 2 * (a * b) + 1 / (a * b) ^ 2 - 2 / (a * b) ≥ 25 / 2 := by
      have h₁₄ : 0 < a * b := by positivity
      have h₁₅ : a * b ≤ 1 / 4 := by linarith
      have h₁₆ : 0 < (a * b) ^ 2 := by positivity
      have h₁₇ : 0 < (a * b) ^ 3 := by positivity
      have h₁₈ : 0 < (a * b) ^ 4 := by positivity
      -- We need to show that 5 - 2 * (a * b) + 1 / (a * b) ^ 2 - 2 / (a * b) ≥ 25 / 2
      -- This can be transformed into a polynomial inequality in (a * b)
      have h₁₉ : (a * b) ^ 3 - (a * b) + 1 ≥ 0 := by
        nlinarith [sq_nonneg ((a * b) - 1 / 2), sq_nonneg ((a * b) + 1 / 2)]
      -- Using the above inequality, we can derive the desired result
      have h₂₀ : 0 < a * b := by positivity
      have h₂₁ : a * b ≤ 1 / 4 := by linarith
      field_simp [h₁₄.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((a * b) - 1 / 4), sq_nonneg ((a * b) + 1 / 4),
        sq_nonneg ((a * b) ^ 2 - 1 / 16), sq_nonneg ((a * b) ^ 2 + 1 / 16),
        sq_nonneg ((a * b) ^ 2 - (a * b) / 2), sq_nonneg ((a * b) ^ 2 + (a * b) / 2)]
    linarith
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_79 : ∀ (x y : ℝ), 0 ≤ x ∧ 0 ≤ y ∧ x ≤ 1 ∧ y ≤ 1 → 1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2) ≤ 2 / Real.sqrt (1 + x * y) := by
  have h_main : ∀ (x y : ℝ), 0 ≤ x ∧ 0 ≤ y ∧ x ≤ 1 ∧ y ≤ 1 → 1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2) ≤ 2 / Real.sqrt (1 + x * y) := by
    intro x y h
    have h₁ : 0 ≤ x := by linarith
    have h₂ : 0 ≤ y := by linarith
    have h₃ : x ≤ 1 := by linarith
    have h₄ : y ≤ 1 := by linarith
    have h₅ : 0 ≤ x * y := by positivity
    have h₆ : x * y ≤ 1 := by
      nlinarith
    have h₇ : 0 < Real.sqrt (1 + x ^ 2) := by
      apply Real.sqrt_pos_of_pos
      nlinarith
    have h₈ : 0 < Real.sqrt (1 + y ^ 2) := by
      apply Real.sqrt_pos_of_pos
      nlinarith
    have h₉ : 0 < Real.sqrt (1 + x * y) := by
      apply Real.sqrt_pos_of_pos
      nlinarith
    have h₁₀ : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by positivity
    have h₁₁ : Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) ≥ 1 + x * y := by
      have h₁₂ : Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) = Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) := by
        rw [Real.sqrt_mul] <;> nlinarith
      rw [h₁₂]
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1),
        sq_nonneg (x * y - x), sq_nonneg (x * y - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have h₁₂ : 1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2) ≤ 2 / Real.sqrt (1 + x * y) := by
      have h₁₃ : 1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2) ≤ 2 / Real.sqrt (1 + x * y) := by
        have h₁₄ : 0 < Real.sqrt (1 + x ^ 2) := by positivity
        have h₁₅ : 0 < Real.sqrt (1 + y ^ 2) := by positivity
        have h₁₆ : 0 < Real.sqrt (1 + x * y) := by positivity
        have h₁₇ : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by positivity
        field_simp
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt (1 + x ^ 2) - Real.sqrt (1 + y ^ 2)),
          Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity),
          Real.sq_sqrt (show 0 ≤ 1 + y ^ 2 by positivity),
          Real.sq_sqrt (show 0 ≤ 1 + x * y by positivity),
          sq_nonneg (x - y), mul_nonneg h₁ h₂, mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄),
          mul_nonneg (sub_nonneg.mpr h₆) (sub_nonneg.mpr h₆), mul_nonneg (sub_nonneg.mpr h₆) h₁,
          mul_nonneg (sub_nonneg.mpr h₆) h₂]
      linarith
    exact h₁₂
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_84 : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → x * (x - z) ^ 2 + y * (y - z) ^ 2 ≥ (x - z) * (y - z) * (x + y - z) := by
  intro x y z h
  have h₁ : x * (x - z) ^ 2 + y * (y - z) ^ 2 ≥ (x - z) * (y - z) * (x + y - z) := by
    have h₂ : 0 ≤ x := by linarith
    have h₃ : 0 ≤ y := by linarith
    have h₄ : 0 ≤ z := by linarith
    have h₅ : 0 ≤ x * y := by positivity
    have h₆ : 0 ≤ x * z := by positivity
    have h₇ : 0 ≤ y * z := by positivity
    -- Expand and simplify the inequality to prove it.
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      mul_nonneg h₂ (sq_nonneg (x - z)), mul_nonneg h₃ (sq_nonneg (y - z)),
      mul_nonneg h₂ (sq_nonneg (x - y)), mul_nonneg h₄ (sq_nonneg (x - y)),
      mul_nonneg h₄ (sq_nonneg (x - z)), mul_nonneg h₄ (sq_nonneg (y - z)),
      mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
      mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₄),
      mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₄),
      mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₂),
      mul_nonneg (sub_nonneg.mpr h₃) (sub_nonneg.mpr h₃),
      mul_nonneg (sub_nonneg.mpr h₄) (sub_nonneg.mpr h₄)]
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_85 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 ≥ 9 / (4 * (a + b + c)) := by
  intro a b c h
  have h_main : a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 ≥ 9 / (4 * (a + b + c)) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
      sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - b)),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)),
      mul_nonneg h₃.le (sq_nonneg (c - a)), mul_nonneg h₁.le (sq_nonneg (a - c)),
      mul_nonneg h₂.le (sq_nonneg (b - a)), mul_nonneg h₃.le (sq_nonneg (c - b)),
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

theorem radmila_exercise_1_86 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a * b + b * c + c * a > 0 := by
    nlinarith [mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
  
  have h₅ : a + b + c > 0 := by
    nlinarith [h₁, h₂, h₃]
  
  have h₆ : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
  
  have h₇ : a * b + b * c + c * a ≤ (a + b + c)^2 / 3 := by
    have h₇₁ : 3 * (a * b + b * c + c * a) ≤ (a + b + c)^2 := by linarith
    have h₇₂ : a * b + b * c + c * a ≤ (a + b + c)^2 / 3 := by
      linarith
    exact h₇₂
  
  have h₈ : (a + b + c) * (a * b + b * c + c * a) + 3 * (a + b + c) ≥ 6 * (a * b + b * c + c * a) := by
    by_cases h₈₁ : a + b + c ≥ 6
    · -- Case: a + b + c ≥ 6
      have h₈₂ : (a + b + c) * (a * b + b * c + c * a) - 6 * (a * b + b * c + c * a) ≥ 0 := by
        have h₈₃ : a * b + b * c + c * a > 0 := by positivity
        have h₈₄ : a + b + c - 6 ≥ 0 := by linarith
        have h₈₅ : (a * b + b * c + c * a) * (a + b + c - 6) ≥ 0 := by
          nlinarith
        nlinarith
      nlinarith
    · -- Case: a + b + c < 6
      have h₈₂ : a + b + c < 6 := by linarith
      have h₈₃ : a * b + b * c + c * a ≤ (a + b + c)^2 / 3 := by
        exact h₇
      have h₈₄ : (a + b + c) * (a * b + b * c + c * a) + 3 * (a + b + c) ≥ 6 * (a * b + b * c + c * a) := by
        have h₈₅ : (a + b + c) * (a * b + b * c + c * a) - 6 * (a * b + b * c + c * a) + 3 * (a + b + c) ≥ 0 := by
          nlinarith [sq_nonneg (a + b + c - 3), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
            mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
            mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁)]
        nlinarith
      exact h₈₄
  
  have h₉ : 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
    have h₉₁ : 0 < a * b + b * c + c * a := by positivity
    have h₉₂ : 0 < a + b + c := by positivity
    have h₉₃ : 0 < (a * b + b * c + c * a) * (a + b + c) := by positivity
    field_simp [h₉₁.ne', h₉₂.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [h₈, h₆, h₇, h₄, h₅, h₁, h₂, h₃, mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem lean_workbook_plus_239842 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
  have h₁ : 0 < a * b := by positivity
  have h₂ : 0 < b * c := by positivity
  have h₃ : 0 < c * a := by positivity
  have h₄ : 0 < a * b * c := by positivity
  have h₅ : 0 < a ^ 2 := by positivity
  have h₆ : 0 < b ^ 2 := by positivity
  have h₇ : 0 < c ^ 2 := by positivity
  have h₈ : 0 < a * b ^ 2 := by positivity
  have h₉ : 0 < b * c ^ 2 := by positivity
  have h₁₀ : 0 < c * a ^ 2 := by positivity
  have h₁₁ : 0 < a ^ 2 * b := by positivity
  have h₁₂ : 0 < b ^ 2 * c := by positivity
  have h₁₃ : 0 < c ^ 2 * a := by positivity
  have h₁₄ : 0 < a ^ 3 := by positivity
  have h₁₅ : 0 < b ^ 3 := by positivity
  have h₁₆ : 0 < c ^ 3 := by positivity
  have h₁₇ : (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
    have h₁₈ : 0 < a * b * c := by positivity
    field_simp [ha.ne', hb.ne', hc.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * (b + c) - b * (c + a)), sq_nonneg (b * (c + a) - c * (a + b)), sq_nonneg (c * (a + b) - a * (b + c)),
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      mul_nonneg ha.le hb.le, mul_nonneg hb.le hc.le, mul_nonneg hc.le ha.le,
      mul_nonneg (sq_nonneg (a - b)) h₁₀.le, mul_nonneg (sq_nonneg (b - c)) h₁₁.le, mul_nonneg (sq_nonneg (c - a)) h₁₂.le,
      mul_nonneg (sq_nonneg (a * b - b * c)) h₁₀.le, mul_nonneg (sq_nonneg (b * c - c * a)) h₁₁.le, mul_nonneg (sq_nonneg (c * a - a * b)) h₁₂.le]
  exact h₁₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_92 : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ |x * y + y * z + z * x| := by
  intro x y z
  have h_main : x ^ 2 + y ^ 2 + z ^ 2 ≥ |x * y + y * z + z * x| := by
    cases' le_total 0 (x * y + y * z + z * x) with h h <;>
    simp_all [abs_of_nonneg, abs_of_nonpos, le_refl]
    <;>
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z), sq_nonneg (x + y - z), sq_nonneg (x - y + z),
      sq_nonneg (-x + y + z), sq_nonneg (x - y - z), sq_nonneg (-x - y + z),
      sq_nonneg (-x + y - z), sq_nonneg (x + y + z - 2 * x),
      sq_nonneg (x + y + z - 2 * y), sq_nonneg (x + y + z - 2 * z)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_93 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ 1 / a + 1 / b + 1 / c := by
  intro a b c h
  have h_main : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ 1 / a + 1 / b + 1 / c := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < a * b * c := by positivity
    -- We need to show that (a^2 + b^2 + c^2) / (a * b * c) ≥ 1 / a + 1 / b + 1 / c
    -- Multiply both sides by (a * b * c) (which is positive) to simplify the inequality
    have h₈ : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ 1 / a + 1 / b + 1 / c := by
      -- Use the division inequality to rewrite the inequality
      field_simp [h₁.ne', h₂.ne', h₃.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to prove the inequality
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
        sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b)]
    exact h₈
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_94 : ∀ (x y z : ℝ), x < y ∧ y < z → (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0 := by
  intro x y z h
  have h₁ : x < y := by linarith
  have h₂ : y < z := by linarith
  have h_main : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0 := by
    have h₃ : z - x > 0 := by linarith
    have h₄ : x - y < 0 := by linarith
    have h₅ : y - z < 0 := by linarith
    have h₆ : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0 := by
      -- Use nlinarith to prove the inequality
      nlinarith [sq_pos_of_neg h₄, sq_pos_of_neg h₅, sq_pos_of_pos h₃, mul_pos h₃ (sq_pos_of_neg h₄),
        mul_pos h₃ (sq_pos_of_neg h₅), mul_pos (sq_pos_of_neg h₄) (sq_pos_of_neg h₅),
        mul_pos (sq_pos_of_neg h₄) h₃, mul_pos (sq_pos_of_neg h₅) h₃,
        mul_pos (sq_pos_of_neg h₄) h₃, mul_pos (sq_pos_of_neg h₅) h₃]
    exact h₆
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_96 : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → (x ^ 3 + y ^ 3 + z ^ 3) / 3 ≥ x * y * z + 3 / 4 * |(x - y) * (y - z) * (z - x)| := by
  intro x y z h
  have h₁ : (x ^ 3 + y ^ 3 + z ^ 3) / 3 ≥ x * y * z + 3 / 4 * |(x - y) * (y - z) * (z - x)| := by
    have h₂ : x ≥ 0 := by linarith
    have h₃ : y ≥ 0 := by linarith
    have h₄ : z ≥ 0 := by linarith
    -- Consider the cases based on the ordering of x, y, z
    cases' le_total x y with h₅ h₅ <;>
    cases' le_total y z with h₆ h₆ <;>
    cases' le_total z x with h₇ h₇ <;>
    simp_all [abs_mul, abs_of_nonneg, abs_of_nonpos, mul_assoc, mul_comm, mul_left_comm,
      sub_nonneg, sub_nonpos] <;>
    (try { contradiction }) <;>
    (try { nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y)] }) <;>
    (try
      {
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y),
          mul_nonneg h₂ h₃, mul_nonneg h₃ h₄, mul_nonneg h₄ h₂,
          mul_nonneg (sq_nonneg (x - y)) h₂, mul_nonneg (sq_nonneg (y - z)) h₃, mul_nonneg (sq_nonneg (z - x)) h₄,
          mul_nonneg (sq_nonneg (x - y)) h₃, mul_nonneg (sq_nonneg (y - z)) h₄, mul_nonneg (sq_nonneg (z - x)) h₂,
          mul_nonneg (sq_nonneg (x + y - 2 * z)) h₂, mul_nonneg (sq_nonneg (y + z - 2 * x)) h₃, mul_nonneg (sq_nonneg (z + x - 2 * y)) h₄]
      }) <;>
    (try
      {
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y),
          mul_nonneg h₂ h₃, mul_nonneg h₃ h₄, mul_nonneg h₄ h₂,
          mul_nonneg (sq_nonneg (x - y)) h₂, mul_nonneg (sq_nonneg (y - z)) h₃, mul_nonneg (sq_nonneg (z - x)) h₄,
          mul_nonneg (sq_nonneg (x - y)) h₃, mul_nonneg (sq_nonneg (y - z)) h₄, mul_nonneg (sq_nonneg (z - x)) h₂,
          mul_nonneg (sq_nonneg (x + y - 2 * z)) h₂, mul_nonneg (sq_nonneg (y + z - 2 * x)) h₃, mul_nonneg (sq_nonneg (z + x - 2 * y)) h₄]
      }) <;>
    (try
      {
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y),
          mul_nonneg h₂ h₃, mul_nonneg h₃ h₄, mul_nonneg h₄ h₂,
          mul_nonneg (sq_nonneg (x - y)) h₂, mul_nonneg (sq_nonneg (y - z)) h₃, mul_nonneg (sq_nonneg (z - x)) h₄,
          mul_nonneg (sq_nonneg (x - y)) h₃, mul_nonneg (sq_nonneg (y - z)) h₄, mul_nonneg (sq_nonneg (z - x)) h₂,
          mul_nonneg (sq_nonneg (x + y - 2 * z)) h₂, mul_nonneg (sq_nonneg (y + z - 2 * x)) h₃, mul_nonneg (sq_nonneg (z + x - 2 * y)) h₄]
      })
    <;>
    (try
      {
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y),
          mul_nonneg h₂ h₃, mul_nonneg h₃ h₄, mul_nonneg h₄ h₂,
          mul_nonneg (sq_nonneg (x - y)) h₂, mul_nonneg (sq_nonneg (y - z)) h₃, mul_nonneg (sq_nonneg (z - x)) h₄,
          mul_nonneg (sq_nonneg (x - y)) h₃, mul_nonneg (sq_nonneg (y - z)) h₄, mul_nonneg (sq_nonneg (z - x)) h₂,
          mul_nonneg (sq_nonneg (x + y - 2 * z)) h₂, mul_nonneg (sq_nonneg (y + z - 2 * x)) h₃, mul_nonneg (sq_nonneg (z + x - 2 * y)) h₄]
      })
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_helpful_inequality : ∀ (a b x y : ℝ), x > 0 ∧ y > 0 → a ^ 2 / x + b ^ 2 / y ≥ (a + b) ^ 2 / (x + y) := by
  have h_main : ∀ (a b x y : ℝ), x > 0 ∧ y > 0 → a ^ 2 / x + b ^ 2 / y ≥ (a + b) ^ 2 / (x + y) := by
    intro a b x y hxy
    have h₁ : 0 < x := hxy.1
    have h₂ : 0 < y := hxy.2
    have h₃ : 0 < x * y := mul_pos h₁ h₂
    have h₄ : 0 < x + y := by linarith
    field_simp [h₁.ne', h₂.ne', h₄.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a - b), sq_nonneg (x - y),
      mul_nonneg (sq_nonneg (a * y - b * x)) (sq_nonneg (x - y)),
      sq_nonneg (a * y + b * x), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (x + y)),
      mul_nonneg (sq_nonneg (a + b)) (sq_nonneg (x + y)), mul_nonneg (sq_nonneg (a * y - b * x)) (sq_nonneg (a + b)),
      mul_nonneg (sq_nonneg (a * x - b * y)) (sq_nonneg (a + b)), mul_nonneg (sq_nonneg (a * y + b * x)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a * x + b * y)) (sq_nonneg (a - b))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_6_6 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  intro a b c h
  have h_main : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a + c - b),
      sq_nonneg (b + c - a), mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_98 : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
  intro a b c d h
  have h₁ : 0 < a := by
    linarith [h.1]

  have h₂ : 0 < b := by
    linarith [h.2.1]

  have h₃ : 0 < c := by
    linarith [h.2.2.1]

  have h₄ : 0 < d := by
    linarith [h.2.2.2]

  have h₅ : 0 < a + b + c + d := by
    linarith [h₁, h₂, h₃, h₄]

  have h₆ : (1 : ℝ) / a + 1 / b + 4 / c + 16 / d = (1 : ℝ)^2 / a + (1 : ℝ)^2 / b + (2 : ℝ)^2 / c + (4 : ℝ)^2 / d := by
    have h₆₁ : (1 : ℝ) / a = (1 : ℝ)^2 / a := by
      field_simp [h₁.ne']
      <;> ring
    have h₆₂ : 1 / b = (1 : ℝ)^2 / b := by
      field_simp [h₂.ne']
      <;> ring
    have h₆₃ : 4 / c = (2 : ℝ)^2 / c := by
      field_simp [h₃.ne']
      <;> ring
    have h₆₄ : 16 / d = (4 : ℝ)^2 / d := by
      field_simp [h₄.ne']
      <;> ring
    rw [h₆₁, h₆₂, h₆₃, h₆₄]
    <;> ring

  have h₇ : (1 : ℝ)^2 / a + (1 : ℝ)^2 / b + (2 : ℝ)^2 / c + (4 : ℝ)^2 / d ≥ (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) := by
    have h₇₁ : 0 < a := h₁
    have h₇₂ : 0 < b := h₂
    have h₇₃ : 0 < c := h₃
    have h₇₄ : 0 < d := h₄
    have h₇₅ : 0 < a + b + c + d := h₅
    -- Use the Titu's lemma to prove the inequality
    have h₇₆ : (1 : ℝ)^2 / a + (1 : ℝ)^2 / b + (2 : ℝ)^2 / c + (4 : ℝ)^2 / d ≥ (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) := by
      -- Prove using the Titu's lemma
      have h₇₇ : (1 : ℝ)^2 / a + (1 : ℝ)^2 / b + (2 : ℝ)^2 / c + (4 : ℝ)^2 / d = (1 : ℝ)^2 / a + (1 : ℝ)^2 / b + (2 : ℝ)^2 / c + (4 : ℝ)^2 / d := rfl
      rw [h₇₇]
      have h₇₈ : (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) = (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) := rfl
      rw [h₇₈]
      -- Use the Titu's lemma
      have h₇₉ : (1 : ℝ)^2 / a + (1 : ℝ)^2 / b + (2 : ℝ)^2 / c + (4 : ℝ)^2 / d ≥ (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) := by
        -- Use the Titu's lemma
        have h₇₁₀ : 0 < a + b + c + d := by positivity
        -- Use the Titu's lemma
        have h₇₁₁ : (1 : ℝ)^2 / a + (2 : ℝ)^2 / c ≥ (1 + 2 : ℝ)^2 / (a + c) := by
          -- Prove using the Titu's lemma
          have h₇₁₂ : 0 < a + c := by positivity
          field_simp [h₇₁.ne', h₇₃.ne', h₇₁₂.ne']
          rw [div_le_div_iff (by positivity) (by positivity)]
          nlinarith [sq_nonneg (1 * c - 2 * a), sq_nonneg (1 * c + 2 * a)]
        have h₇₁₂ : (1 : ℝ)^2 / b + (4 : ℝ)^2 / d ≥ (1 + 4 : ℝ)^2 / (b + d) := by
          -- Prove using the Titu's lemma
          have h₇₁₃ : 0 < b + d := by positivity
          field_simp [h₇₂.ne', h₇₄.ne', h₇₁₃.ne']
          rw [div_le_div_iff (by positivity) (by positivity)]
          nlinarith [sq_nonneg (1 * d - 4 * b), sq_nonneg (1 * d + 4 * b)]
        have h₇₁₃ : (1 + 2 : ℝ)^2 / (a + c) + (1 + 4 : ℝ)^2 / (b + d) ≥ (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) := by
          -- Prove using the Titu's lemma
          have h₇₁₄ : 0 < a + c := by positivity
          have h₇₁₅ : 0 < b + d := by positivity
          have h₇₁₆ : 0 < (a + c) * (b + d) := by positivity
          have h₇₁₇ : 0 < a + b + c + d := by positivity
          field_simp [h₇₁₄.ne', h₇₁₅.ne', h₇₁₇.ne']
          rw [div_le_div_iff (by positivity) (by positivity)]
          nlinarith [sq_nonneg ((1 + 2 : ℝ) * (b + d) - (1 + 4 : ℝ) * (a + c)),
            sq_nonneg ((1 + 2 : ℝ) * (b + d) + (1 + 4 : ℝ) * (a + c))]
        -- Combine the inequalities
        linarith
      exact h₇₉
    exact h₇₆

  have h₈ : (1 + 1 + 2 + 4 : ℝ)^2 / (a + b + c + d) = (64 : ℝ) / (a + b + c + d) := by
    norm_num at h₇ ⊢
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try ring_nf at h₇ ⊢) <;>
    (try field_simp at h₇ ⊢) <;>
    (try nlinarith)

  have h₉ : (1 : ℝ) / a + 1 / b + 4 / c + 16 / d ≥ (64 : ℝ) / (a + b + c + d) := by
    linarith [h₆, h₇, h₈]

  have h₁₀ : 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
    linarith

  exact h₁₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_99 : ∀ (a b : ℝ), a > 0 ∧ b > 0 → 8 * (a ^ 4 + b ^ 4) ≥ (a + b) ^ 4 := by
  intro a b h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < a * b := by positivity
  have h₄ : 0 < a * b ^ 2 := by positivity
  have h₅ : 0 < a ^ 2 * b := by positivity
  have h₆ : 0 < a ^ 3 := by positivity
  have h₇ : 0 < b ^ 3 := by positivity
  have h₈ : 0 < a * b ^ 3 := by positivity
  have h₉ : 0 < a ^ 3 * b := by positivity
  have h_main : 8 * (a ^ 4 + b ^ 4) ≥ (a + b) ^ 4 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2 - 2 * a * b),
      sq_nonneg (a ^ 2 + b ^ 2 + 2 * a * b), sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b),
      sq_nonneg (a * b - b ^ 2), sq_nonneg (a * b - a ^ 2)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_100 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 9 / (x + y + z) := by
  intro x y z h
  have h_main : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 9 / (x + y + z) := by
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
      mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
      mul_nonneg (sq_nonneg (x - y)) h₃.le, mul_nonneg (sq_nonneg (y - z)) h₁.le,
      mul_nonneg (sq_nonneg (z - x)) h₂.le]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_101 : ∀ (a b x y z : ℝ), a > 0 ∧ b > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0 → x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
  intro a b x y z h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < x := by linarith
  have h₄ : 0 < y := by linarith
  have h₅ : 0 < z := by linarith
  have h₆ : 0 < a * y + b * z := by positivity
  have h₇ : 0 < a * z + b * x := by positivity
  have h₈ : 0 < a * x + b * y := by positivity
  have h₉ : 0 < a + b := by positivity
  have h₁₀ : 0 < x * y + y * z + z * x := by positivity
  have h₁₁ : (x + y + z)^2 ≥ 3 * (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h₁₂ : (x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y)) = (x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z)) := by
    have h₁₂₁ : x / (a * y + b * z) = x^2 / (a * x * y + b * x * z) := by
      have h₁₂₂ : a * x * y + b * x * z = x * (a * y + b * z) := by ring
      rw [h₁₂₂]
      have h₁₂₃ : x^2 / (x * (a * y + b * z)) = x / (a * y + b * z) := by
        have h₁₂₄ : x ≠ 0 := by linarith
        have h₁₂₅ : a * y + b * z ≠ 0 := by positivity
        field_simp [h₁₂₄, h₁₂₅]
        <;> ring
        <;> field_simp [h₁₂₄, h₁₂₅]
        <;> ring
      rw [h₁₂₃]
    have h₁₂₆ : y / (a * z + b * x) = y^2 / (a * y * z + b * x * y) := by
      have h₁₂₇ : a * y * z + b * x * y = y * (a * z + b * x) := by ring
      rw [h₁₂₇]
      have h₁₂₈ : y^2 / (y * (a * z + b * x)) = y / (a * z + b * x) := by
        have h₁₂₉ : y ≠ 0 := by linarith
        have h₁₃₀ : a * z + b * x ≠ 0 := by positivity
        field_simp [h₁₂₉, h₁₃₀]
        <;> ring
        <;> field_simp [h₁₂₉, h₁₃₀]
        <;> ring
      rw [h₁₂₈]
    have h₁₃₁ : z / (a * x + b * y) = z^2 / (a * x * z + b * y * z) := by
      have h₁₃₂ : a * x * z + b * y * z = z * (a * x + b * y) := by ring
      rw [h₁₃₂]
      have h₁₃₃ : z^2 / (z * (a * x + b * y)) = z / (a * x + b * y) := by
        have h₁₃₄ : z ≠ 0 := by linarith
        have h₁₃₅ : a * x + b * y ≠ 0 := by positivity
        field_simp [h₁₃₄, h₁₃₅]
        <;> ring
        <;> field_simp [h₁₃₄, h₁₃₅]
        <;> ring
      rw [h₁₃₃]
    rw [h₁₂₁, h₁₂₆, h₁₃₁]
    <;> ring
  
  have h₁₃ : x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z) ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by
    have h₁₃₁ : 0 < a * x * y + b * x * z := by positivity
    have h₁₃₂ : 0 < a * y * z + b * x * y := by positivity
    have h₁₃₃ : 0 < a * x * z + b * y * z := by positivity
    have h₁₃₄ : 0 < (a * x * y + b * x * z) * (a * y * z + b * x * y) := by positivity
    have h₁₃₅ : 0 < (a * x * y + b * x * z) * (a * x * z + b * y * z) := by positivity
    have h₁₃₆ : 0 < (a * y * z + b * x * y) * (a * x * z + b * y * z) := by positivity
    -- Use Titu's lemma to prove the inequality
    have h₁₃₇ : (x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z)) ≥ (x + y + z)^2 / ((a * x * y + b * x * z) + (a * y * z + b * x * y) + (a * x * z + b * y * z)) := by
      -- Apply Titu's lemma
      have h₁₃₈ : x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z) ≥ (x + y + z)^2 / ((a * x * y + b * x * z) + (a * y * z + b * x * y) + (a * x * z + b * y * z)) := by
        -- Use Titu's lemma (a special case of Cauchy-Schwarz)
        field_simp [h₁₃₁, h₁₃₂, h₁₃₃]
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x * (a * y * z + b * x * y) - y * (a * x * y + b * x * z)), sq_nonneg (y * (a * x * z + b * y * z) - z * (a * y * z + b * x * y)), sq_nonneg (z * (a * x * y + b * x * z) - x * (a * x * z + b * y * z))]
      linarith
    have h₁₃₈ : (a * x * y + b * x * z) + (a * y * z + b * x * y) + (a * x * z + b * y * z) = (a + b) * (x * y + y * z + z * x) := by
      ring
    have h₁₃₉ : (x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z)) ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by
      calc
        (x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z)) ≥ (x + y + z)^2 / ((a * x * y + b * x * z) + (a * y * z + b * x * y) + (a * x * z + b * y * z)) := by
          exact h₁₃₇
        _ = (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by
          rw [h₁₃₈]
        _ ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by rfl
    exact h₁₃₉
  
  have h₁₄ : (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
    have h₁₄₁ : (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
      have h₁₄₂ : 0 < (a + b) * (x * y + y * z + z * x) := by positivity
      -- Use the division inequality to transform the goal into a product form
      rw [ge_iff_le]
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Simplify the inequality using nlinarith
      nlinarith [h₁₁]
    exact h₁₄₁
  
  have h₁₅ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
    calc
      x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = (x^2 / (a * x * y + b * x * z) + y^2 / (a * y * z + b * x * y) + z^2 / (a * x * z + b * y * z)) := by rw [h₁₂]
      _ ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by exact h₁₃
      _ ≥ 3 / (a + b) := by exact h₁₄
  
  exact h₁₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_102 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) ≥ a + b + c := by
  have h_main : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) ≥ a + b + c := by
    intro a b c h
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a + b := by linarith
    have h₅ : 0 < b + c := by linarith
    have h₆ : 0 < c + a := by linarith
    have h₇ : (a ^ 2 + b ^ 2) / (a + b) ≥ (a + b) / 2 := by
      -- Prove that (a^2 + b^2) / (a + b) ≥ (a + b) / 2
      have h₇₁ : 0 < a + b := by linarith
      have h₇₂ : 0 < a * b := by positivity
      field_simp [h₇₁.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    have h₈ : (b ^ 2 + c ^ 2) / (b + c) ≥ (b + c) / 2 := by
      -- Prove that (b^2 + c^2) / (b + c) ≥ (b + c) / 2
      have h₈₁ : 0 < b + c := by linarith
      have h₈₂ : 0 < b * c := by positivity
      field_simp [h₈₁.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
    have h₉ : (c ^ 2 + a ^ 2) / (c + a) ≥ (c + a) / 2 := by
      -- Prove that (c^2 + a^2) / (c + a) ≥ (c + a) / 2
      have h₉₁ : 0 < c + a := by linarith
      have h₉₂ : 0 < c * a := by positivity
      field_simp [h₉₁.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]
    -- Sum the inequalities and simplify to get the final result
    have h₁₀ : (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) ≥ (a + b) / 2 + (b + c) / 2 + (c + a) / 2 := by
      linarith
    have h₁₁ : (a + b) / 2 + (b + c) / 2 + (c + a) / 2 = a + b + c := by
      ring
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_103_1 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) ≥ 1 / 2 := by
  intro x y z h
  have h_main : x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y) ≥ 1 / 2 := by
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 2 * x + y), sq_nonneg (y - 2 * y + z), sq_nonneg (z - 2 * z + x),
      sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_103_2 : ∀ (w x y z : ℝ), w > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0 → w / (x + 2 * y + 3 * z) + x / (y + 2 * z + 3 * w) + y / (z + 2 * w + 3 * x) + z / (w + 2 * x + 3 * y) ≥ 2 / 3 := by
  have h_main : ∀ (w x y z : ℝ), w > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0 → w / (x + 2 * y + 3 * z) + x / (y + 2 * z + 3 * w) + y / (z + 2 * w + 3 * x) + z / (w + 2 * x + 3 * y) ≥ 2 / 3 := by
    intro w x y z h
    have h₁ : 0 < w := by linarith
    have h₂ : 0 < x := by linarith
    have h₃ : 0 < y := by linarith
    have h₄ : 0 < z := by linarith
    have h₅ : 0 < w * x := mul_pos h₁ h₂
    have h₆ : 0 < x * y := mul_pos h₂ h₃
    have h₇ : 0 < y * z := mul_pos h₃ h₄
    have h₈ : 0 < z * w := mul_pos h₄ h₁
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (w - x), sq_nonneg (w - y), sq_nonneg (w - z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      mul_nonneg h₁.le (sq_nonneg (w - x)), mul_nonneg h₁.le (sq_nonneg (w - y)), mul_nonneg h₁.le (sq_nonneg (w - z)),
      mul_nonneg h₁.le (sq_nonneg (x - y)), mul_nonneg h₁.le (sq_nonneg (x - z)), mul_nonneg h₁.le (sq_nonneg (y - z)),
      mul_nonneg h₂.le (sq_nonneg (w - x)), mul_nonneg h₂.le (sq_nonneg (w - y)), mul_nonneg h₂.le (sq_nonneg (w - z)),
      mul_nonneg h₂.le (sq_nonneg (x - y)), mul_nonneg h₂.le (sq_nonneg (x - z)), mul_nonneg h₂.le (sq_nonneg (y - z)),
      mul_nonneg h₃.le (sq_nonneg (w - x)), mul_nonneg h₃.le (sq_nonneg (w - y)), mul_nonneg h₃.le (sq_nonneg (w - z)),
      mul_nonneg h₃.le (sq_nonneg (x - y)), mul_nonneg h₃.le (sq_nonneg (x - z)), mul_nonneg h₃.le (sq_nonneg (y - z)),
      mul_nonneg h₄.le (sq_nonneg (w - x)), mul_nonneg h₄.le (sq_nonneg (w - y)), mul_nonneg h₄.le (sq_nonneg (w - z)),
      mul_nonneg h₄.le (sq_nonneg (x - y)), mul_nonneg h₄.le (sq_nonneg (x - z)), mul_nonneg h₄.le (sq_nonneg (y - z))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_104 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x ^ 2 / ((x + y) * (x + z)) + y ^ 2 / ((y + z) * (y + x)) + z ^ 2 / ((z + x) * (z + y)) ≥ 3 / 4 := by
  have h_main : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x ^ 2 / ((x + y) * (x + z)) + y ^ 2 / ((y + z) * (y + x)) + z ^ 2 / ((z + x) * (z + y)) ≥ 3 / 4 := by
    intro x y z h
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2),
      sq_nonneg (x ^ 2 - x * y), sq_nonneg (y ^ 2 - y * z), sq_nonneg (z ^ 2 - z * x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)), mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (z - x)),
      mul_nonneg (sq_nonneg (z - x)) (sq_nonneg (x - y))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_7_5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a + b) * (a + c) ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
  intro a b c h
  have h_main : (a + b) * (a + c) ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < a * b * c := by positivity
    have h₈ : 0 < a * b * c * (a + b + c) := by positivity
    -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
    have h₉ : 0 ≤ Real.sqrt (a * b * c * (a + b + c)) := by positivity
    -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
    have h₁₀ : 0 ≤ (a + b) * (a + c) := by positivity
    -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
    have h₁₁ : ((a + b) * (a + c))^2 ≥ (2 * Real.sqrt (a * b * c * (a + b + c)))^2 := by
      -- Prove that the square of the left-hand side is greater than or equal to the square of the right-hand side
      have h₁₂ : 0 ≤ a * b := by positivity
      have h₁₃ : 0 ≤ a * c := by positivity
      have h₁₄ : 0 ≤ b * c := by positivity
      have h₁₅ : 0 ≤ a * b * c := by positivity
      -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
      have h₁₆ : 0 ≤ a * b * c * (a + b + c) := by positivity
      -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
      have h₁₇ : (a + b) * (a + c) ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
        -- Prove that the left-hand side is greater than or equal to the right-hand side
        have h₁₈ : Real.sqrt (a * b * c * (a + b + c)) ≤ ((a + b) * (a + c)) / 2 := by
          apply Real.sqrt_le_iff.mpr
          constructor
          · positivity
          · nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg ((a + b) * (a + c) - 2 * a * b), sq_nonneg ((a + b) * (a + c) - 2 * a * c), sq_nonneg ((a + b) * (a + c) - 2 * b * c), mul_nonneg h₁.le h₂.le, mul_nonneg h₁.le h₃.le, mul_nonneg h₂.le h₃.le, sq_nonneg (a - b + a - c), sq_nonneg (a - b - (a - c)), sq_nonneg (a - c - (b - c)), sq_nonneg (b - c - (a - c))]
        -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
        nlinarith [Real.sq_sqrt (show 0 ≤ a * b * c * (a + b + c) by positivity), sq_nonneg ((a + b) * (a + c) - 2 * Real.sqrt (a * b * c * (a + b + c)))]
      nlinarith [Real.sq_sqrt (show 0 ≤ a * b * c * (a + b + c) by positivity), sq_nonneg ((a + b) * (a + c) - 2 * Real.sqrt (a * b * c * (a + b + c)))]
    -- Use the fact that the square of the left-hand side is greater than or equal to the square of the right-hand side
    nlinarith [Real.sq_sqrt (show 0 ≤ a * b * c * (a + b + c) by positivity), sq_nonneg ((a + b) * (a + c) - 2 * Real.sqrt (a * b * c * (a + b + c)))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_7_7 : ∀ (a b c : ℝ), 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧ c < 1 → Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) < 1 := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : a < 1 := by linarith
  have h₃ : 0 < b := by linarith
  have h₄ : b < 1 := by linarith
  have h₅ : 0 < c := by linarith
  have h₆ : c < 1 := by linarith
  have h₇ : 0 < a * b := by positivity
  have h₈ : 0 < a * b * c := by positivity
  have h₉ : 0 < 1 - a := by linarith
  have h₁₀ : 0 < 1 - b := by linarith
  have h₁₁ : 0 < 1 - c := by linarith
  have h₁₂ : 0 < (1 - a) * (1 - b) * (1 - c) := by positivity
  have h₁₃ : Real.sqrt (a * b * c) ≤ (a * b + c) / 2 := by
    have h₁₃₁ : 0 ≤ a * b := by positivity
    have h₁₃₂ : 0 ≤ c := by positivity
    have h₁₃₃ : 0 ≤ a * b * c := by positivity
    have h₁₃₄ : Real.sqrt (a * b * c) ≤ (a * b + c) / 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ a * b * c by positivity), sq_nonneg (a * b - c)]
    exact h₁₃₄
  have h₁₄ : Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ ((1 - a) * (1 - b) + (1 - c)) / 2 := by
    have h₁₄₁ : 0 ≤ (1 - a) * (1 - b) := by positivity
    have h₁₄₂ : 0 ≤ (1 - c) := by positivity
    have h₁₄₃ : 0 ≤ (1 - a) * (1 - b) * (1 - c) := by positivity
    have h₁₄₄ : Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ ((1 - a) * (1 - b) + (1 - c)) / 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (1 - a) * (1 - b) * (1 - c) by positivity), sq_nonneg ((1 - a) * (1 - b) - (1 - c))]
    exact h₁₄₄
  have h₁₅ : Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ (a * b - a / 2 - b / 2 + 1 : ℝ) := by
    have h₁₅₁ : Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ (a * b + c) / 2 + ((1 - a) * (1 - b) + (1 - c)) / 2 := by
      linarith
    have h₁₅₂ : (a * b + c) / 2 + ((1 - a) * (1 - b) + (1 - c)) / 2 = (a * b - a / 2 - b / 2 + 1 : ℝ) := by
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> linarith
    linarith
  have h₁₆ : a * b - a / 2 - b / 2 + 1 < 1 := by
    have h₁₆₁ : a * b - a / 2 - b / 2 + 1 < 1 := by
      nlinarith [mul_pos h₁ h₃, mul_pos h₃ h₅, mul_pos h₅ h₁]
    linarith
  have h₁₇ : Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) < 1 := by
    linarith
  exact h₁₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_110 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1 → 1 / (y * z + z) + 1 / (z * x + x) + 1 / (x * y + y) ≥ 3 / 2 := by
  intro x y z h
  have h_main : 1 / (y * z + z) + 1 / (z * x + x) + 1 / (x * y + y) ≥ 3 / 2 := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have hz : 0 < z := by linarith
    have h₁ : 0 < x * y := by positivity
    have h₂ : 0 < x * z := by positivity
    have h₃ : 0 < y * z := by positivity
    have h₄ : 0 < x * y * z := by positivity
    have h₅ : x * y * z = 1 := by linarith
    have h₆ : 0 < x * y * z := by positivity
    field_simp [hx.ne', hy.ne', hz.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
      mul_le_mul_of_nonneg_right (sq_nonneg (x - 1)) (le_of_lt hy),
      mul_le_mul_of_nonneg_right (sq_nonneg (y - 1)) (le_of_lt hx),
      mul_le_mul_of_nonneg_right (sq_nonneg (z - 1)) (le_of_lt hx),
      mul_le_mul_of_nonneg_right (sq_nonneg (x - 1)) (le_of_lt hz),
      mul_le_mul_of_nonneg_right (sq_nonneg (y - 1)) (le_of_lt hz),
      mul_le_mul_of_nonneg_right (sq_nonneg (z - 1)) (le_of_lt hy),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
      mul_pos (mul_pos hx hy) hz, mul_pos (mul_pos hx hy) hx,
      mul_pos (mul_pos hx hy) hy]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_8_7 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥ 1 / 7 * (a + b + c) ^ 3 := by
  have h_main : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥ 1 / 7 * (a + b + c) ^ 3 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 ≤ a * b * c := by positivity
    have h₂ : 0 ≤ a * b := by positivity
    have h₃ : 0 ≤ b * c := by positivity
    have h₄ : 0 ≤ c * a := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c), sq_nonneg (a + b - 2 * c), sq_nonneg (b + c - 2 * a),
      sq_nonneg (c + a - 2 * b), mul_nonneg ha (sq_nonneg (a - b)),
      mul_nonneg hb (sq_nonneg (b - c)), mul_nonneg hc (sq_nonneg (c - a)),
      mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hb (sq_nonneg (b - a)),
      mul_nonneg hc (sq_nonneg (c - b))]
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_115 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
  intro a b c h
  have h_main : a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
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
    have h₁₁ : 0 < a ^ 3 := by positivity
    have h₁₂ : 0 < b ^ 3 := by positivity
    have h₁₃ : 0 < c ^ 3 := by positivity
    have h₁₄ : 0 < a ^ 2 * b := by positivity
    have h₁₅ : 0 < b ^ 2 * c := by positivity
    have h₁₆ : 0 < c ^ 2 * a := by positivity
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

theorem radmila_exercise_1_117 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a / ((a + b) * (a + c)) + b / ((b + c) * (b + a)) + c / ((c + a) * (c + b)) ≤ 9 / (4 * (a + b + c)) := by
  have h_main : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a / ((a + b) * (a + c)) + b / ((b + c) * (b + a)) + c / ((c + a) * (c + b)) ≤ 9 / (4 * (a + b + c)) := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < a * c := mul_pos ha hc
    have h₃ : 0 < b * c := mul_pos hb hc
    have h₄ : 0 < a * b * c := by positivity
    have h₅ : 0 < a * b * c * a := by positivity
    have h₆ : 0 < a * b * c * b := by positivity
    have h₇ : 0 < a * b * c * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (a - c)),
      mul_nonneg h₃.le (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - c)),
      mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)), mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (a + c - b)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a)), mul_nonneg (sq_nonneg (a + b - c)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a + c - b)) (sq_nonneg (a - c)), mul_nonneg (sq_nonneg (b + c - a)) (sq_nonneg (b - c))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_118 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
  intro a b c h
  have h₁ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
    have h₂ : a > 0 := by linarith
    have h₃ : b > 0 := by linarith
    have h₄ : c > 0 := by linarith
    have h₅ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) = a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
      ring
    have h₆ : a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) ≥ 0 := by
      cases' le_total a b with h₇ h₇ <;> cases' le_total b c with h₈ h₈ <;> cases' le_total c a with h₉ h₉ <;>
        nlinarith [mul_pos h₂ h₃, mul_pos h₃ h₄, mul_pos h₄ h₂, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg (sub_nonneg.mpr h₇) (sub_nonneg.mpr h₈), mul_nonneg (sub_nonneg.mpr h₈) (sub_nonneg.mpr h₉),
          mul_nonneg (sub_nonneg.mpr h₉) (sub_nonneg.mpr h₇), mul_nonneg (sub_nonneg.mpr h₇) (sub_nonneg.mpr h₉),
          mul_nonneg (sub_nonneg.mpr h₈) (sub_nonneg.mpr h₇), mul_nonneg (sub_nonneg.mpr h₉) (sub_nonneg.mpr h₈)]
    have h₇ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) ≥ 0 := by
      linarith
    have h₈ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
      linarith
    exact h₈
  exact h₁
