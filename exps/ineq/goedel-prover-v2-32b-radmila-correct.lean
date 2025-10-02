
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
    -- Use the property that the product of two negative numbers is positive
    have h₄ : a * b > 0 := by
      -- Multiply the inequality a < 0 by b (which is negative) to get a * b > 0
      have h₅ : a * b > 0 := by
        -- Use the fact that multiplying both sides of an inequality by a negative number reverses the inequality
        nlinarith [h₂, h₃]
      exact h₅
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
  have h₁ : a * b < 0 := by
    have h₂ : a < 0 := h.1
    have h₃ : b > 0 := h.2
    -- Use the fact that the product of a negative number and a positive number is negative.
    have h₄ : a * b < 0 := by
      -- Use the property that if a < 0 and b > 0, then a * b < 0.
      nlinarith
    exact h₄
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_iii : ∀ (a b c : ℝ), a < b ∧ b < c → a < c := by
  intro a b c h
  have h₁ : a < c := by
    -- Apply the transitivity property of the less-than relation
    exact lt_trans h.1 h.2
  -- The result follows directly from h₁
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_iv : ∀ (a b c d : ℝ), a < b ∧ c < d → a + c < b + d := by
  intro a b c d h
  have h₁ : a + c < b + c := by
    apply add_lt_add_right h.1
  have h₂ : b + c < b + d := by
    apply add_lt_add_left h.2
  exact lt_trans h₁ h₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_v : ∀ (a b : ℝ), a < b → -b < -a := by
  intro a b h
  have h₁ : -b < -a := by
    -- Add -a - b to both sides of the inequality a < b
    have h₂ : a + (-a - b) < b + (-a - b) := by
      -- Use the property that adding the same number to both sides preserves the inequality
      linarith
    -- Simplify both sides of the inequality
    have h₃ : a + (-a - b) = -b := by ring
    have h₄ : b + (-a - b) = -a := by ring
    -- Substitute the simplified forms back into the inequality
    rw [h₃] at h₂
    rw [h₄] at h₂
    -- The result is -b < -a
    exact h₂
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
    by_contra h
    -- Assume for contradiction that 1 / a ≤ 0
    have h₁ : 1 / a ≤ 0 := by
      -- Since we are assuming the negation of 1 / a > 0, it must be that 1 / a ≤ 0
      linarith
    -- Multiply both sides of 1 / a ≤ 0 by a > 0 to get a * (1 / a) ≤ 0
    have h₂ : a * (1 / a) ≤ 0 := by
      -- Use the fact that a > 0 and 1 / a ≤ 0 to multiply the inequality
      have h₃ : 0 < a := ha
      have h₄ : 1 / a ≤ 0 := h₁
      nlinarith
    -- But a * (1 / a) = 1, so we have 1 ≤ 0, which is a contradiction
    have h₃ : a * (1 / a) = 1 := by
      -- Simplify the product a * (1 / a)
      field_simp [ha.ne']
    have h₄ : (1 : ℝ) ≤ 0 := by linarith
    -- The contradiction shows that our assumption was false, so 1 / a > 0
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_vii : ∀ (a : ℝ), a < 0 → 1 / a < 0 := by
  intro a h₀
  have h₁ : (1 : ℝ) / a < 0 := by
    -- Use the lemma `div_neg_of_pos_of_neg` to prove that 1 / a < 0
    -- This lemma states that if the numerator is positive and the denominator is negative, then the division is negative.
    have h₂ : (0 : ℝ) < 1 := by norm_num
    have h₃ : a < 0 := h₀
    -- Apply the lemma to get the desired result
    exact div_neg_of_pos_of_neg h₂ h₃
  -- The result follows directly from the `have` statement
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_viii : ∀ (a b : ℝ), a > 0 ∧ b > 0 → a / b > 0 := by
  intro a b h
  have h₁ : b > 0 := by
    -- Extract the second part of the hypothesis which states that b > 0
    have h₂ : b > 0 := h.2
    -- Directly use the extracted hypothesis to conclude b > 0
    exact h₂
  
  have h₂ : 1 / b > 0 := by
    -- Since b > 0, the reciprocal of b is also positive.
    have h₃ : 0 < b := by linarith
    -- Use the property that the reciprocal of a positive number is positive.
    have h₄ : 0 < 1 / b := by
      apply div_pos
      · norm_num -- Prove that 1 > 0
      · linarith -- Use the fact that b > 0
    -- The result follows directly from the above steps.
    exact h₄
  
  have h₃ : a / b > 0 := by
    -- Since a > 0 and 1/b > 0, their product a * (1/b) = a / b is positive.
    have h₄ : a > 0 := h.1
    have h₅ : 0 < a := by linarith
    have h₆ : 0 < 1 / b := by linarith
    -- Use the property that the product of two positive numbers is positive.
    have h₇ : 0 < a * (1 / b) := by positivity
    -- Simplify the expression a * (1 / b) to a / b.
    have h₈ : a / b = a * (1 / b) := by
      field_simp
      <;> ring
    -- Substitute a / b with a * (1 / b) and use the fact that their product is positive.
    rw [h₈]
    linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_ix : ∀ (a b c d : ℝ), 0 < a ∧ a < b ∧ 0 < c ∧ c < d → a * c < b * d := by
  intro a b c d h
  have h₁ : 0 < a := h.1
  have h₂ : a < b := h.2.1
  have h₃ : 0 < c := h.2.2.1
  have h₄ : c < d := h.2.2.2
  have h₅ : 0 < b := by linarith
  have h₆ : 0 < d := by linarith
  have h₇ : 0 < a * c := by positivity
  have h₈ : 0 < a * d := by positivity
  have h₉ : 0 < b * c := by positivity
  have h₁₀ : 0 < b * d := by positivity
  -- We need to show that a * c < b * d.
  -- We can use the fact that a < b and c < d to derive inequalities involving products.
  -- Specifically, we can use the fact that a * c < a * d and a * d < b * d, which together imply a * c < b * d.
  have h₁₁ : a * c < a * d := by
    -- Since a > 0 and c < d, multiplying both sides by a gives a * c < a * d.
    nlinarith
  have h₁₂ : a * d < b * d := by
    -- Since d > 0 and a < b, multiplying both sides by d gives a * d < b * d.
    nlinarith
  -- Combining the inequalities a * c < a * d and a * d < b * d gives a * c < b * d.
  nlinarith

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_x : ∀ (a : ℝ), a > 1 → a ^ 2 > a := by
  intro a h
  have h₁ : a > 0 := by
    linarith
  
  have h₂ : a ^ 2 > a := by
    have h₃ : a * a > a := by
      -- Multiply both sides of the inequality `a > 1` by `a` (which is positive)
      have h₄ : a > 1 := h
      have h₅ : a > 0 := h₁
      nlinarith
    -- Since `a ^ 2` is `a * a`, we can directly use the result from `h₃`
    have h₆ : a ^ 2 = a * a := by ring
    rw [h₆]
    exact h₃
  
  exact h₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_1_4_xi : ∀ (a : ℝ), 0 < a ∧ a < 1 → a ^ 2 < a := by
  intro a h
  have h₁ : a ^ 2 < a := by
    have h₂ : 0 < a := h.1
    have h₃ : a < 1 := h.2
    have h₄ : a * a < a := by
      -- Multiply both sides of the inequality `a < 1` by `a` (which is positive)
      have h₅ : a * a < a * 1 := by
        -- Since `a > 0`, multiplying both sides of `a < 1` by `a` preserves the inequality
        nlinarith
      -- Simplify `a * 1` to `a`
      linarith
    -- Since `a * a = a²`, we have `a² < a`
    nlinarith
  -- The final result follows directly from `h₁`
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_1_left : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → 0 ≤ (b - a) / (1 - a * b) := by
  intro a b h
  have h₁ : a * b ≤ 1 := by
    have h₁₁ : 0 ≤ a := by linarith
    have h₁₂ : a ≤ 1 := by linarith
    have h₁₃ : 0 ≤ b := by linarith
    have h₁₄ : b ≤ 1 := by linarith
    nlinarith [mul_nonneg h₁₁ h₁₃]
  
  have h₂ : 1 - a * b ≥ 0 := by
    have h₂₁ : a * b ≤ 1 := h₁
    linarith
  
  have h₃ : b - a ≥ 0 := by
    have h₃₁ : a ≤ b := by linarith
    linarith
  
  have h₄ : 0 ≤ (b - a) / (1 - a * b) := by
    by_cases h₄₁ : (1 - a * b) = 0
    · -- Case: 1 - a * b = 0
      have h₄₂ : (b - a) / (1 - a * b) = 0 := by
        rw [h₄₁]
        simp
      rw [h₄₂]
      <;> linarith
    · -- Case: 1 - a * b ≠ 0
      have h₄₂ : 1 - a * b > 0 := by
        by_contra h₄₃
        have h₄₄ : 1 - a * b ≤ 0 := by linarith
        have h₄₅ : 1 - a * b = 0 := by
          linarith
        contradiction
      have h₄₃ : 0 ≤ (b - a) / (1 - a * b) := by
        apply div_nonneg h₃ (by linarith)
      exact h₄₃
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_1_right : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → (b - a) / (1 - a * b) ≤ 1 := by
  intro a b h
  have h₁ : a * b ≤ a := by
    have h₁₁ : 0 ≤ a := by linarith
    have h₁₂ : b ≤ 1 := by linarith
    nlinarith
  
  have h₂ : b - a ≤ 1 - a := by
    have h₂₁ : b ≤ 1 := by linarith
    linarith
  
  have h₃ : 1 - a ≤ 1 - a * b := by
    have h₃₁ : a * b ≤ a := h₁
    linarith
  
  have h₄ : b - a ≤ 1 - a * b := by
    linarith
  
  have h₅ : 0 ≤ 1 - a * b := by
    have h₅₁ : 0 ≤ a := by linarith
    have h₅₂ : 0 ≤ b := by linarith
    have h₅₃ : a ≤ 1 := by linarith
    have h₅₄ : b ≤ 1 := by linarith
    have h₅₅ : 0 ≤ a * b := by positivity
    have h₅₆ : a * b ≤ 1 := by
      nlinarith
    linarith
  
  have h₆ : (b - a) / (1 - a * b) ≤ 1 := by
    by_cases h₆₁ : (1 - a * b) = 0
    · -- Case: 1 - a * b = 0
      have h₆₂ : (b - a) / (1 - a * b) = 0 := by
        rw [h₆₁]
        simp
      rw [h₆₂]
      <;> norm_num
    · -- Case: 1 - a * b ≠ 0
      have h₆₃ : 0 < 1 - a * b := by
        by_contra h₆₄
        have h₆₅ : 1 - a * b ≤ 0 := by linarith
        have h₆₆ : 1 - a * b = 0 := by
          have h₆₇ : 0 ≤ 1 - a * b := h₅
          linarith
        contradiction
      -- Since 1 - a * b > 0, we can divide both sides by it
      have h₆₈ : (b - a) / (1 - a * b) ≤ 1 := by
        rw [div_le_iff h₆₃]
        nlinarith
      exact h₆₈
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_2_left : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → 0 ≤ a / (1 + b) + b / (1 + a) := by
  intro a b h
  have h₁ : 0 ≤ a := by linarith
  have h₂ : a ≤ b := by linarith
  have h₃ : b ≤ 1 := by linarith
  have h₄ : 0 ≤ b := by linarith
  have h₅ : 0 < 1 + a := by linarith
  have h₆ : 0 < 1 + b := by linarith
  have h₇ : 0 ≤ a / (1 + b) := by
    -- Prove that a / (1 + b) is non-negative
    apply div_nonneg h₁
    linarith
  have h₈ : 0 ≤ b / (1 + a) := by
    -- Prove that b / (1 + a) is non-negative
    apply div_nonneg h₄
    linarith
  -- Sum of non-negative numbers is non-negative
  linarith

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
    have h₅ : 0 ≤ 1 + a := by linarith
    have h₆ : 0 ≤ 1 + b := by linarith
    have h₇ : 0 ≤ (1 + a) * (1 + b) := by positivity
    field_simp [h₅, h₆]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
      mul_nonneg h₁ h₄, mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
      mul_nonneg (sub_nonneg.mpr h₂) h₁, mul_nonneg (sub_nonneg.mpr h₃) h₁,
      mul_nonneg (sub_nonneg.mpr h₃) h₄]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_3_left : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → 0 ≤ a * b ^ 2 - b * a ^ 2 := by
  intro a b h
  have h₁ : a * b ^ 2 - b * a ^ 2 = a * b * (b - a) := by
    have h₁₁ : a * b ^ 2 - b * a ^ 2 = a * b * b - b * a * a := by ring
    have h₁₂ : a * b * b - b * a * a = a * b * (b - a) := by
      ring_nf
      <;>
      linarith
    linarith
  
  have h₂ : 0 ≤ a := by
    have h₂₁ : 0 ≤ a := h.1
    exact h₂₁
  
  have h₃ : 0 ≤ b := by
    have h₃₁ : a ≤ b := h.2.1
    have h₃₂ : 0 ≤ a := h.1
    linarith
  
  have h₄ : 0 ≤ b - a := by
    have h₄₁ : a ≤ b := h.2.1
    linarith
  
  have h₅ : 0 ≤ a * b := by
    have h₅₁ : 0 ≤ a := h₂
    have h₅₂ : 0 ≤ b := h₃
    nlinarith
  
  have h₆ : 0 ≤ a * b * (b - a) := by
    have h₆₁ : 0 ≤ a * b := h₅
    have h₆₂ : 0 ≤ b - a := h₄
    nlinarith
  
  have h₇ : 0 ≤ a * b ^ 2 - b * a ^ 2 := by
    rw [h₁]
    exact h₆
  
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_7_3_right : ∀ (a b : ℝ), 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → a * b ^ 2 - b * a ^ 2 ≤ 1 / 4 := by
  intro a b h
  have h₁ : a * b ^ 2 - b * a ^ 2 ≤ a - a ^ 2 := by
    have h₁₁ : 0 ≤ a := by linarith
    have h₁₂ : a ≤ b := by linarith
    have h₁₃ : b ≤ 1 := by linarith
    have h₁₄ : 0 ≤ b := by linarith
    have h₁₅ : 0 ≤ 1 - b := by linarith
    have h₁₆ : 0 ≤ a * (1 + b) - a ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a - b)]
    have h₁₇ : (1 - b) * (a * (1 + b) - a ^ 2) ≥ 0 := by
      nlinarith
    have h₁₈ : a - a ^ 2 - (a * b ^ 2 - b * a ^ 2) = (1 - b) * (a * (1 + b) - a ^ 2) := by
      ring_nf
      <;>
      nlinarith
    have h₁₉ : a - a ^ 2 - (a * b ^ 2 - b * a ^ 2) ≥ 0 := by
      linarith
    linarith
  
  have h₂ : a - a ^ 2 ≤ 1 / 4 := by
    have h₂₁ : (a - 1 / 2) ^ 2 ≥ 0 := by nlinarith
    have h₂₂ : a - a ^ 2 ≤ 1 / 4 := by
      nlinarith [h₂₁]
    exact h₂₂
  
  have h₃ : a * b ^ 2 - b * a ^ 2 ≤ 1 / 4 := by
    linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_9 : ∀ (a b x y : ℝ), a ≥ b ∧ x ≥ y → a * x + b * y ≥ a * y + b * x := by
  intro a b x y h
  have h_main : (a - b) * (x - y) ≥ 0 := by
    have h₁ : a ≥ b := h.1
    have h₂ : x ≥ y := h.2
    have h₃ : a - b ≥ 0 := by linarith
    have h₄ : x - y ≥ 0 := by linarith
    have h₅ : (a - b) * (x - y) ≥ 0 := by
      -- Since both (a - b) and (x - y) are non-negative, their product is non-negative.
      nlinarith
    exact h₅
  
  have h_final : a * x + b * y ≥ a * y + b * x := by
    have h₁ : (a - b) * (x - y) ≥ 0 := h_main
    have h₂ : a * x + b * y - (a * y + b * x) = (a - b) * (x - y) := by
      ring
    have h₃ : a * x + b * y - (a * y + b * x) ≥ 0 := by
      linarith
    linarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_10 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x) ≥ Real.sqrt x + Real.sqrt y := by
  intro x y h
  have h₁ : Real.sqrt (x ^ 2 / y) = x / Real.sqrt y := by
    have h₁₁ : 0 < x := h.1
    have h₁₂ : 0 < y := h.2
    have h₁₃ : 0 < x ^ 2 / y := by positivity
    have h₁₄ : Real.sqrt (x ^ 2 / y) = Real.sqrt (x ^ 2) / Real.sqrt y := by
      rw [Real.sqrt_div (by positivity)]
      <;> field_simp [h₁₂.ne']
    rw [h₁₄]
    have h₁₅ : Real.sqrt (x ^ 2) = x := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
    rw [h₁₅]
    <;> field_simp [h₁₂.ne']
    <;> ring_nf
    <;> field_simp [h₁₂.ne']
    <;> linarith
  
  have h₂ : Real.sqrt (y ^ 2 / x) = y / Real.sqrt x := by
    have h₂₁ : 0 < x := h.1
    have h₂₂ : 0 < y := h.2
    have h₂₃ : 0 < y ^ 2 / x := by positivity
    have h₂₄ : Real.sqrt (y ^ 2 / x) = Real.sqrt (y ^ 2) / Real.sqrt x := by
      rw [Real.sqrt_div (by positivity)]
      <;> field_simp [h₂₁.ne']
    rw [h₂₄]
    have h₂₅ : Real.sqrt (y ^ 2) = y := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
    rw [h₂₅]
    <;> field_simp [h₂₁.ne']
    <;> ring_nf
    <;> field_simp [h₂₁.ne']
    <;> linarith
  
  have h₃ : x / Real.sqrt y + Real.sqrt y ≥ 2 * Real.sqrt x := by
    have h₃₁ : 0 < x := h.1
    have h₃₂ : 0 < y := h.2
    have h₃₃ : 0 < Real.sqrt x := Real.sqrt_pos.mpr h₃₁
    have h₃₄ : 0 < Real.sqrt y := Real.sqrt_pos.mpr h₃₂
    have h₃₅ : 0 < Real.sqrt x * Real.sqrt y := by positivity
    -- Use the fact that (sqrt(x) - sqrt(y))^2 ≥ 0 to derive the inequality
    have h₃₆ : (Real.sqrt x - Real.sqrt y) ^ 2 ≥ 0 := by positivity
    have h₃₇ : x + y - 2 * Real.sqrt x * Real.sqrt y ≥ 0 := by
      nlinarith [Real.sq_sqrt (le_of_lt h₃₁), Real.sq_sqrt (le_of_lt h₃₂),
        sq_nonneg (Real.sqrt x - Real.sqrt y)]
    -- Divide both sides by sqrt(y) to get the desired inequality
    have h₃₈ : (x + y) / Real.sqrt y ≥ 2 * Real.sqrt x := by
      have h₃₈₁ : (x + y) / Real.sqrt y ≥ 2 * Real.sqrt x := by
        calc
          (x + y) / Real.sqrt y = (x + y) / Real.sqrt y := by rfl
          _ ≥ (2 * Real.sqrt x * Real.sqrt y) / Real.sqrt y := by
            gcongr
            <;> nlinarith [Real.sq_sqrt (le_of_lt h₃₁), Real.sq_sqrt (le_of_lt h₃₂)]
          _ = 2 * Real.sqrt x := by
            field_simp [h₃₄.ne']
            <;> ring_nf
            <;> field_simp [h₃₄.ne']
            <;> linarith
      linarith
    have h₃₉ : x / Real.sqrt y + Real.sqrt y = (x + y) / Real.sqrt y := by
      have h₃₉₁ : x / Real.sqrt y + Real.sqrt y = (x + y) / Real.sqrt y := by
        field_simp [h₃₄.ne']
        <;> ring_nf
        <;> field_simp [h₃₄.ne']
        <;> linarith
      linarith
    linarith
  
  have h₄ : y / Real.sqrt x + Real.sqrt x ≥ 2 * Real.sqrt y := by
    have h₄₁ : 0 < x := h.1
    have h₄₂ : 0 < y := h.2
    have h₄₃ : 0 < Real.sqrt x := Real.sqrt_pos.mpr h₄₁
    have h₄₄ : 0 < Real.sqrt y := Real.sqrt_pos.mpr h₄₂
    have h₄₅ : 0 < Real.sqrt x * Real.sqrt y := by positivity
    -- Use the fact that (sqrt(x) - sqrt(y))^2 ≥ 0 to derive the inequality
    have h₄₆ : (Real.sqrt y - Real.sqrt x) ^ 2 ≥ 0 := by positivity
    have h₄₇ : y + x - 2 * Real.sqrt y * Real.sqrt x ≥ 0 := by
      nlinarith [Real.sq_sqrt (le_of_lt h₄₁), Real.sq_sqrt (le_of_lt h₄₂),
        sq_nonneg (Real.sqrt y - Real.sqrt x)]
    -- Divide both sides by sqrt(x) to get the desired inequality
    have h₄₈ : (y + x) / Real.sqrt x ≥ 2 * Real.sqrt y := by
      have h₄₈₁ : (y + x) / Real.sqrt x ≥ 2 * Real.sqrt y := by
        calc
          (y + x) / Real.sqrt x = (y + x) / Real.sqrt x := by rfl
          _ ≥ (2 * Real.sqrt y * Real.sqrt x) / Real.sqrt x := by
            gcongr
            <;> nlinarith [Real.sq_sqrt (le_of_lt h₄₁), Real.sq_sqrt (le_of_lt h₄₂)]
          _ = 2 * Real.sqrt y := by
            field_simp [h₄₃.ne']
            <;> ring_nf
            <;> field_simp [h₄₃.ne']
            <;> linarith
      linarith
    have h₄₉ : y / Real.sqrt x + Real.sqrt x = (y + x) / Real.sqrt x := by
      have h₄₉₁ : y / Real.sqrt x + Real.sqrt x = (y + x) / Real.sqrt x := by
        field_simp [h₄₃.ne']
        <;> ring_nf
        <;> field_simp [h₄₃.ne']
        <;> linarith
      linarith
    linarith
  
  have h₅ : x / Real.sqrt y + y / Real.sqrt x ≥ Real.sqrt x + Real.sqrt y := by
    have h₅₁ : x / Real.sqrt y + Real.sqrt y ≥ 2 * Real.sqrt x := h₃
    have h₅₂ : y / Real.sqrt x + Real.sqrt x ≥ 2 * Real.sqrt y := h₄
    have h₅₃ : x / Real.sqrt y + y / Real.sqrt x + (Real.sqrt x + Real.sqrt y) ≥ 2 * Real.sqrt x + 2 * Real.sqrt y := by
      linarith
    linarith
  
  have h₆ : Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x) ≥ Real.sqrt x + Real.sqrt y := by
    have h₆₁ : Real.sqrt (x ^ 2 / y) + Real.sqrt (y ^ 2 / x) = x / Real.sqrt y + y / Real.sqrt x := by
      rw [h₁, h₂]
      <;> ring
    rw [h₆₁]
    linarith
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_11 : ∀ (a b c d : ℝ), a + d = b + c → (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0 := by
  intro a b c d h
  have h1 : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b) * (c - d) := by
    have h₁ : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b) * (c - d) := by
      ring_nf at h ⊢
      <;>
      (try linarith) <;>
      (try nlinarith) <;>
      (try
        {
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
        })
      <;>
      (try
        {
          linarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
        })
    rw [h₁]
  
  have h2 : a - b = c - d := by
    have h₂ : a + d = b + c := h
    have h₃ : a - b = c - d := by linarith
    exact h₃
  
  have h3 : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b) ^ 2 := by
    have h₃ : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b) * (c - d) := h1
    have h₄ : a - b = c - d := h2
    calc
      (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b) * (c - d) := by rw [h₃]
      _ = 2 * (a - b) * (a - b) := by rw [h₄]
      _ = 2 * (a - b) ^ 2 := by ring
  
  have h4 : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0 := by
    have h₄ : (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) = 2 * (a - b) ^ 2 := h3
    rw [h₄]
    have h₅ : 2 * (a - b) ^ 2 ≥ 0 := by
      have h₅₁ : (a - b) ^ 2 ≥ 0 := by nlinarith
      nlinarith
    linarith
  
  exact h4

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_12 : ∀ (a b c d : ℝ), a < b ∧ b < c ∧ c < d → (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 > 0 := by
  intro a b c d h
  have h₁ : (a - b) ^ 2 > 0 := by
    have h₁₁ : a - b ≠ 0 := by
      linarith [h.1]
    have h₁₂ : (a - b) ^ 2 > 0 := by
      exact sq_pos_of_ne_zero h₁₁
    exact h₁₂
  
  have h₂ : (b - c) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (b - c)]
  
  have h₃ : (c - d) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (c - d)]
  
  have h₄ : (d - a) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (d - a)]
  
  have h_main : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 > 0 := by
    have h₅ : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 > 0 := by
      -- Use nlinarith to combine the inequalities and conclude the proof
      nlinarith [h₁, h₂, h₃, h₄]
    exact h₅
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_15 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by
  have lemma1 : ∀ (x y : ℝ), x > 0 → y > 0 → x ^ 5 + y ^ 5 ≥ x * y * (x ^ 3 + y ^ 3) := by
    intro x y hx hy
    have h₁ : 0 < x * y := mul_pos hx hy
    have h₂ : (x - y) * (x ^ 4 - y ^ 4) ≥ 0 := by
      by_cases h : x ≥ y
      · have h₃ : x - y ≥ 0 := by linarith
        have h₄ : x ^ 4 - y ^ 4 ≥ 0 := by
          have h₅ : x ^ 2 ≥ y ^ 2 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
          nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2)]
        nlinarith
      · have h₃ : x - y < 0 := by linarith
        have h₄ : x ^ 4 - y ^ 4 < 0 := by
          have h₅ : x ^ 2 < y ^ 2 := by
            nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x - y), sq_nonneg (x + y)]
          nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2)]
        nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2),
      sq_nonneg (x ^ 2 + y ^ 2)]
  
  have lemma2 : ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → a * b * c = 1 → a ^ 3 + b ^ 3 + 1 ≥ a * b * (a + b + c) := by
    intro a b c ha hb hc habc
    have h₁ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
      nlinarith [sq_nonneg (a - b), mul_pos ha hb, sq_nonneg (a + b)]
    have h₂ : 1 = a * b * c := by linarith
    nlinarith [h₁, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  
  have lemma3 : ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → a * b * c = 1 → a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
    intro a b c ha hb hc habc
    have h₁ : a ^ 5 + b ^ 5 ≥ a * b * (a ^ 3 + b ^ 3) := lemma1 a b ha hb
    have h₂ : a ^ 3 + b ^ 3 + 1 ≥ a * b * (a + b + c) := lemma2 a b c ha hb hc habc
    have h₃ : 0 < a * b := mul_pos ha hb
    have h₄ : 0 < a + b + c := by positivity
    have h₅ : 0 < a ^ 5 + b ^ 5 + a * b := by positivity
    have h₆ : 0 < a ^ 3 + b ^ 3 + 1 := by positivity
    -- Prove that a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a ^ 3 + b ^ 3 + 1)
    have h₇ : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a ^ 3 + b ^ 3 + 1) := by
      -- Use the fact that a ^ 5 + b ^ 5 ≥ a * b * (a ^ 3 + b ^ 3)
      have h₇₁ : a ^ 5 + b ^ 5 + a * b ≥ a * b * (a ^ 3 + b ^ 3 + 1) := by
        nlinarith [h₁]
      -- Use the division inequality to compare the fractions
      have h₇₂ : 0 < a * b * (a ^ 3 + b ^ 3 + 1) := by positivity
      have h₇₃ : 0 < a ^ 5 + b ^ 5 + a * b := by positivity
      calc
        a * b / (a ^ 5 + b ^ 5 + a * b) ≤ a * b / (a * b * (a ^ 3 + b ^ 3 + 1)) := by
          apply div_le_div_of_le_left (by positivity) (by positivity)
          linarith
        _ = 1 / (a ^ 3 + b ^ 3 + 1) := by
          have h₇₄ : a * b / (a * b * (a ^ 3 + b ^ 3 + 1)) = 1 / (a ^ 3 + b ^ 3 + 1) := by
            field_simp [h₃.ne']
            <;> ring_nf
            <;> field_simp [h₃.ne']
            <;> ring_nf
          rw [h₇₄]
    -- Prove that 1 / (a ^ 3 + b ^ 3 + 1) ≤ c / (a + b + c)
    have h₈ : 1 / (a ^ 3 + b ^ 3 + 1) ≤ c / (a + b + c) := by
      -- Use the fact that a ^ 3 + b ^ 3 + 1 ≥ a * b * (a + b + c)
      have h₈₁ : a ^ 3 + b ^ 3 + 1 ≥ a * b * (a + b + c) := h₂
      have h₈₂ : 0 < a * b * (a + b + c) := by positivity
      have h₈₃ : 0 < a ^ 3 + b ^ 3 + 1 := by positivity
      calc
        1 / (a ^ 3 + b ^ 3 + 1) ≤ 1 / (a * b * (a + b + c)) := by
          apply one_div_le_one_div_of_le
          · positivity
          · linarith
        _ = c / (a + b + c) := by
          have h₈₄ : 1 / (a * b * (a + b + c)) = c / (a + b + c) := by
            have h₈₅ : a * b * c = 1 := habc
            have h₈₆ : c = 1 / (a * b) := by
              field_simp [h₃.ne'] at h₈₅ ⊢
              nlinarith
            rw [h₈₆]
            field_simp [h₃.ne']
            <;> ring_nf
            <;> field_simp [h₃.ne']
            <;> nlinarith
          rw [h₈₄]
    -- Combine the two inequalities to get the final result
    calc
      a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a ^ 3 + b ^ 3 + 1) := h₇
      _ ≤ c / (a + b + c) := h₈
  
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a * b * c = 1 := by
    have h₅ : a * b * c = 1 := by tauto
    exact h₅
  have h₅ : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
    have h₅₁ : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := lemma3 a b c h₁ h₂ h₃ h₄
    exact h₅₁
  have h₆ : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
    have h₆₁ : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
      have h₆₂ : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
        -- Use the lemma3 to get the inequality for the cyclic permutation (b, c, a)
        have h₆₃ : b > 0 := by linarith
        have h₆₄ : c > 0 := by linarith
        have h₆₅ : a > 0 := by linarith
        have h₆₆ : b * c * a = 1 := by
          calc
            b * c * a = a * b * c := by ring
            _ = 1 := by linarith
        have h₆₇ : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (b + c + a) := lemma3 b c a h₆₃ h₆₄ h₆₅ h₆₆
        -- Since addition is commutative, a + b + c = b + c + a
        have h₆₈ : a / (b + c + a) = a / (a + b + c) := by
          ring_nf
          <;> field_simp [add_assoc]
          <;> ring_nf
        rw [h₆₈] at h₆₇
        linarith
      exact h₆₂
    exact h₆₁
  have h₇ : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (a + b + c) := by
    have h₇₁ : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (a + b + c) := by
      have h₇₂ : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (a + b + c) := by
        -- Use the lemma3 to get the inequality for the cyclic permutation (c, a, b)
        have h₇₃ : c > 0 := by linarith
        have h₇₄ : a > 0 := by linarith
        have h₇₅ : b > 0 := by linarith
        have h₇₆ : c * a * b = 1 := by
          calc
            c * a * b = a * b * c := by ring
            _ = 1 := by linarith
        have h₇₇ : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (c + a + b) := lemma3 c a b h₇₃ h₇₄ h₇₅ h₇₆
        -- Since addition is commutative, a + b + c = c + a + b
        have h₇₈ : b / (c + a + b) = b / (a + b + c) := by
          ring_nf
          <;> field_simp [add_assoc]
          <;> ring_nf
        rw [h₇₈] at h₇₇
        linarith
      exact h₇₂
    exact h₇₁
  have h₈ : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by
    have h₈₁ : 0 < a + b + c := by positivity
    have h₈₂ : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a) ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by
      linarith [h₅, h₆, h₇]
    have h₈₃ : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1 := by
      have h₈₄ : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = (a + b + c) / (a + b + c) := by
        field_simp [h₈₁.ne']
        <;> ring_nf
        <;> field_simp [h₈₁.ne']
        <;> ring_nf
      rw [h₈₄]
      have h₈₅ : (a + b + c : ℝ) / (a + b + c) = 1 := by
        field_simp [h₈₁.ne']
      rw [h₈₅]
    linarith [h₈₂, h₈₃]
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_am_gm_inequality : ∀ (a b : ℝ), a ≥ 0 ∧ b ≥ 0 → (a + b) / 2 ≥ Real.sqrt (a * b) := by
  intro a b h
  have h₁ : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  
  have h₂ : a + b - 2 * (Real.sqrt a * Real.sqrt b) ≥ 0 := by
    have h₂₁ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₂₂ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₂₃ : (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := h₁
    have h₂₄ : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
      have h₂₄₁ : 0 ≤ a := by linarith
      have h₂₄₂ : 0 ≤ b := by linarith
      have h₂₄₃ : (Real.sqrt a) ^ 2 = a := by rw [Real.sq_sqrt] <;> linarith
      have h₂₄₄ : (Real.sqrt b) ^ 2 = b := by rw [Real.sq_sqrt] <;> linarith
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    linarith
  
  have h₃ : a + b ≥ 2 * (Real.sqrt a * Real.sqrt b) := by
    have h₃₁ : a + b - 2 * (Real.sqrt a * Real.sqrt b) ≥ 0 := h₂
    linarith
  
  have h₄ : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
    have h₄₁ : 0 ≤ a := by linarith
    have h₄₂ : 0 ≤ b := by linarith
    have h₄₃ : 0 ≤ a * b := by positivity
    have h₄₄ : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
      rw [← Real.sqrt_mul] <;>
      (try positivity) <;>
      (try linarith)
      <;>
      (try nlinarith)
    rw [h₄₄]
    <;>
    (try positivity) <;>
    (try linarith) <;>
    (try nlinarith)
  
  have h₅ : a + b ≥ 2 * Real.sqrt (a * b) := by
    have h₅₁ : a + b ≥ 2 * (Real.sqrt a * Real.sqrt b) := h₃
    have h₅₂ : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := h₄
    have h₅₃ : 2 * (Real.sqrt a * Real.sqrt b) = 2 * Real.sqrt (a * b) := by
      rw [h₅₂]
      <;> ring
    linarith
  
  have h₆ : (a + b) / 2 ≥ Real.sqrt (a * b) := by
    have h₆₁ : a + b ≥ 2 * Real.sqrt (a * b) := h₅
    have h₆₂ : (a + b) / 2 ≥ Real.sqrt (a * b) := by
      linarith
    exact h₆₂
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_18 : ∀ (x : ℝ), x ≥ 0 → 1 + x ≥ 2 * Real.sqrt x := by
  intro x hx
  have h_main : (Real.sqrt x - 1) ^ 2 ≥ 0 := by
    -- The square of any real number is non-negative.
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  
  have h_expand : (Real.sqrt x - 1) ^ 2 = x - 2 * Real.sqrt x + 1 := by
    have h₁ : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    -- Expand the square (sqrt(x) - 1)^2
    have h₂ : (Real.sqrt x - 1) ^ 2 = (Real.sqrt x) ^ 2 - 2 * Real.sqrt x + 1 := by
      ring_nf
      <;>
      nlinarith [Real.sq_sqrt hx]
    -- Simplify (sqrt(x))^2 to x
    have h₃ : (Real.sqrt x) ^ 2 = x := by
      rw [Real.sq_sqrt hx]
    -- Substitute back into the expanded form
    rw [h₂, h₃]
    <;>
    ring_nf
    <;>
    nlinarith [Real.sq_sqrt hx]
  
  have h_combine : x - 2 * Real.sqrt x + 1 ≥ 0 := by
    have h₁ : (Real.sqrt x - 1) ^ 2 = x - 2 * Real.sqrt x + 1 := h_expand
    have h₂ : (Real.sqrt x - 1) ^ 2 ≥ 0 := h_main
    linarith
  
  have h_final : 1 + x ≥ 2 * Real.sqrt x := by
    have h₁ : x - 2 * Real.sqrt x + 1 ≥ 0 := h_combine
    -- Rearrange the inequality to get 1 + x ≥ 2 * Real.sqrt x
    have h₂ : 1 + x ≥ 2 * Real.sqrt x := by
      linarith [Real.sqrt_nonneg x]
    exact h₂
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_19 : ∀ (x : ℝ), x > 0 → x + 1 / x ≥ 2 := by
  intro x hx
  have h_main : x + 1 / x ≥ 2 := by
    have h₁ : 0 < x := hx
    field_simp [h₁.ne']
    rw [le_div_iff (by positivity)]
    -- Use nlinarith to prove the inequality after simplifying
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - 1 / x)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_20 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → x ^ 2 + y ^ 2 ≥ 2 * x * y := by
  intro x y h
  have h₁ : (x - y) ^ 2 ≥ 0 := by
    -- Use the fact that the square of any real number is non-negative
    nlinarith [sq_nonneg (x - y)]
  
  have h₂ : x ^ 2 + y ^ 2 ≥ 2 * x * y := by
    -- Expand the square (x - y)^2 and use the non-negativity to derive the desired inequality
    nlinarith [h₁]
  
  -- The final result follows directly from h₂
  exact h₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_21 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 2 * (x ^ 2 + y ^ 2) ≥ (x + y) ^ 2 := by
  intro x y h
  have h₁ : (x - y) ^ 2 ≥ 0 := by
    -- Prove that the square of any real number is non-negative
    nlinarith [sq_nonneg (x - y)]
  
  have h₂ : x ^ 2 + y ^ 2 ≥ 2 * x * y := by
    -- Use the non-negativity of (x - y)^2 to derive the inequality x^2 + y^2 ≥ 2xy
    have h₂₁ : (x - y) ^ 2 ≥ 0 := h₁
    -- Expand (x - y)^2 and simplify to get x^2 + y^2 - 2xy ≥ 0
    have h₂₂ : x ^ 2 + y ^ 2 - 2 * x * y ≥ 0 := by
      nlinarith
    -- Rearrange the inequality to get x^2 + y^2 ≥ 2xy
    nlinarith
  
  have h₃ : 2 * (x ^ 2 + y ^ 2) ≥ (x + y) ^ 2 := by
    -- Use the derived inequality x^2 + y^2 ≥ 2xy to prove the main inequality
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
  
  -- The final result follows directly from the established inequality h₃
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_22 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 1 / x + 1 / y ≥ 4 / (x + y) := by
  intro x y h
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < x + y := by linarith
  have h₄ : 0 < x * y := by positivity
  have h₅ : 0 < x * y * (x + y) := by positivity
  have h₆ : (x - y) ^ 2 ≥ 0 := by nlinarith
  have h₇ : x ^ 2 + y ^ 2 - 2 * x * y ≥ 0 := by
    nlinarith [sq_nonneg (x - y)]
  
  have h₈ : x ^ 2 + y ^ 2 + 2 * x * y ≥ 4 * x * y := by
    nlinarith [h₇]
  
  have h₉ : y * (x + y) + x * (x + y) ≥ 4 * x * y := by
    have h₉₁ : y * (x + y) + x * (x + y) = x ^ 2 + y ^ 2 + 2 * x * y := by
      ring
    rw [h₉₁]
    nlinarith [h₈]
  
  have h₁₀ : 1 / x + 1 / y ≥ 4 / (x + y) := by
    have h₁₀₁ : 1 / x + 1 / y = (y + x) / (x * y) := by
      field_simp [h₁.ne', h₂.ne']
      <;> ring
      <;> field_simp [h₁.ne', h₂.ne']
      <;> ring
    rw [h₁₀₁]
    have h₁₀₂ : (y + x) / (x * y) ≥ 4 / (x + y) := by
      -- Prove that (y + x) / (x * y) ≥ 4 / (x + y)
      have h₁₀₃ : 0 < x * y := by positivity
      have h₁₀₄ : 0 < x + y := by positivity
      -- Use the fact that the denominators are positive to cross-multiply
      have h₁₀₅ : (y + x) / (x * y) ≥ 4 / (x + y) := by
        rw [ge_iff_le]
        rw [div_le_div_iff (by positivity) (by positivity)]
        -- Use the inequality derived earlier
        nlinarith [h₉]
      exact h₁₀₅
    linarith
  
  exact h₁₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_23 : ∀ (a b x : ℝ), a > 0 ∧ b > 0 ∧ x > 0 → a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
  have h_main : ∀ (a b x : ℝ), a > 0 → b > 0 → x > 0 → a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
    intro a b x ha hb hx
    have h₁ : 0 < a * x := by positivity
    have h₂ : 0 < b / x := by positivity
    have h₃ : 0 < a * b := by positivity
    have h₄ : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr h₃
    -- Use the AM-GM inequality to prove the desired inequality
    have h₅ : a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
      -- Use the fact that the square of any real number is non-negative to derive the inequality
      have h₅₁ : 0 ≤ (a * x - b / x) ^ 2 := sq_nonneg _
      have h₅₂ : (a * x - b / x) ^ 2 ≥ 0 := by linarith
      have h₅₃ : a * x + b / x ≥ 2 * Real.sqrt (a * b) := by
        -- Use the AM-GM inequality to prove the desired inequality
        have h₅₄ : Real.sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
        have h₅₅ : (a * x + b / x) ≥ 2 * Real.sqrt (a * b) := by
          -- Use the fact that the square of any real number is non-negative to derive the inequality
          have h₅₆ : (a * x + b / x) ≥ 2 * Real.sqrt (a * b) := by
            -- Use the AM-GM inequality to prove the desired inequality
            have h₅₇ : Real.sqrt (a * b) = Real.sqrt (a * b) := rfl
            have h₅₈ : 0 ≤ a * x := by positivity
            have h₅₉ : 0 ≤ b / x := by positivity
            -- Use the AM-GM inequality to prove the desired inequality
            have h₅₁₀ : Real.sqrt (a * b) ≤ (a * x + b / x) / 2 := by
              apply Real.sqrt_le_iff.mpr
              constructor
              · positivity
              · -- Prove that (a * x + b / x) ^ 2 ≥ 4 * (a * b)
                have h₅₁₁ : 0 ≤ a * x := by positivity
                have h₅₁₂ : 0 ≤ b / x := by positivity
                have h₅₁₃ : 0 ≤ a * x * (b / x) := by positivity
                have h₅₁₄ : a * x * (b / x) = a * b := by
                  field_simp
                  <;> ring
                  <;> field_simp [hx.ne']
                  <;> ring
                nlinarith [sq_nonneg (a * x - b / x)]
            -- Use the AM-GM inequality to prove the desired inequality
            nlinarith
          linarith
        linarith
      linarith
    exact h₅
  intro a b x h
  have h₁ : a > 0 := h.1
  have h₂ : b > 0 := h.2.1
  have h₃ : x > 0 := h.2.2
  exact h_main a b x h₁ h₂ h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_24 : ∀ (a b : ℝ), a > 0 ∧ b > 0 → a / b + b / a ≥ 2 := by
  intro a b h
  have h₁ : 0 < a := by
    linarith
  
  have h₂ : 0 < b := by
    linarith
  
  have h₃ : 0 < a / b := by
    apply div_pos h₁ h₂
  
  have h₄ : 0 < b / a := by
    apply div_pos h₂ h₁
  
  have h₅ : (Real.sqrt (a / b) - Real.sqrt (b / a)) ^ 2 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (a / b), Real.sqrt_nonneg (b / a)]
  
  have h₆ : a / b + b / a - 2 ≥ 0 := by
    have h₆₁ : 0 ≤ Real.sqrt (a / b) := Real.sqrt_nonneg (a / b)
    have h₆₂ : 0 ≤ Real.sqrt (b / a) := Real.sqrt_nonneg (b / a)
    have h₆₃ : Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
      have h₆₄ : Real.sqrt (a / b) * Real.sqrt (b / a) = Real.sqrt ((a / b) * (b / a)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h₆₄]
      have h₆₅ : (a / b : ℝ) * (b / a) = 1 := by
        field_simp [h₁.ne', h₂.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne']
        <;> linarith
      rw [h₆₅]
      <;> simp [Real.sqrt_one]
    have h₆₆ : (Real.sqrt (a / b) - Real.sqrt (b / a)) ^ 2 ≥ 0 := h₅
    have h₆₇ : (Real.sqrt (a / b) - Real.sqrt (b / a)) ^ 2 = (a / b + b / a) - 2 := by
      have h₆₈ : (Real.sqrt (a / b) - Real.sqrt (b / a)) ^ 2 = (Real.sqrt (a / b)) ^ 2 + (Real.sqrt (b / a)) ^ 2 - 2 * (Real.sqrt (a / b) * Real.sqrt (b / a)) := by
        ring_nf
        <;>
        nlinarith [Real.sqrt_nonneg (a / b), Real.sqrt_nonneg (b / a)]
      rw [h₆₈]
      have h₆₉ : (Real.sqrt (a / b)) ^ 2 = a / b := by
        rw [Real.sq_sqrt (by positivity)]
      have h₆₁₀ : (Real.sqrt (b / a)) ^ 2 = b / a := by
        rw [Real.sq_sqrt (by positivity)]
      rw [h₆₉, h₆₁₀]
      have h₆₁₁ : Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := h₆₃
      nlinarith
    nlinarith
  
  have h₇ : a / b + b / a ≥ 2 := by
    linarith
  
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_25_left : ∀ (a b : ℝ), 0 < b ∧ b ≤ a → 1 / 8 * ((a - b) ^ 2 / a) ≤ (a + b) / 2 - Real.sqrt (a * b) := by
  intro a b h
  have h₁ : 0 < a := by
    linarith [h.1]
  
  have h₂ : 0 < b := by
    linarith [h.1]
  
  have h₃ : 0 ≤ Real.sqrt a := by
    exact Real.sqrt_nonneg a
  
  have h₄ : 0 ≤ Real.sqrt b := by
    exact Real.sqrt_nonneg b
  
  have h₅ : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 4 * a := by
    have h₅₁ : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
    have h₅₂ : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
      nlinarith [Real.sq_sqrt (le_of_lt h₁), Real.sq_sqrt (le_of_lt h₂),
        mul_self_nonneg (Real.sqrt a - Real.sqrt b)]
    rw [h₅₂]
    have h₅₃ : Real.sqrt (a * b) ≤ a := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [h.2]
    have h₅₄ : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
      rw [Real.sqrt_mul] <;> linarith
    have h₅₅ : a + b + 2 * (Real.sqrt a * Real.sqrt b) ≤ 4 * a := by
      nlinarith [h.2, Real.sqrt_nonneg (a * b), h₅₃, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a * b)]
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a * b)]
  
  have h₆ : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h₆₁ : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)) ^ 2 := by
      ring_nf
      <;> field_simp [pow_two]
      <;> ring_nf
    rw [h₆₁]
    have h₆₂ : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
      have h₆₂₁ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      have h₆₂₂ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
      nlinarith [Real.sq_sqrt (le_of_lt h₁), Real.sq_sqrt (le_of_lt h₂)]
    rw [h₆₂]
    <;> ring_nf
    <;> field_simp [pow_two]
    <;> ring_nf
  
  have h₇ : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
    have h₇₁ : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
      have h₇₂ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      have h₇₃ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
      have h₇₄ : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg (a * b)
      have h₇₅ : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul] <;> linarith
      calc
        (Real.sqrt a - Real.sqrt b) ^ 2 = (Real.sqrt a) ^ 2 + (Real.sqrt b) ^ 2 - 2 * (Real.sqrt a * Real.sqrt b) := by
          ring_nf
          <;>
          nlinarith
        _ = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
          have h₇₆ : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
          have h₇₇ : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
          rw [h₇₆, h₇₇]
          <;>
          ring_nf
        _ = a + b - 2 * Real.sqrt (a * b) := by
          have h₇₈ : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
            rw [Real.sqrt_mul] <;> linarith
          rw [h₇₈]
          <;>
          ring_nf
    have h₇₂ : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
      nlinarith [h₇₁]
    rw [h₇₂]
  
  have h₈ : (a + b) / 2 - Real.sqrt (a * b) - 1 / 8 * ((a - b) ^ 2 / a) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 * (1 - (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a)) := by
    have h₈₁ : (a + b) / 2 - Real.sqrt (a * b) - 1 / 8 * ((a - b) ^ 2 / a) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 - 1 / 8 * ((a - b) ^ 2 / a) := by
      rw [h₇]
    rw [h₈₁]
    have h₈₂ : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
      rw [h₆]
    have h₈₃ : 1 / 8 * ((a - b) ^ 2 / a) = 1 / 8 * (((Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2) / a) := by
      rw [h₈₂]
      <;> ring_nf
    rw [h₈₃]
    have h₈₄ : (Real.sqrt a - Real.sqrt b) ^ 2 / 2 - 1 / 8 * (((Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2) / a) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 * (1 - (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a)) := by
      have h₈₅ : 0 < a := by linarith
      field_simp [h₈₅.ne']
      <;> ring_nf
      <;> field_simp [h₈₅.ne']
      <;> ring_nf
      <;> nlinarith [Real.sq_sqrt (le_of_lt h₁), Real.sq_sqrt (le_of_lt h₂)]
    rw [h₈₄]
    <;> ring_nf
  
  have h₉ : 1 - (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a) ≥ 0 := by
    have h₉₁ : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 4 * a := h₅
    have h₉₂ : 0 < a := by linarith
    have h₉₃ : 0 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by positivity
    have h₉₄ : (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  
  have h₁₀ : (Real.sqrt a - Real.sqrt b) ^ 2 / 2 ≥ 0 := by
    have h₁₀₁ : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := by positivity
    have h₁₀₂ : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by positivity
    linarith
  
  have h₁₁ : (a + b) / 2 - Real.sqrt (a * b) - 1 / 8 * ((a - b) ^ 2 / a) ≥ 0 := by
    have h₁₁₁ : (a + b) / 2 - Real.sqrt (a * b) - 1 / 8 * ((a - b) ^ 2 / a) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 * (1 - (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a)) := by
      rw [h₈]
    rw [h₁₁₁]
    have h₁₁₂ : (Real.sqrt a - Real.sqrt b) ^ 2 / 2 ≥ 0 := h₁₀
    have h₁₁₃ : 1 - (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a) ≥ 0 := h₉
    have h₁₁₄ : (Real.sqrt a - Real.sqrt b) ^ 2 / 2 * (1 - (Real.sqrt a + Real.sqrt b) ^ 2 / (4 * a)) ≥ 0 := by
      nlinarith
    linarith
  
  have h₁₂ : 1 / 8 * ((a - b) ^ 2 / a) ≤ (a + b) / 2 - Real.sqrt (a * b) := by
    have h₁₂₁ : (a + b) / 2 - Real.sqrt (a * b) - 1 / 8 * ((a - b) ^ 2 / a) ≥ 0 := h₁₁
    linarith
  
  exact h₁₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_25_right : ∀ (a b : ℝ), 0 < b ∧ b ≤ a → (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := by
  have h₁ : ∀ (a b : ℝ), 0 < b → b ≤ a → (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
    intro a b hb hba
    have h₂ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₃ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₄ : 0 ≤ Real.sqrt a * Real.sqrt b := mul_nonneg h₂ h₃
    have h₅ : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul] <;> linarith
    have h₆ : (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
    calc
      (a + b) / 2 - Real.sqrt (a * b) = (a + b) / 2 - (Real.sqrt a * Real.sqrt b) := by rw [h₅]
      _ = (a + b - 2 * (Real.sqrt a * Real.sqrt b)) / 2 := by ring
      _ = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
        rw [h₆]
        <;> ring
        <;> field_simp
        <;> ring
  
  have h₂ : ∀ (a b : ℝ), 0 < b → b ≤ a → (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    intro a b hb hba
    have h₃ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₄ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₅ : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)) ^ 2 := by
      ring_nf
      <;>
      nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
    have h₆ : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
      have h₇ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      have h₈ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
      nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
    calc
      (a - b) ^ 2 = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b)) ^ 2 := by
        rw [h₆]
        <;>
        ring_nf
      _ = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
        rw [h₅]
        <;>
        ring_nf
        <;>
        nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith)]
  
  have h₃ : ∀ (a b : ℝ), 0 < b → b ≤ a → (Real.sqrt a + Real.sqrt b) ^ 2 ≥ 4 * b := by
    intro a b hb hba
    have h₄ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h₅ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have h₆ : Real.sqrt b ≥ 0 := Real.sqrt_nonneg b
    have h₇ : Real.sqrt a ≥ Real.sqrt b := by
      apply Real.sqrt_le_sqrt
      linarith
    have h₈ : Real.sqrt a + Real.sqrt b ≥ 2 * Real.sqrt b := by linarith
    have h₉ : (Real.sqrt a + Real.sqrt b) ^ 2 ≥ (2 * Real.sqrt b) ^ 2 := by
      gcongr
      <;> nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show 0 ≤ b by linarith)]
    have h₁₀ : (2 * Real.sqrt b) ^ 2 = 4 * b := by
      nlinarith [Real.sq_sqrt (show 0 ≤ b by linarith)]
    nlinarith
  
  have h₄ : ∀ (a b : ℝ), 0 < b → b ≤ a → (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ 1 / 2 := by
    intro a b hb hba
    have h₅ : (Real.sqrt a + Real.sqrt b) ^ 2 ≥ 4 * b := h₃ a b hb hba
    have h₆ : 0 < 8 * b := by positivity
    have h₇ : (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ (4 * b) / (8 * b) := by
      -- Use the fact that the numerator is at least 4b to bound the fraction from below
      have h₈ : (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ (4 * b) / (8 * b) := by
        -- Prove that (Real.sqrt a + Real.sqrt b)^2 / (8 * b) ≥ (4 * b) / (8 * b)
        have h₉ : 0 < 8 * b := by positivity
        have h₁₀ : 0 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by positivity
        have h₁₁ : 0 ≤ 4 * b := by positivity
        -- Use the division inequality to compare the two fractions
        rw [ge_iff_le]
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith
      linarith
    have h₈ : (4 * b) / (8 * b) = 1 / 2 := by
      -- Simplify the right-hand side to 1/2
      have h₉ : b ≠ 0 := by linarith
      field_simp [h₉]
      <;> ring_nf
      <;> field_simp [h₉]
      <;> linarith
    linarith
  
  have h₅ : ∀ (a b : ℝ), 0 < b → b ≤ a → (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
    intro a b hb hba
    have h₆ : (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ 1 / 2 := h₄ a b hb hba
    have h₇ : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
    have h₈ : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) = (Real.sqrt a - Real.sqrt b) ^ 2 * ((Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b)) := by
      ring
      <;> field_simp [hb.ne']
      <;> ring
    rw [h₈]
    have h₉ : (Real.sqrt a - Real.sqrt b) ^ 2 * ((Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b)) ≥ (Real.sqrt a - Real.sqrt b) ^ 2 * (1 / 2) := by
      have h₁₀ : (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ 1 / 2 := h₄ a b hb hba
      have h₁₁ : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
      nlinarith
    have h₁₀ : (Real.sqrt a - Real.sqrt b) ^ 2 * (1 / 2) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by ring
    linarith
  
  have h₆ : ∀ (a b : ℝ), 0 < b ∧ b ≤ a → (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := by
    intro a b h
    have h₇ : 0 < b := h.1
    have h₈ : b ≤ a := h.2
    have h₉ : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
      apply h₁
      <;> assumption
    have h₁₀ : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
      apply h₂
      <;> assumption
    have h₁₁ : (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) ≥ (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
      apply h₅
      <;> assumption
    have h₁₂ : (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := by
      calc
        (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by rw [h₉]
        _ ≤ (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 / (8 * b) := by
          -- Use the inequality from h₅ to bound the term
          linarith
        _ = ((Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2) / (8 * b) := by ring
        _ = ((a - b) ^ 2) / (8 * b) := by
          -- Substitute the expression for (a - b)^2 from h₂
          rw [h₁₀]
          <;> ring
          <;> field_simp [h₇.ne']
          <;> ring_nf
        _ = 1 / 8 * ((a - b) ^ 2 / b) := by
          -- Simplify the expression to match the desired form
          field_simp [h₇.ne']
          <;> ring_nf
          <;> field_simp [h₇.ne']
          <;> ring_nf
          <;> nlinarith
    exact h₁₂
  
  intro a b h
  have h₇ : (a + b) / 2 - Real.sqrt (a * b) ≤ 1 / 8 * ((a - b) ^ 2 / b) := h₆ a b h
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_26 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → (x + y) * (y + z) * (z + x) ≥ 8 * x * y * z := by
  intro x y z h
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < z := by linarith
  have h_main : (x + y) * (y + z) * (z + x) ≥ 8 * x * y * z := by
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    have h₇ : 0 < x * y * z := by positivity
    have h₈ : 0 < x * y * z * x := by positivity
    have h₉ : 0 < x * y * z * y := by positivity
    have h₁₀ : 0 < x * y * z * z := by positivity
    -- Use nlinarith to handle the inequality after expanding and simplifying
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x * y + y * z + z * x - 3 * x * y * z)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_27 : ∀ (x y z : ℝ), ¬ (x = y) ∧ ¬ (y = z) ∧ ¬ (x = z) → x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
  intro x y z h
  have h₁ : x ^ 2 + y ^ 2 ≥ 2 * x * y := by
    have h₁₀ : 0 ≤ (x - y) ^ 2 := by nlinarith
    nlinarith [h₁₀]
  
  have h₂ : y ^ 2 + z ^ 2 ≥ 2 * y * z := by
    have h₂₀ : 0 ≤ (y - z) ^ 2 := by nlinarith
    nlinarith [h₂₀]
  
  have h₃ : z ^ 2 + x ^ 2 ≥ 2 * z * x := by
    have h₃₀ : 0 ≤ (z - x) ^ 2 := by nlinarith
    nlinarith [h₃₀]
  
  have h₄ : 2 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * (x * y + y * z + z * x) := by
    have h₄₁ : 2 * (x ^ 2 + y ^ 2 + z ^ 2) = (x ^ 2 + y ^ 2) + (y ^ 2 + z ^ 2) + (z ^ 2 + x ^ 2) := by ring
    have h₄₂ : 2 * (x * y + y * z + z * x) = 2 * x * y + 2 * y * z + 2 * z * x := by ring
    rw [h₄₁, h₄₂]
    linarith [h₁, h₂, h₃]
  
  have h₅ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
    have h₅₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
      linarith
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_28 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x * y + y * z + z * x ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
  intro x y z h
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < z := by linarith
  have h₄ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
    have h₄₁ : 0 ≤ (y + z) / 2 := by positivity
    have h₄₂ : 0 ≤ y * z := by positivity
    have h₄₃ : (y + z) ^ 2 ≥ 4 * (y * z) := by
      nlinarith [sq_nonneg (y - z)]
    have h₄₄ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith
    exact h₄₄
  have h₅ : x * Real.sqrt (y * z) ≤ x * (y + z) / 2 := by
    have h₅₁ : x * Real.sqrt (y * z) ≤ x * ((y + z) / 2) := by
      -- Use the fact that sqrt(yz) ≤ (y + z)/2 and multiply both sides by x > 0
      have h₅₂ : Real.sqrt (y * z) ≤ (y + z) / 2 := h₄
      have h₅₃ : 0 < x := h₁
      have h₅₄ : 0 ≤ (y + z) / 2 := by positivity
      nlinarith
    -- Simplify the right side to match the desired form
    have h₅₅ : x * ((y + z) / 2) = x * (y + z) / 2 := by ring
    linarith
  
  have h₆ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
    have h₆₁ : 0 ≤ (z + x) / 2 := by positivity
    have h₆₂ : 0 ≤ z * x := by positivity
    have h₆₃ : (z + x) ^ 2 ≥ 4 * (z * x) := by
      nlinarith [sq_nonneg (z - x)]
    have h₆₄ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith
    exact h₆₄
  
  have h₇ : y * Real.sqrt (z * x) ≤ y * (z + x) / 2 := by
    have h₇₁ : y * Real.sqrt (z * x) ≤ y * ((z + x) / 2) := by
      -- Use the fact that sqrt(zx) ≤ (z + x)/2 and multiply both sides by y > 0
      have h₇₂ : Real.sqrt (z * x) ≤ (z + x) / 2 := h₆
      have h₇₃ : 0 < y := h₂
      have h₇₄ : 0 ≤ (z + x) / 2 := by positivity
      nlinarith
    -- Simplify the right side to match the desired form
    have h₇₅ : y * ((z + x) / 2) = y * (z + x) / 2 := by ring
    linarith
  
  have h₈ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    have h₈₁ : 0 ≤ (x + y) / 2 := by positivity
    have h₈₂ : 0 ≤ x * y := by positivity
    have h₈₃ : (x + y) ^ 2 ≥ 4 * (x * y) := by
      nlinarith [sq_nonneg (x - y)]
    have h₈₄ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith
    exact h₈₄
  
  have h₉ : z * Real.sqrt (x * y) ≤ z * (x + y) / 2 := by
    have h₉₁ : z * Real.sqrt (x * y) ≤ z * ((x + y) / 2) := by
      -- Use the fact that sqrt(xy) ≤ (x + y)/2 and multiply both sides by z > 0
      have h₉₂ : Real.sqrt (x * y) ≤ (x + y) / 2 := h₈
      have h₉₃ : 0 < z := h₃
      have h₉₄ : 0 ≤ (x + y) / 2 := by positivity
      nlinarith
    -- Simplify the right side to match the desired form
    have h₉₅ : z * ((x + y) / 2) = z * (x + y) / 2 := by ring
    linarith
  
  have h₁₀ : x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) ≤ x * (y + z) / 2 + y * (z + x) / 2 + z * (x + y) / 2 := by
    linarith [h₅, h₇, h₉]
  
  have h₁₁ : x * (y + z) / 2 + y * (z + x) / 2 + z * (x + y) / 2 = x * y + y * z + z * x := by
    have h₁₁₁ : x * (y + z) / 2 + y * (z + x) / 2 + z * (x + y) / 2 = (x * (y + z) + y * (z + x) + z * (x + y)) / 2 := by ring
    rw [h₁₁₁]
    have h₁₁₂ : (x * (y + z) + y * (z + x) + z * (x + y)) / 2 = (x * y + x * z + y * z + y * x + z * x + z * y) / 2 := by ring
    rw [h₁₁₂]
    have h₁₁₃ : (x * y + x * z + y * z + y * x + z * x + z * y) / 2 = x * y + y * z + z * x := by ring
    rw [h₁₁₃]
  
  have h₁₂ : x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) ≤ x * y + y * z + z * x := by
    linarith [h₁₀, h₁₁]
  
  have h₁₃ : x * y + y * z + z * x ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
    linarith [h₁₂]
  
  exact h₁₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_29 : ∀ (x y : ℝ), x ^ 2 + y ^ 2 + 1 ≥ x * y + x + y := by
  intro x y
  have h_main : x ^ 2 + y ^ 2 + 1 - (x * y + x + y) = (1 / 2 : ℝ) * ((x - y) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2) := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try ring_nf at *) <;>
    (try nlinarith)
    <;>
    (try
      {
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      })
    <;>
    (try
      {
        linarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      })
  
  have h_final : x ^ 2 + y ^ 2 + 1 ≥ x * y + x + y := by
    have h1 : (1 / 2 : ℝ) * ((x - y) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2) ≥ 0 := by
      have h2 : (x - y) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      have h3 : (1 / 2 : ℝ) ≥ 0 := by norm_num
      nlinarith
    have h4 : x ^ 2 + y ^ 2 + 1 - (x * y + x + y) ≥ 0 := by
      linarith
    linarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_30 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → 1 / x + 1 / y + 1 / z ≥ 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) := by
  intro x y z h
  have h₁ : 1 / Real.sqrt (x * y) ≤ (1 / x + 1 / y) / 2 := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have hxy : 0 < x * y := by positivity
    have h₂ : 0 < Real.sqrt (x * y) := Real.sqrt_pos.mpr hxy
    have h₃ : 0 < 1 / x := by positivity
    have h₄ : 0 < 1 / y := by positivity
    have h₅ : 0 < 1 / x + 1 / y := by positivity
    -- Use the AM-GM inequality to show that (1/x + 1/y)/2 ≥ 1/sqrt(xy)
    have h₆ : Real.sqrt (x * y) ≥ 2 * x * y / (x + y) := by
      -- Prove that sqrt(xy) ≥ 2xy / (x + y)
      have h₇ : 0 < x + y := by positivity
      have h₈ : 0 < x * y := by positivity
      have h₉ : 0 < x * y * (x + y) := by positivity
      -- Use the fact that sqrt(xy) ≥ 2xy / (x + y)
      have h₁₀ : Real.sqrt (x * y) ≥ 2 * x * y / (x + y) := by
        apply Real.le_sqrt_of_sq_le
        field_simp [h₇.ne']
        rw [div_le_iff (by positivity)]
        nlinarith [sq_nonneg (x - y)]
      linarith
    -- Use the inequality to show that 1/sqrt(xy) ≤ (1/x + 1/y)/2
    have h₇ : 1 / Real.sqrt (x * y) ≤ (1 / x + 1 / y) / 2 := by
      have h₈ : 1 / Real.sqrt (x * y) ≤ 1 / (2 * x * y / (x + y)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      have h₉ : 1 / (2 * x * y / (x + y)) = (x + y) / (2 * x * y) := by
        field_simp [hx.ne', hy.ne']
        <;> ring
        <;> field_simp [hx.ne', hy.ne']
        <;> ring
      have h₁₀ : (x + y) / (2 * x * y) = (1 / x + 1 / y) / 2 := by
        field_simp [hx.ne', hy.ne']
        <;> ring
        <;> field_simp [hx.ne', hy.ne']
        <;> ring
      have h₁₁ : 1 / (2 * x * y / (x + y)) = (1 / x + 1 / y) / 2 := by
        rw [h₉, h₁₀]
      linarith
    exact h₇
  
  have h₂ : 1 / Real.sqrt (y * z) ≤ (1 / y + 1 / z) / 2 := by
    have hy : 0 < y := by linarith
    have hz : 0 < z := by linarith
    have hyz : 0 < y * z := by positivity
    have h₂ : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr hyz
    have h₃ : 0 < 1 / y := by positivity
    have h₄ : 0 < 1 / z := by positivity
    have h₅ : 0 < 1 / y + 1 / z := by positivity
    -- Use the AM-GM inequality to show that (1/y + 1/z)/2 ≥ 1/sqrt(yz)
    have h₆ : Real.sqrt (y * z) ≥ 2 * y * z / (y + z) := by
      -- Prove that sqrt(yz) ≥ 2yz / (y + z)
      have h₇ : 0 < y + z := by positivity
      have h₈ : 0 < y * z := by positivity
      have h₉ : 0 < y * z * (y + z) := by positivity
      -- Use the fact that sqrt(yz) ≥ 2yz / (y + z)
      have h₁₀ : Real.sqrt (y * z) ≥ 2 * y * z / (y + z) := by
        apply Real.le_sqrt_of_sq_le
        field_simp [h₇.ne']
        rw [div_le_iff (by positivity)]
        nlinarith [sq_nonneg (y - z)]
      linarith
    -- Use the inequality to show that 1/sqrt(yz) ≤ (1/y + 1/z)/2
    have h₇ : 1 / Real.sqrt (y * z) ≤ (1 / y + 1 / z) / 2 := by
      have h₈ : 1 / Real.sqrt (y * z) ≤ 1 / (2 * y * z / (y + z)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      have h₉ : 1 / (2 * y * z / (y + z)) = (y + z) / (2 * y * z) := by
        field_simp [hy.ne', hz.ne']
        <;> ring
        <;> field_simp [hy.ne', hz.ne']
        <;> ring
      have h₁₀ : (y + z) / (2 * y * z) = (1 / y + 1 / z) / 2 := by
        field_simp [hy.ne', hz.ne']
        <;> ring
        <;> field_simp [hy.ne', hz.ne']
        <;> ring
      have h₁₁ : 1 / (2 * y * z / (y + z)) = (1 / y + 1 / z) / 2 := by
        rw [h₉, h₁₀]
      linarith
    exact h₇
  
  have h₃ : 1 / Real.sqrt (z * x) ≤ (1 / z + 1 / x) / 2 := by
    have hz : 0 < z := by linarith
    have hx : 0 < x := by linarith
    have hzx : 0 < z * x := by positivity
    have h₂ : 0 < Real.sqrt (z * x) := Real.sqrt_pos.mpr hzx
    have h₃ : 0 < 1 / z := by positivity
    have h₄ : 0 < 1 / x := by positivity
    have h₅ : 0 < 1 / z + 1 / x := by positivity
    -- Use the AM-GM inequality to show that (1/z + 1/x)/2 ≥ 1/sqrt(zx)
    have h₆ : Real.sqrt (z * x) ≥ 2 * z * x / (z + x) := by
      -- Prove that sqrt(zx) ≥ 2zx / (z + x)
      have h₇ : 0 < z + x := by positivity
      have h₈ : 0 < z * x := by positivity
      have h₉ : 0 < z * x * (z + x) := by positivity
      -- Use the fact that sqrt(zx) ≥ 2zx / (z + x)
      have h₁₀ : Real.sqrt (z * x) ≥ 2 * z * x / (z + x) := by
        apply Real.le_sqrt_of_sq_le
        field_simp [h₇.ne']
        rw [div_le_iff (by positivity)]
        nlinarith [sq_nonneg (z - x)]
      linarith
    -- Use the inequality to show that 1/sqrt(zx) ≤ (1/z + 1/x)/2
    have h₇ : 1 / Real.sqrt (z * x) ≤ (1 / z + 1 / x) / 2 := by
      have h₈ : 1 / Real.sqrt (z * x) ≤ 1 / (2 * z * x / (z + x)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      have h₉ : 1 / (2 * z * x / (z + x)) = (z + x) / (2 * z * x) := by
        field_simp [hz.ne', hx.ne']
        <;> ring
        <;> field_simp [hz.ne', hx.ne']
        <;> ring
      have h₁₀ : (z + x) / (2 * z * x) = (1 / z + 1 / x) / 2 := by
        field_simp [hz.ne', hx.ne']
        <;> ring
        <;> field_simp [hz.ne', hx.ne']
        <;> ring
      have h₁₁ : 1 / (2 * z * x / (z + x)) = (1 / z + 1 / x) / 2 := by
        rw [h₉, h₁₀]
      linarith
    exact h₇
  
  have h₄ : 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) ≤ 1 / x + 1 / y + 1 / z := by
    have h₅ : 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) ≤ (1 / x + 1 / y) / 2 + (1 / y + 1 / z) / 2 + (1 / z + 1 / x) / 2 := by
      linarith
    have h₆ : (1 / x + 1 / y) / 2 + (1 / y + 1 / z) / 2 + (1 / z + 1 / x) / 2 = 1 / x + 1 / y + 1 / z := by
      ring
    linarith
  
  have h₅ : 1 / x + 1 / y + 1 / z ≥ 1 / Real.sqrt (x * y) + 1 / Real.sqrt (y * z) + 1 / Real.sqrt (z * x) := by
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_31 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x * y / z + y * z / x + z * x / y ≥ x + y + z := by
  intro x y z h
  have h₁ : x * y / z + y * z / x ≥ 2 * y := by
    have h₁₁ : 0 < x := by linarith
    have h₁₂ : 0 < y := by linarith
    have h₁₃ : 0 < z := by linarith
    have h₁₄ : 0 < x * z := by positivity
    have h₁₅ : 0 < x * z * y := by positivity
    field_simp [h₁₁.ne', h₁₃.ne']
    rw [le_div_iff (by positivity)]
    -- Use nlinarith to prove the inequality after simplification
    nlinarith [sq_nonneg (x - z), sq_nonneg (x + z), sq_nonneg (x - z + x + z),
      sq_nonneg (x - z - (x + z))]
  
  have h₂ : x * y / z + z * x / y ≥ 2 * x := by
    have h₂₁ : 0 < x := by linarith
    have h₂₂ : 0 < y := by linarith
    have h₂₃ : 0 < z := by linarith
    have h₂₄ : 0 < y * z := by positivity
    have h₂₅ : 0 < y * z * x := by positivity
    field_simp [h₂₁.ne', h₂₂.ne']
    rw [le_div_iff (by positivity)]
    -- Use nlinarith to prove the inequality after simplification
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), sq_nonneg (y - z + y + z),
      sq_nonneg (y - z - (y + z))]
  
  have h₃ : y * z / x + z * x / y ≥ 2 * z := by
    have h₃₁ : 0 < x := by linarith
    have h₃₂ : 0 < y := by linarith
    have h₃₃ : 0 < z := by linarith
    have h₃₄ : 0 < x * y := by positivity
    have h₃₅ : 0 < x * y * z := by positivity
    field_simp [h₃₁.ne', h₃₂.ne']
    rw [le_div_iff (by positivity)]
    -- Use nlinarith to prove the inequality after simplification
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + x + y),
      sq_nonneg (x - y - (x + y))]
  
  have h₄ : 2 * (x * y / z + y * z / x + z * x / y) ≥ 2 * (x + y + z) := by
    have h₄₁ : 2 * (x * y / z + y * z / x + z * x / y) = (x * y / z + y * z / x) + (x * y / z + z * x / y) + (y * z / x + z * x / y) := by
      ring
    rw [h₄₁]
    linarith [h₁, h₂, h₃]
  
  have h₅ : x * y / z + y * z / x + z * x / y ≥ x + y + z := by
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_32 : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * Real.sqrt (y ^ 2 + z ^ 2) + y * Real.sqrt (x ^ 2 + z ^ 2) := by
  intro x y z
  have h₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ 2 * x * Real.sqrt (y ^ 2 + z ^ 2) := by
    have h₁₀ : 0 ≤ (x - Real.sqrt (y ^ 2 + z ^ 2)) ^ 2 := by nlinarith
    have h₁₁ : (x - Real.sqrt (y ^ 2 + z ^ 2)) ^ 2 = x ^ 2 + (y ^ 2 + z ^ 2) - 2 * x * Real.sqrt (y ^ 2 + z ^ 2) := by
      have h₁₂ : 0 ≤ y ^ 2 + z ^ 2 := by nlinarith
      have h₁₃ : 0 ≤ Real.sqrt (y ^ 2 + z ^ 2) := Real.sqrt_nonneg (y ^ 2 + z ^ 2)
      nlinarith [Real.sq_sqrt (show 0 ≤ y ^ 2 + z ^ 2 by nlinarith)]
    rw [h₁₁] at h₁₀
    nlinarith [Real.sqrt_nonneg (y ^ 2 + z ^ 2)]
  
  have h₂ : x ^ 2 + y ^ 2 + z ^ 2 ≥ 2 * y * Real.sqrt (x ^ 2 + z ^ 2) := by
    have h₂₀ : 0 ≤ (y - Real.sqrt (x ^ 2 + z ^ 2)) ^ 2 := by nlinarith
    have h₂₁ : (y - Real.sqrt (x ^ 2 + z ^ 2)) ^ 2 = y ^ 2 + (x ^ 2 + z ^ 2) - 2 * y * Real.sqrt (x ^ 2 + z ^ 2) := by
      have h₂₂ : 0 ≤ x ^ 2 + z ^ 2 := by nlinarith
      have h₂₃ : 0 ≤ Real.sqrt (x ^ 2 + z ^ 2) := Real.sqrt_nonneg (x ^ 2 + z ^ 2)
      nlinarith [Real.sq_sqrt (show 0 ≤ x ^ 2 + z ^ 2 by nlinarith)]
    rw [h₂₁] at h₂₀
    nlinarith [Real.sqrt_nonneg (x ^ 2 + z ^ 2)]
  
  have h₃ : 2 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * x * Real.sqrt (y ^ 2 + z ^ 2) + 2 * y * Real.sqrt (x ^ 2 + z ^ 2) := by
    have h₃₁ : 2 * (x ^ 2 + y ^ 2 + z ^ 2) = (x ^ 2 + y ^ 2 + z ^ 2) + (x ^ 2 + y ^ 2 + z ^ 2) := by ring
    rw [h₃₁]
    nlinarith [h₁, h₂]
  
  have h₄ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * Real.sqrt (y ^ 2 + z ^ 2) + y * Real.sqrt (x ^ 2 + z ^ 2) := by
    have h₄₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * Real.sqrt (y ^ 2 + z ^ 2) + y * Real.sqrt (x ^ 2 + z ^ 2) := by
      have h₄₂ : 2 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * x * Real.sqrt (y ^ 2 + z ^ 2) + 2 * y * Real.sqrt (x ^ 2 + z ^ 2) := h₃
      have h₄₃ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * Real.sqrt (y ^ 2 + z ^ 2) + y * Real.sqrt (x ^ 2 + z ^ 2) := by
        linarith
      exact h₄₃
    exact h₄₁
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_33 : ∀ (x y : ℝ), x ^ 4 + y ^ 4 + 8 ≥ 8 * x * y := by
  intro x y
  have h₁ : x ^ 4 + 4 ≥ 4 * x ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 + 2), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  
  have h₂ : y ^ 4 + 4 ≥ 4 * y ^ 2 := by
    nlinarith [sq_nonneg (y ^ 2 - 2), sq_nonneg (y ^ 2 + 2), sq_nonneg (y - 1), sq_nonneg (y + 1)]
  
  have h₃ : x ^ 4 + y ^ 4 + 8 ≥ 4 * x ^ 2 + 4 * y ^ 2 := by
    linarith [h₁, h₂]
  
  have h₄ : 4 * x ^ 2 + 4 * y ^ 2 ≥ 8 * x * y := by
    have h₄₁ : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    nlinarith [sq_nonneg (x + y)]
  
  have h₅ : x ^ 4 + y ^ 4 + 8 ≥ 8 * x * y := by
    linarith [h₃, h₄]
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_34 : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 := by
  intro a b c d h
  have h₁ : ∀ (x y : ℝ), x > 0 → y > 0 → x / y + y / x ≥ 2 := by
    intro x y hx hy
    have h₂ : 0 < x * y := mul_pos hx hy
    have h₃ : 0 < x ^ 2 := pow_pos hx 2
    have h₄ : 0 < y ^ 2 := pow_pos hy 2
    field_simp [hx.ne', hy.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (x - y)]
  
  have h₂ : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) = 4 + (a / b + b / a) + (a / c + c / a) + (a / d + d / a) + (b / c + c / b) + (b / d + d / b) + (c / d + d / c) := by
    have ha : a > 0 := h.1
    have hb : b > 0 := h.2.1
    have hc : c > 0 := h.2.2.1
    have hd : d > 0 := h.2.2.2
    have h₃ : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) = 4 + (a / b + b / a) + (a / c + c / a) + (a / d + d / a) + (b / c + c / b) + (b / d + d / b) + (c / d + d / c) := by
      have h₄ : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) = (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) := rfl
      calc
        (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) = (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) := rfl
        _ = 4 + (a / b + b / a) + (a / c + c / a) + (a / d + d / a) + (b / c + c / b) + (b / d + d / b) + (c / d + d / c) := by
          field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
          ring
          <;>
            simp_all [ha.ne', hb.ne', hc.ne', hd.ne']
          <;>
            ring_nf
          <;>
            field_simp [ha.ne', hb.ne', hc.ne', hd.ne']
          <;>
            ring_nf
          <;>
            linarith
    exact h₃
  
  have h₃ : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 := by
    have ha : a > 0 := h.1
    have hb : b > 0 := h.2.1
    have hc : c > 0 := h.2.2.1
    have hd : d > 0 := h.2.2.2
    have h₄ : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) = 4 + (a / b + b / a) + (a / c + c / a) + (a / d + d / a) + (b / c + c / b) + (b / d + d / b) + (c / d + d / c) := h₂
    have h₅ : a / b + b / a ≥ 2 := h₁ a b ha hb
    have h₆ : a / c + c / a ≥ 2 := h₁ a c ha hc
    have h₇ : a / d + d / a ≥ 2 := h₁ a d ha hd
    have h₈ : b / c + c / b ≥ 2 := h₁ b c hb hc
    have h₉ : b / d + d / b ≥ 2 := h₁ b d hb hd
    have h₁₀ : c / d + d / c ≥ 2 := h₁ c d hc hd
    have h₁₁ : 4 + (a / b + b / a) + (a / c + c / a) + (a / d + d / a) + (b / c + c / b) + (b / d + d / b) + (c / d + d / c) ≥ 16 := by
      linarith
    linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_35 : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → a / b + b / c + c / d + d / a ≥ 4 := by
  intro a b c d h_pos
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < d := by linarith
  set w₁ := a / b with hw₁_def
  set w₂ := b / c with hw₂_def
  set w₃ := c / d with hw₃_def
  set w₄ := d / a with hw₄_def
  have h_w₁_pos : 0 < w₁ := by
    rw [hw₁_def]
    exact div_pos h₁ h₂
  have h_w₂_pos : 0 < w₂ := by
    rw [hw₂_def]
    exact div_pos h₂ h₃
  have h_w₃_pos : 0 < w₃ := by
    rw [hw₃_def]
    exact div_pos h₃ h₄
  have h_w₄_pos : 0 < w₄ := by
    rw [hw₄_def]
    exact div_pos h₄ h₁
  have h_product : w₁ * w₂ * w₃ * w₄ = 1 := by
    calc
      w₁ * w₂ * w₃ * w₄ = (a / b) * (b / c) * (c / d) * (d / a) := by
        simp [hw₁_def, hw₂_def, hw₃_def, hw₄_def]
        <;> ring_nf
      _ = 1 := by
        have h₅ : a ≠ 0 := by linarith
        have h₆ : b ≠ 0 := by linarith
        have h₇ : c ≠ 0 := by linarith
        have h₈ : d ≠ 0 := by linarith
        field_simp [h₅, h₆, h₇, h₈]
        <;> ring_nf
        <;> field_simp [h₅, h₆, h₇, h₈]
        <;> linarith
  have h_sum_nonneg : 0 ≤ (w₁ + w₂ + w₃ + w₄) / 4 := by
    have h₅ : 0 ≤ w₁ := by linarith
    have h₆ : 0 ≤ w₂ := by linarith
    have h₇ : 0 ≤ w₃ := by linarith
    have h₈ : 0 ≤ w₄ := by linarith
    linarith
  have h_am_gm : (w₁ * w₂ * w₃ * w₄ : ℝ) ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := by
    have h₅ : 0 ≤ w₁ := by linarith
    have h₆ : 0 ≤ w₂ := by linarith
    have h₇ : 0 ≤ w₃ := by linarith
    have h₈ : 0 ≤ w₄ := by linarith
    -- Use the AM-GM inequality for four variables
    have h₉ : w₁ * w₂ * w₃ * w₄ ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := by
      -- Apply the AM-GM inequality
      nlinarith [sq_nonneg (w₁ - w₂), sq_nonneg (w₁ - w₃), sq_nonneg (w₁ - w₄), sq_nonneg (w₂ - w₃), sq_nonneg (w₂ - w₄), sq_nonneg (w₃ - w₄),
        mul_nonneg h₅ h₆, mul_nonneg h₅ h₇, mul_nonneg h₅ h₈, mul_nonneg h₆ h₇, mul_nonneg h₆ h₈, mul_nonneg h₇ h₈]
    -- Convert the product to real numbers and use the result
    norm_cast at h₉ ⊢
    <;> linarith
  have h_one_le_pow : (1 : ℝ) ^ 4 ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := by
    have h₅ : (w₁ * w₂ * w₃ * w₄ : ℝ) = 1 := by
      norm_cast
      <;> simp_all [h_product]
      <;> ring_nf at *
      <;> linarith
    have h₆ : (w₁ * w₂ * w₃ * w₄ : ℝ) ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := h_am_gm
    have h₇ : (1 : ℝ) ^ 4 ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := by
      calc
        (1 : ℝ) ^ 4 = (1 : ℝ) := by norm_num
        _ ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := by
          have h₈ : (w₁ * w₂ * w₃ * w₄ : ℝ) = 1 := by
            norm_cast
            <;> simp_all [h_product]
            <;> ring_nf at *
            <;> linarith
          have h₉ : (w₁ * w₂ * w₃ * w₄ : ℝ) ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := h_am_gm
          linarith
    exact h₇
  have h_one_le_sum_div_four : (1 : ℝ) ≤ (w₁ + w₂ + w₃ + w₄) / 4 := by
    have h₅ : 0 ≤ (w₁ + w₂ + w₃ + w₄) / 4 := h_sum_nonneg
    have h₆ : (1 : ℝ) ^ 4 ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := h_one_le_pow
    -- Use the fact that the function x^4 is strictly increasing for x ≥ 0 to deduce 1 ≤ (w₁ + w₂ + w₃ + w₄) / 4
    have h₇ : (1 : ℝ) ≤ (w₁ + w₂ + w₃ + w₄) / 4 := by
      by_contra h
      -- If (w₁ + w₂ + w₃ + w₄) / 4 < 1, then ((w₁ + w₂ + w₃ + w₄) / 4)^4 < 1
      have h₈ : (w₁ + w₂ + w₃ + w₄) / 4 < 1 := by linarith
      have h₉ : 0 ≤ (w₁ + w₂ + w₃ + w₄) / 4 := h_sum_nonneg
      have h₁₀ : ((w₁ + w₂ + w₃ + w₄) / 4 : ℝ) ^ 4 < 1 := by
        have h₁₁ : 0 ≤ (w₁ + w₂ + w₃ + w₄) / 4 := h_sum_nonneg
        have h₁₂ : (w₁ + w₂ + w₃ + w₄) / 4 < 1 := h₈
        have h₁₃ : ((w₁ + w₂ + w₃ + w₄) / 4 : ℝ) ^ 4 < 1 := by
          exact pow_lt_one (by linarith) (by linarith) (by norm_num)
        exact h₁₃
      have h₁₁ : (1 : ℝ) ^ 4 ≤ ((w₁ + w₂ + w₃ + w₄) / 4) ^ 4 := h_one_le_pow
      linarith
    exact h₇
  have h_main : w₁ + w₂ + w₃ + w₄ ≥ 4 := by
    have h₅ : (1 : ℝ) ≤ (w₁ + w₂ + w₃ + w₄) / 4 := h_one_le_sum_div_four
    have h₆ : (w₁ + w₂ + w₃ + w₄ : ℝ) ≥ 4 := by
      linarith
    exact_mod_cast h₆
  have h_final : a / b + b / c + c / d + d / a ≥ 4 := by
    calc
      a / b + b / c + c / d + d / a = w₁ + w₂ + w₃ + w₄ := by
        simp [hw₁_def, hw₂_def, hw₃_def, hw₄_def]
        <;> ring_nf
      _ ≥ 4 := h_main
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_39 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ (1 + a) * (1 + b) * (1 + c) = 8 → a * b * c ≤ 1 := by
  have h₀ : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ (1 + a) * (1 + b) * (1 + c) = 8 → a * b * c ≤ 1 := by
    intro a b c h
    have h₁ : a > 0 := by linarith
    have h₂ : b > 0 := by linarith
    have h₃ : c > 0 := by linarith
    have h₄ : (1 + a) * (1 + b) * (1 + c) = 8 := by linarith
    have h₅ : a * b * c ≤ 1 := by
      -- Use the AM-GM inequality to prove the desired inequality
      have h₆ : 0 < a * b := by positivity
      have h₇ : 0 < a * c := by positivity
      have h₈ : 0 < b * c := by positivity
      have h₉ : 0 < a * b * c := by positivity
      -- Expand the product (1 + a)(1 + b)(1 + c)
      have h₁₀ : (1 + a) * (1 + b) * (1 + c) = 1 + a + b + c + (a * b + a * c + b * c) + a * b * c := by
        ring
      rw [h₁₀] at h₄
      -- Use non-linear arithmetic to prove the inequality
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1)]
    exact h₅
  exact h₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_40 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a ^ 3 / b + b ^ 3 / c + c ^ 3 / a ≥ a * b + b * c + c * a := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a ^ 3 / b + a * b ≥ 2 * a ^ 2 := by
    have h₄₁ : 0 < a * b := mul_pos h₁ h₂
    have h₄₂ : 0 < a ^ 2 := pow_pos h₁ 2
    have h₄₃ : 0 < b := h₂
    have h₄₄ : 0 < a ^ 3 := pow_pos h₁ 3
    field_simp [h₂.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b)]
  
  have h₅ : b ^ 3 / c + b * c ≥ 2 * b ^ 2 := by
    have h₅₁ : 0 < b * c := mul_pos h₂ h₃
    have h₅₂ : 0 < b ^ 2 := pow_pos h₂ 2
    have h₅₃ : 0 < c := h₃
    have h₅₄ : 0 < b ^ 3 := pow_pos h₂ 3
    field_simp [h₃.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b + c)]
  
  have h₆ : c ^ 3 / a + c * a ≥ 2 * c ^ 2 := by
    have h₆₁ : 0 < c * a := mul_pos h₃ h₁
    have h₆₂ : 0 < c ^ 2 := pow_pos h₃ 2
    have h₆₃ : 0 < a := h₁
    have h₆₄ : 0 < c ^ 3 := pow_pos h₃ 3
    field_simp [h₁.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c + a)]
  
  have h₇ : a ^ 3 / b + b ^ 3 / c + c ^ 3 / a + (a * b + b * c + c * a) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h₇₁ : a ^ 3 / b + a * b ≥ 2 * a ^ 2 := h₄
    have h₇₂ : b ^ 3 / c + b * c ≥ 2 * b ^ 2 := h₅
    have h₇₃ : c ^ 3 / a + c * a ≥ 2 * c ^ 2 := h₆
    have h₇₄ : a ^ 3 / b + b ^ 3 / c + c ^ 3 / a + (a * b + b * c + c * a) = (a ^ 3 / b + a * b) + (b ^ 3 / c + b * c) + (c ^ 3 / a + c * a) := by
      ring
    rw [h₇₄]
    linarith
  
  have h₈ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₈₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₉ : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := by
    have h₉₁ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := h₈
    nlinarith
  
  have h₁₀ : a ^ 3 / b + b ^ 3 / c + c ^ 3 / a + (a * b + b * c + c * a) ≥ 2 * (a * b + b * c + c * a) := by
    have h₁₀₁ : a ^ 3 / b + b ^ 3 / c + c ^ 3 / a + (a * b + b * c + c * a) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := h₇
    have h₁₀₂ : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a) := h₉
    linarith
  
  have h₁₁ : a ^ 3 / b + b ^ 3 / c + c ^ 3 / a ≥ a * b + b * c + c * a := by
    have h₁₁₁ : a ^ 3 / b + b ^ 3 / c + c ^ 3 / a + (a * b + b * c + c * a) ≥ 2 * (a * b + b * c + c * a) := h₁₀
    linarith
  
  exact h₁₁

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
      mul_nonneg h.1 h.2.1, mul_nonneg h.2.1 h.2.2, mul_nonneg h.2.2 h.1,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg c), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg a),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg b)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_42 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 < b * c := by positivity
  have h₆ : 0 < c * a := by positivity
  have h₇ : 0 < a * b * c := by positivity
  have h₈ : 0 < a ^ 2 * b := by positivity
  have h₉ : 0 < b ^ 2 * c := by positivity
  have h₁₀ : 0 < c ^ 2 * a := by positivity
  have h₁₁ : 0 < a * b ^ 2 := by positivity
  have h₁₂ : 0 < b * c ^ 2 := by positivity
  have h₁₃ : 0 < c * a ^ 2 := by positivity
  have h₁₄ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
      sq_nonneg (a * b ^ 2 - b * c ^ 2), sq_nonneg (b * c ^ 2 - c * a ^ 2), sq_nonneg (c * a ^ 2 - a * b ^ 2),
      mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b))]
  exact h₁₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_43 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + a * c) / (1 + c) ≥ 3 := by
  intro a b c h
  have h₁ : (1 + a * b) / (1 + a) + (1 + b * c) / (1 + b) + (1 + a * c) / (1 + c) ≥ 3 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < c := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < a * c := by positivity
    have h₈ : 0 < a * b * c := by positivity
    -- Use the substitution x = 1, y = 1, z = 1 to find that the minimum is achieved when a = b = c = 1
    -- However, we will directly use AM-GM inequality to prove the desired inequality
    have h₉ : 0 < 1 + a := by linarith
    have h₁₀ : 0 < 1 + b := by linarith
    have h₁₁ : 0 < 1 + c := by linarith
    have h₁₂ : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
    field_simp [h₉.ne', h₁₀.ne', h₁₁.ne']
    rw [le_div_iff (by positivity)]
    -- Expand and simplify the inequality to a polynomial form
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₄.le, mul_nonneg h₄.le h₂.le,
      mul_nonneg (sq_nonneg (a - 1)) h₄.le, mul_nonneg (sq_nonneg (b - 1)) h₂.le,
      mul_nonneg (sq_nonneg (c - 1)) h₃.le, mul_nonneg (sq_nonneg (a - 1)) h₃.le,
      mul_nonneg (sq_nonneg (b - 1)) h₄.le, mul_nonneg (sq_nonneg (c - 1)) h₂.le,
      mul_nonneg (sq_nonneg (a - 1)) (mul_nonneg h₃.le h₄.le),
      mul_nonneg (sq_nonneg (b - 1)) (mul_nonneg h₂.le h₄.le),
      mul_nonneg (sq_nonneg (c - 1)) (mul_nonneg h₂.le h₃.le)]
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_50 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_pos h₁ h₂, mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂)]
  
  have h₅ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    have h₅₁ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b) + a * b * c := by linarith
    have h₅₂ : a * b * (a + b) + a * b * c = a * b * (a + b + c) := by ring
    linarith
  
  have h₆ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₆₁ : 0 < a * b * (a + b + c) := by positivity
    have h₆₂ : 0 < a ^ 3 + b ^ 3 + a * b * c := by positivity
    have h₆₃ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := h₅
    have h₆₄ : 0 < a * b * (a + b + c) := by positivity
    have h₆₅ : 0 < a ^ 3 + b ^ 3 + a * b * c := by positivity
    -- Use the fact that if x ≥ y > 0, then 1/x ≤ 1/y
    have h₆₆ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₆₆
  
  have h₇ : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
    nlinarith [sq_nonneg (b - c), mul_pos h₂ h₃, mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃)]
  
  have h₈ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    have h₈₁ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (b + c) + a * b * c := by linarith
    have h₈₂ : b * c * (b + c) + a * b * c = b * c * (a + b + c) := by ring
    linarith
  
  have h₉ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₉₁ : 0 < b * c * (a + b + c) := by positivity
    have h₉₂ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₉₃ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := h₈
    have h₉₄ : 0 < b * c * (a + b + c) := by positivity
    have h₉₅ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    -- Use the fact that if x ≥ y > 0, then 1/x ≤ 1/y
    have h₉₆ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₉₆
  
  have h₁₀ : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := by
    nlinarith [sq_nonneg (c - a), mul_pos h₃ h₁, mul_pos (sq_pos_of_pos h₃) (sq_pos_of_pos h₁)]
  
  have h₁₁ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    have h₁₁₁ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (c + a) + a * b * c := by linarith
    have h₁₁₂ : c * a * (c + a) + a * b * c = c * a * (a + b + c) := by ring
    linarith
  
  have h₁₂ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    have h₁₂₁ : 0 < c * a * (a + b + c) := by positivity
    have h₁₂₂ : 0 < c ^ 3 + a ^ 3 + a * b * c := by positivity
    have h₁₂₃ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := h₁₁
    have h₁₂₄ : 0 < c * a * (a + b + c) := by positivity
    have h₁₂₅ : 0 < c ^ 3 + a ^ 3 + a * b * c := by positivity
    -- Use the fact that if x ≥ y > 0, then 1/x ≤ 1/y
    have h₁₂₆ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₂₆
  
  have h₁₃ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    have h₁₃₁ : 0 < a * b * c := by positivity
    have h₁₃₂ : 0 < a + b + c := by positivity
    have h₁₃₃ : 0 < a * b * (a + b + c) := by positivity
    have h₁₃₄ : 0 < b * c * (a + b + c) := by positivity
    have h₁₃₅ : 0 < c * a * (a + b + c) := by positivity
    have h₁₃₆ : 0 < a * b * c * (a + b + c) := by positivity
    have h₁₃₇ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = (c + a + b) / (a * b * c * (a + b + c)) := by
      field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₃.ne', h₁₃₄.ne', h₁₃₅.ne']
      <;> ring_nf
      <;> field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₃.ne', h₁₃₄.ne', h₁₃₅.ne']
      <;> ring_nf
      <;> nlinarith [h₁, h₂, h₃]
    have h₁₃₈ : (c + a + b) / (a * b * c * (a + b + c)) = 1 / (a * b * c) := by
      have h₁₃₉ : (c + a + b) / (a * b * c * (a + b + c)) = (a + b + c) / (a * b * c * (a + b + c)) := by
        ring_nf
        <;> field_simp [h₁₃₁.ne', h₁₃₂.ne']
        <;> ring_nf
        <;> nlinarith [h₁, h₂, h₃]
      rw [h₁₃₉]
      have h₁₄₀ : (a + b + c) / (a * b * c * (a + b + c)) = 1 / (a * b * c) := by
        have h₁₄₁ : a + b + c ≠ 0 := by linarith
        have h₁₄₂ : a * b * c ≠ 0 := by positivity
        field_simp [h₁₄₁, h₁₄₂]
        <;> ring_nf
        <;> field_simp [h₁₄₁, h₁₄₂]
        <;> nlinarith [h₁, h₂, h₃]
      rw [h₁₄₀]
    rw [h₁₃₇, h₁₃₈]
  
  have h₁₄ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    have h₁₄₁ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
      linarith [h₆, h₉, h₁₂]
    have h₁₄₂ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
      exact h₁₃
    linarith
  
  exact h₁₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_51 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → (1 / a + 1) * (1 / b + 1) * (1 / c + 1) ≥ 64 := by
  intro a b c h
  have h₁ : 1 / a + 1 / b + 1 / c ≥ 9 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < c := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < a * c := by positivity
    have h₇ : 0 < b * c := by positivity
    have h₈ : a + b + c = 1 := by linarith
    field_simp [h₂.ne', h₃.ne', h₄.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos h₂ h₃, mul_pos h₂ h₄, mul_pos h₃ h₄]
  
  have h₂ : a * b + b * c + c * a ≤ 1 / 3 := by
    have h₃ : (a + b + c) ^ 2 = 1 := by
      have h₄ : a + b + c = 1 := by linarith
      rw [h₄]
      <;> ring
    have h₄ : 0 < a := by linarith
    have h₅ : 0 < b := by linarith
    have h₆ : 0 < c := by linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₃ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) ≥ 27 := by
    have h₄ : 0 < a := by linarith
    have h₅ : 0 < b := by linarith
    have h₆ : 0 < c := by linarith
    have h₇ : 0 < a * b := by positivity
    have h₈ : 0 < b * c := by positivity
    have h₉ : 0 < c * a := by positivity
    have h₁₀ : 0 < a * b * c := by positivity
    have h₁₁ : 0 < a * b + b * c + c * a := by positivity
    have h₁₂ : a * b + b * c + c * a ≤ 1 / 3 := h₂
    have h₁₃ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) ≥ 9 / (a * b + b * c + c * a) := by
      -- Use the AM-HM inequality to prove this step
      have h₁₄ : 0 < a * b := by positivity
      have h₁₅ : 0 < b * c := by positivity
      have h₁₆ : 0 < c * a := by positivity
      have h₁₇ : 0 < a * b + b * c + c * a := by positivity
      field_simp [h₁₄.ne', h₁₅.ne', h₁₆.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    have h₁₈ : 9 / (a * b + b * c + c * a) ≥ 27 := by
      -- Prove that 9 / (a * b + b * c + c * a) ≥ 27 using the given condition
      have h₁₉ : 0 < a * b + b * c + c * a := by positivity
      have h₂₀ : a * b + b * c + c * a ≤ 1 / 3 := h₂
      have h₂₁ : 9 / (a * b + b * c + c * a) ≥ 27 := by
        rw [ge_iff_le]
        rw [le_div_iff (by positivity)]
        nlinarith
      linarith
    linarith
  
  have h₄ : a * b * c ≤ 1 / 27 := by
    have h₅ : 0 < a := by linarith
    have h₆ : 0 < b := by linarith
    have h₇ : 0 < c := by linarith
    have h₈ : 0 < a * b := by positivity
    have h₉ : 0 < a * c := by positivity
    have h₁₀ : 0 < b * c := by positivity
    have h₁₁ : a + b + c = 1 := by linarith
    have h₁₂ : a * b * c ≤ 1 / 27 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b + c)]
    exact h₁₂
  
  have h₅ : 1 / (a * b * c) ≥ 27 := by
    have h₆ : 0 < a := by linarith
    have h₇ : 0 < b := by linarith
    have h₈ : 0 < c := by linarith
    have h₉ : 0 < a * b := by positivity
    have h₁₀ : 0 < a * b * c := by positivity
    have h₁₁ : a * b * c ≤ 1 / 27 := h₄
    have h₁₂ : 1 / (a * b * c) ≥ 27 := by
      have h₁₃ : 0 < a * b * c := by positivity
      have h₁₄ : 0 < 1 / (a * b * c) := by positivity
      -- Use the fact that the reciprocal function is decreasing to show the inequality
      have h₁₅ : 1 / (a * b * c) ≥ 27 := by
        calc
          1 / (a * b * c) ≥ 1 / (1 / 27) := by
            apply one_div_le_one_div_of_le
            · positivity
            · linarith
          _ = 27 := by norm_num
      exact h₁₅
    exact h₁₂
  
  have h₆ : (1 / a + 1) * (1 / b + 1) * (1 / c + 1) ≥ 64 := by
    have h₇ : 0 < a := by linarith
    have h₈ : 0 < b := by linarith
    have h₉ : 0 < c := by linarith
    have h₁₀ : 0 < a * b := by positivity
    have h₁₁ : 0 < a * c := by positivity
    have h₁₂ : 0 < b * c := by positivity
    have h₁₃ : 0 < a * b * c := by positivity
    have h₁₄ : (1 / a + 1) * (1 / b + 1) * (1 / c + 1) = 1 + (1 / a + 1 / b + 1 / c) + (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) + 1 / (a * b * c) := by
      have h₁₅ : (1 / a + 1) * (1 / b + 1) * (1 / c + 1) = (1 / a + 1) * ((1 / b + 1) * (1 / c + 1)) := by ring
      rw [h₁₅]
      field_simp [h₇.ne', h₈.ne', h₉.ne']
      <;> ring_nf
      <;> field_simp [h₇.ne', h₈.ne', h₉.ne']
      <;> ring_nf
      <;> nlinarith
    rw [h₁₄]
    have h₁₅ : 1 + (1 / a + 1 / b + 1 / c) + (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) + 1 / (a * b * c) ≥ 64 := by
      have h₁₆ : 1 / a + 1 / b + 1 / c ≥ 9 := h₁
      have h₁₇ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) ≥ 27 := h₃
      have h₁₈ : 1 / (a * b * c) ≥ 27 := h₅
      linarith
    linarith
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_52 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → (1 / a - 1) * (1 / b - 1) * (1 / c - 1) ≥ 8 := by
  intro a b c h
  have h₁ : (1 / a - 1) * (1 / b - 1) * (1 / c - 1) = (b + c) * (a + c) * (a + b) / (a * b * c) := by
    have h₁₁ : a > 0 := by linarith
    have h₁₂ : b > 0 := by linarith
    have h₁₃ : c > 0 := by linarith
    have h₁₄ : a + b + c = 1 := by linarith
    have h₁₅ : 1 / a - 1 = (b + c) / a := by
      have h₁₅₁ : 1 / a - 1 = (1 - a) / a := by
        field_simp [h₁₁.ne']
        <;> ring
      have h₁₅₂ : (1 - a) / a = (b + c) / a := by
        have h₁₅₃ : 1 - a = b + c := by linarith
        rw [h₁₅₃]
        <;> field_simp [h₁₁.ne']
        <;> ring
      linarith
    have h₁₆ : 1 / b - 1 = (a + c) / b := by
      have h₁₆₁ : 1 / b - 1 = (1 - b) / b := by
        field_simp [h₁₂.ne']
        <;> ring
      have h₁₆₂ : (1 - b) / b = (a + c) / b := by
        have h₁₆₃ : 1 - b = a + c := by linarith
        rw [h₁₆₃]
        <;> field_simp [h₁₂.ne']
        <;> ring
      linarith
    have h₁₇ : 1 / c - 1 = (a + b) / c := by
      have h₁₇₁ : 1 / c - 1 = (1 - c) / c := by
        field_simp [h₁₃.ne']
        <;> ring
      have h₁₇₂ : (1 - c) / c = (a + b) / c := by
        have h₁₇₃ : 1 - c = a + b := by linarith
        rw [h₁₇₃]
        <;> field_simp [h₁₃.ne']
        <;> ring
      linarith
    calc
      (1 / a - 1) * (1 / b - 1) * (1 / c - 1) = ((b + c) / a) * ((a + c) / b) * ((a + b) / c) := by
        rw [h₁₅, h₁₆, h₁₇]
      _ = (b + c) * (a + c) * (a + b) / (a * b * c) := by
        field_simp [h₁₁.ne', h₁₂.ne', h₁₃.ne']
        <;> ring
        <;> field_simp [h₁₁.ne', h₁₂.ne', h₁₃.ne']
        <;> ring
  
  have h₂ : (b + c) * (a + c) * (a + b) ≥ 8 * a * b * c := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < a * b := by positivity
    have h₂₅ : 0 < a * c := by positivity
    have h₂₆ : 0 < b * c := by positivity
    have h₂₇ : a ^ 2 * b + b * c ^ 2 ≥ 2 * a * b * c := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (c - b)]
    have h₂₈ : a ^ 2 * c + b ^ 2 * c ≥ 2 * a * b * c := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h₂₉ : a * b ^ 2 + a * c ^ 2 ≥ 2 * a * b * c := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (c - b)]
    have h₃₀ : (a + b) * (a + c) * (b + c) = a ^ 2 * b + a ^ 2 * c + a * b ^ 2 + a * c ^ 2 + b ^ 2 * c + b * c ^ 2 + 2 * a * b * c := by
      ring
    have h₃₁ : (a + b) * (a + c) * (b + c) ≥ 8 * a * b * c := by
      nlinarith [h₂₇, h₂₈, h₂₉]
    have h₃₂ : (b + c) * (a + c) * (a + b) ≥ 8 * a * b * c := by
      calc
        (b + c) * (a + c) * (a + b) = (a + b) * (a + c) * (b + c) := by ring
        _ ≥ 8 * a * b * c := by linarith
    exact h₃₂
  
  have h₃ : (b + c) * (a + c) * (a + b) / (a * b * c) ≥ 8 := by
    have h₃₁ : 0 < a := by linarith
    have h₃₂ : 0 < b := by linarith
    have h₃₃ : 0 < c := by linarith
    have h₃₄ : 0 < a * b := by positivity
    have h₃₅ : 0 < a * c := by positivity
    have h₃₆ : 0 < b * c := by positivity
    have h₃₇ : 0 < a * b * c := by positivity
    have h₃₈ : (b + c) * (a + c) * (a + b) ≥ 8 * a * b * c := h₂
    have h₃₉ : (b + c) * (a + c) * (a + b) / (a * b * c) ≥ 8 := by
      calc
        (b + c) * (a + c) * (a + b) / (a * b * c) = (b + c) * (a + c) * (a + b) / (a * b * c) := by rfl
        _ ≥ (8 * a * b * c) / (a * b * c) := by
          gcongr
          <;> nlinarith
        _ = 8 := by
          field_simp [h₃₁.ne', h₃₂.ne', h₃₃.ne']
          <;> ring
          <;> field_simp [h₃₁.ne', h₃₂.ne', h₃₃.ne']
          <;> linarith
    exact h₃₉
  
  have h₄ : (1 / a - 1) * (1 / b - 1) * (1 / c - 1) ≥ 8 := by
    calc
      (1 / a - 1) * (1 / b - 1) * (1 / c - 1) = (b + c) * (a + c) * (a + b) / (a * b * c) := by rw [h₁]
      _ ≥ 8 := by exact h₃
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_54 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 → a * b * c ≥ 8 := by
  intro a b c h
  have hx_pos : 1 + a > 1 := by
    have h₁ : a > 0 := h.1
    linarith
  
  have hy_pos : 1 + b > 1 := by
    have h₁ : b > 0 := h.2.1
    linarith
  
  have hz_pos : 1 + c > 1 := by
    have h₁ : c > 0 := h.2.2.1
    linarith
  
  have h_sum_inv : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 := by
    have h₁ : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 := h.2.2.2
    exact h₁
  
  have h_sum_ge_9 : (1 + a) + (1 + b) + (1 + c) ≥ 9 := by
    have h₁ : 0 < (1 + a : ℝ) := by linarith
    have h₂ : 0 < (1 + b : ℝ) := by linarith
    have h₃ : 0 < (1 + c : ℝ) := by linarith
    have h₄ : 0 < (1 + a : ℝ) * (1 + b : ℝ) := by positivity
    have h₅ : 0 < (1 + a : ℝ) * (1 + b : ℝ) * (1 + c : ℝ) := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne'] at h_sum_inv
    nlinarith [sq_nonneg ((1 + a : ℝ) - (1 + b : ℝ)), sq_nonneg ((1 + b : ℝ) - (1 + c : ℝ)), sq_nonneg ((1 + c : ℝ) - (1 + a : ℝ))]
  
  have h_prod_eq_sum : (1 + a) * (1 + b) * (1 + c) = (1 + a) * (1 + b) + (1 + b) * (1 + c) + (1 + c) * (1 + a) := by
    have h₁ : 0 < (1 + a : ℝ) := by linarith
    have h₂ : 0 < (1 + b : ℝ) := by linarith
    have h₃ : 0 < (1 + c : ℝ) := by linarith
    have h₄ : 0 < (1 + a : ℝ) * (1 + b : ℝ) := by positivity
    have h₅ : 0 < (1 + a : ℝ) * (1 + c : ℝ) := by positivity
    have h₆ : 0 < (1 + b : ℝ) * (1 + c : ℝ) := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne'] at h_sum_inv
    nlinarith [sq_nonneg ((1 + a : ℝ) - (1 + b : ℝ)), sq_nonneg ((1 + b : ℝ) - (1 + c : ℝ)), sq_nonneg ((1 + c : ℝ) - (1 + a : ℝ))]
  
  have h_main : a * b * c ≥ 8 := by
    have h₁ : (1 + a) * (1 + b) * (1 + c) = (1 + a) * (1 + b) + (1 + b) * (1 + c) + (1 + c) * (1 + a) := h_prod_eq_sum
    have h₂ : (1 + a) + (1 + b) + (1 + c) ≥ 9 := h_sum_ge_9
    have h₃ : 0 < (1 + a : ℝ) := by linarith
    have h₄ : 0 < (1 + b : ℝ) := by linarith
    have h₅ : 0 < (1 + c : ℝ) := by linarith
    have h₆ : 0 < (1 + a : ℝ) * (1 + b : ℝ) := by positivity
    have h₇ : 0 < (1 + a : ℝ) * (1 + c : ℝ) := by positivity
    have h₈ : 0 < (1 + b : ℝ) * (1 + c : ℝ) := by positivity
    have h₉ : a * b * c = ((1 + a) * (1 + b) * (1 + c)) - ((1 + a) * (1 + b) + (1 + b) * (1 + c) + (1 + c) * (1 + a)) + ((1 + a) + (1 + b) + (1 + c)) - 1 := by
      ring_nf
      <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try nlinarith) <;>
      (try ring_nf at * <;> nlinarith)
      <;>
      (try
        {
          field_simp [h₃.ne', h₄.ne', h₅.ne'] at h_sum_inv ⊢
          <;>
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
        })
      <;>
      (try
        {
          nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
        })
    have h₁₀ : a * b * c = ((1 + a) + (1 + b) + (1 + c)) - 1 := by
      calc
        a * b * c = ((1 + a) * (1 + b) * (1 + c)) - ((1 + a) * (1 + b) + (1 + b) * (1 + c) + (1 + c) * (1 + a)) + ((1 + a) + (1 + b) + (1 + c)) - 1 := by rw [h₉]
        _ = ((1 + a) + (1 + b) + (1 + c)) - 1 := by
          have h₁₁ : (1 + a) * (1 + b) * (1 + c) = (1 + a) * (1 + b) + (1 + b) * (1 + c) + (1 + c) * (1 + a) := h_prod_eq_sum
          nlinarith
    have h₁₁ : a * b * c ≥ 8 := by
      calc
        a * b * c = ((1 + a) + (1 + b) + (1 + c)) - 1 := by rw [h₁₀]
        _ ≥ 9 - 1 := by
          linarith
        _ = 8 := by norm_num
    exact h₁₁
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_55 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 2 * a * b / (a + b) + 2 * b * c / (b + c) + 2 * c * a / (c + a) ≤ a + b + c := by
  intro a b c h
  have h_main : 2 * a * b / (a + b) + 2 * b * c / (b + c) + 2 * c * a / (c + a) ≤ a + b + c := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    have h₇ : 2 * a * b / (a + b) ≤ (a + b) / 2 := by
      -- Prove that 2 * a * b / (a + b) ≤ (a + b) / 2
      have h₇₁ : 0 < a + b := by linarith
      rw [div_le_iff (by positivity)]
      nlinarith [sq_nonneg (a - b)]
    have h₈ : 2 * b * c / (b + c) ≤ (b + c) / 2 := by
      -- Prove that 2 * b * c / (b + c) ≤ (b + c) / 2
      have h₈₁ : 0 < b + c := by linarith
      rw [div_le_iff (by positivity)]
      nlinarith [sq_nonneg (b - c)]
    have h₉ : 2 * c * a / (c + a) ≤ (c + a) / 2 := by
      -- Prove that 2 * c * a / (c + a) ≤ (c + a) / 2
      have h₉₁ : 0 < c + a := by linarith
      rw [div_le_iff (by positivity)]
      nlinarith [sq_nonneg (c - a)]
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
  have h₁ : (x + y + z) ^ 2 / 3 ≥ x * y + y * z + z * x := by
    have h₁₀ : 0 ≤ (x - y)^2 + (y - z)^2 + (z - x)^2 := by nlinarith
    have h₁₁ : (x + y + z)^2 = x^2 + y^2 + z^2 + 2 * (x * y + y * z + z * x) := by
      ring
    have h₁₂ : (x + y + z)^2 / 3 = (x^2 + y^2 + z^2) / 3 + (2 : ℝ) / 3 * (x * y + y * z + z * x) := by
      rw [h₁₁]
      ring
      <;> field_simp
      <;> ring
    have h₁₃ : (x^2 + y^2 + z^2) / 3 ≥ (x * y + y * z + z * x) / 3 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h₂ : x * y + y * z + z * x ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
    have h₃ : 0 ≤ x := by linarith
    have h₄ : 0 ≤ y := by linarith
    have h₅ : 0 ≤ z := by linarith
    have h₆ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
      have h₆₁ : 0 ≤ y := by linarith
      have h₆₂ : 0 ≤ z := by linarith
      have h₆₃ : 0 ≤ y * z := by positivity
      have h₆₄ : Real.sqrt (y * z) ≤ (y + z) / 2 := by
        nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (y * z : ℝ)), sq_nonneg (y - z)]
      exact h₆₄
    have h₇ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
      have h₇₁ : 0 ≤ z := by linarith
      have h₇₂ : 0 ≤ x := by linarith
      have h₇₃ : 0 ≤ z * x := by positivity
      have h₇₄ : Real.sqrt (z * x) ≤ (z + x) / 2 := by
        nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (z * x : ℝ)), sq_nonneg (z - x)]
      exact h₇₄
    have h₈ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
      have h₈₁ : 0 ≤ x := by linarith
      have h₈₂ : 0 ≤ y := by linarith
      have h₈₃ : 0 ≤ x * y := by positivity
      have h₈₄ : Real.sqrt (x * y) ≤ (x + y) / 2 := by
        nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (x * y : ℝ)), sq_nonneg (x - y)]
      exact h₈₄
    have h₉ : x * Real.sqrt (y * z) ≤ x * ((y + z) / 2) := by
      have h₉₁ : 0 ≤ x := by linarith
      have h₉₂ : Real.sqrt (y * z) ≤ (y + z) / 2 := h₆
      nlinarith
    have h₁₀ : y * Real.sqrt (z * x) ≤ y * ((z + x) / 2) := by
      have h₁₀₁ : 0 ≤ y := by linarith
      have h₁₀₂ : Real.sqrt (z * x) ≤ (z + x) / 2 := h₇
      nlinarith
    have h₁₁ : z * Real.sqrt (x * y) ≤ z * ((x + y) / 2) := by
      have h₁₁₁ : 0 ≤ z := by linarith
      have h₁₁₂ : Real.sqrt (x * y) ≤ (x + y) / 2 := h₈
      nlinarith
    have h₁₂ : x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) = x * y + y * z + z * x := by
      ring_nf
      <;>
      linarith
    nlinarith [h₉, h₁₀, h₁₁]
  
  have h_main : (x + y + z) ^ 2 / 3 ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := by
    have h₃ : (x + y + z) ^ 2 / 3 ≥ x * y + y * z + z * x := h₁
    have h₄ : x * y + y * z + z * x ≥ x * Real.sqrt (y * z) + y * Real.sqrt (z * x) + z * Real.sqrt (x * y) := h₂
    linarith
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_59 : ∀ (x y : ℝ), x > 1 ∧ y > 1 → x ^ 2 / (y - 1) + y ^ 2 / (x - 1) ≥ 8 := by
  intro x y h
  have h₁ : x > 1 := by
    exact h.1
  
  have h₂ : y > 1 := by
    exact h.2
  
  have h₃ : 0 < x - 1 := by
    linarith
  
  have h₄ : 0 < y - 1 := by
    linarith
  
  have h₅ : 0 < (x - 1) * (y - 1) := by
    have h₅₁ : 0 < x - 1 := h₃
    have h₅₂ : 0 < y - 1 := h₄
    positivity
  
  have h₆ : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) ≥ 8 := by
    have h₆₁ : 0 < x - 1 := h₃
    have h₆₂ : 0 < y - 1 := h₄
    have h₆₃ : 0 < (x - 1) * (y - 1) := h₅
    field_simp [h₆₁.ne', h₆₂.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_nonneg (x - 2), sq_nonneg (y - 2),
      mul_pos h₆₁ h₆₂, sq_nonneg (x + y - 2)]
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_4_8 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  intro a b c h
  have h₁ : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₂ : 0 < a * b := by
    have h₃ : 0 < a := h.1
    have h₄ : 0 < b := h.2.1
    positivity
  
  have h₃ : 0 < b * c := by
    have h₄ : 0 < b := h.2.1
    have h₅ : 0 < c := h.2.2
    positivity
  
  have h₄ : 0 < c * a := by
    have h₅ : 0 < c := h.2.2
    have h₆ : 0 < a := h.1
    positivity
  
  have h₅ : 0 < a * b + b * c + c * a := by
    have h₆ : 0 < a * b := h₂
    have h₇ : 0 < b * c := h₃
    have h₈ : 0 < c * a := h₄
    positivity
  
  have h₆ : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a + b + c) ^ 2 / (2 * (a * b + b * c + c * a)) := by
    have h₇ : 0 < a := by linarith
    have h₈ : 0 < b := by linarith
    have h₉ : 0 < c := by linarith
    have h₁₀ : 0 < b + c := by linarith
    have h₁₁ : 0 < c + a := by linarith
    have h₁₂ : 0 < a + b := by linarith
    have h₁₃ : 0 < a * (b + c) := by positivity
    have h₁₄ : 0 < b * (c + a) := by positivity
    have h₁₅ : 0 < c * (a + b) := by positivity
    have h₁₆ : 0 < a * (b + c) * (b * (c + a)) := by positivity
    have h₁₇ : 0 < a * (b + c) * (c * (a + b)) := by positivity
    have h₁₈ : 0 < b * (c + a) * (c * (a + b)) := by positivity
    -- Use Titu's lemma to prove the inequality
    have h₁₉ : (a / (b + c) + b / (c + a) + c / (a + b)) = (a^2 / (a * (b + c)) + b^2 / (b * (c + a)) + c^2 / (c * (a + b))) := by
      have h₂₀ : a^2 / (a * (b + c)) = a / (b + c) := by
        have h₂₁ : a ≠ 0 := by linarith
        have h₂₂ : b + c ≠ 0 := by linarith
        field_simp [h₂₁, h₂₂]
        <;> ring_nf
        <;> field_simp [h₂₁, h₂₂]
        <;> ring_nf
      have h₂₃ : b^2 / (b * (c + a)) = b / (c + a) := by
        have h₂₄ : b ≠ 0 := by linarith
        have h₂₅ : c + a ≠ 0 := by linarith
        field_simp [h₂₄, h₂₅]
        <;> ring_nf
        <;> field_simp [h₂₄, h₂₅]
        <;> ring_nf
      have h₂₆ : c^2 / (c * (a + b)) = c / (a + b) := by
        have h₂₇ : c ≠ 0 := by linarith
        have h₂₈ : a + b ≠ 0 := by linarith
        field_simp [h₂₇, h₂₈]
        <;> ring_nf
        <;> field_simp [h₂₇, h₂₈]
        <;> ring_nf
      rw [h₂₀, h₂₃, h₂₆]
      <;> ring_nf
    rw [h₁₉]
    -- Use the fact that the sum of squares over sums is greater than or equal to the square of the sum over the sum of the denominators
    have h₂₀ : (a^2 / (a * (b + c)) + b^2 / (b * (c + a)) + c^2 / (c * (a + b))) ≥ (a + b + c) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := by
      -- Use the Cauchy-Schwarz inequality to prove the inequality
      have h₂₁ : 0 < a * (b + c) := by positivity
      have h₂₂ : 0 < b * (c + a) := by positivity
      have h₂₃ : 0 < c * (a + b) := by positivity
      have h₂₄ : 0 < a * (b + c) + b * (c + a) + c * (a + b) := by positivity
      -- Use the Titu's lemma to prove the inequality
      have h₂₅ : (a^2 / (a * (b + c)) + b^2 / (b * (c + a)) + c^2 / (c * (a + b))) ≥ (a + b + c) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := by
        -- Use the Titu's lemma to prove the inequality
        field_simp [h₂₁.ne', h₂₂.ne', h₂₃.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (a * (b * (c + a)) - b * (a * (b + c))), sq_nonneg (b * (c * (a + b)) - c * (b * (c + a))), sq_nonneg (c * (a * (b + c)) - a * (c * (a + b)))]
      linarith
    -- Simplify the denominator
    have h₂₁ : (a + b + c) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) = (a + b + c) ^ 2 / (2 * (a * b + b * c + c * a)) := by
      have h₂₂ : a * (b + c) + b * (c + a) + c * (a + b) = 2 * (a * b + b * c + c * a) := by
        ring
      rw [h₂₂]
      <;> field_simp
      <;> ring_nf
    rw [h₂₁] at h₂₀
    linarith
  
  have h₇ : (a + b + c) ^ 2 / (2 * (a * b + b * c + c * a)) ≥ 3 / 2 := by
    have h₈ : 0 < a * b + b * c + c * a := by positivity
    have h₉ : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := h₁
    have h₁₀ : (a + b + c) ^ 2 / (2 * (a * b + b * c + c * a)) ≥ 3 / 2 := by
      rw [ge_iff_le]
      rw [le_div_iff (by positivity)]
      nlinarith
    exact h₁₀
  
  have h₈ : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    linarith
  
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_60 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
  intro a b c h
  have h₁ : 2 * a ^ 3 + b ^ 3 ≥ 3 * a ^ 2 * b := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b / 2),
      mul_pos h₁₁ h₁₂, sq_nonneg (a + b / 2), sq_nonneg (a - 2 * b),
      sq_nonneg (2 * a - b)]
  
  have h₂ : 2 * b ^ 3 + c ^ 3 ≥ 3 * b ^ 2 * c := by
    have h₂₁ : 0 < b := by linarith
    have h₂₂ : 0 < c := by linarith
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - c / 2),
      mul_pos h₂₁ h₂₂, sq_nonneg (b + c / 2), sq_nonneg (b - 2 * c),
      sq_nonneg (2 * b - c)]
  
  have h₃ : 2 * c ^ 3 + a ^ 3 ≥ 3 * c ^ 2 * a := by
    have h₃₁ : 0 < c := by linarith
    have h₃₂ : 0 < a := by linarith
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c - a / 2),
      mul_pos h₃₁ h₃₂, sq_nonneg (c + a / 2), sq_nonneg (c - 2 * a),
      sq_nonneg (2 * c - a)]
  
  have h₄ : 3 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
    have h₄₁ : 3 * (a ^ 3 + b ^ 3 + c ^ 3) = (2 * a ^ 3 + b ^ 3) + (2 * b ^ 3 + c ^ 3) + (2 * c ^ 3 + a ^ 3) := by
      ring
    rw [h₄₁]
    have h₄₂ : (2 * a ^ 3 + b ^ 3) + (2 * b ^ 3 + c ^ 3) + (2 * c ^ 3 + a ^ 3) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
      nlinarith [h₁, h₂, h₃]
    linarith
  
  have h₅ : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
    have h₅₁ : 3 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := h₄
    have h₅₂ : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
      linarith
    exact h₅₂
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_62 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ b / a + c / b + a / c := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 < b * c := by positivity
  have h₆ : 0 < c * a := by positivity
  have h₇ : 0 < a * b * c := by positivity
  have h₈ : (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2) - (b / a + c / b + a / c) ≥ 0 := by
    have h₉ : 0 < a * b * c := by positivity
    have h₁₀ : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c),
      sq_nonneg (a ^ 2 * c - a * b * c), sq_nonneg (b ^ 2 * a - a * b * c), sq_nonneg (c ^ 2 * b - a * b * c),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁, mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂),
      mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃), mul_pos (sq_pos_of_pos h₃) (sq_pos_of_pos h₁)]
  
  have h₉ : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ b / a + c / b + a / c := by
    linarith
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_63 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c) := by
  intro a b c h
  have h₁ : 1 / a ^ 2 + 1 / b ^ 2 ≥ 2 / (a * b) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < a * b := by positivity
    have h₁₄ : 0 < a ^ 2 := by positivity
    have h₁₅ : 0 < b ^ 2 := by positivity
    have h₁₆ : 0 < a ^ 2 * b ^ 2 := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    have h₁₇ : 0 ≤ (a - b) ^ 2 := by positivity
    have h₁₈ : 0 ≤ (1 / a - 1 / b) ^ 2 := by positivity
    have h₁₉ : (1 / a - 1 / b) ^ 2 ≥ 0 := by positivity
    have h₂₀ : 1 / a ^ 2 + 1 / b ^ 2 - 2 / (a * b) ≥ 0 := by
      field_simp [h₁₁.ne', h₁₂.ne']
      rw [le_div_iff (by positivity)]
      -- Simplify the expression to show it is non-negative
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    -- Combine the inequalities to get the final result
    linarith
  
  have h₂ : 1 / a ^ 2 + 1 / c ^ 2 ≥ 2 / (a * c) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < c := by linarith
    have h₂₃ : 0 < a * c := by positivity
    have h₂₄ : 0 < a ^ 2 := by positivity
    have h₂₅ : 0 < c ^ 2 := by positivity
    have h₂₆ : 0 < a ^ 2 * c ^ 2 := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    have h₂₇ : 0 ≤ (a - c) ^ 2 := by positivity
    have h₂₈ : 0 ≤ (1 / a - 1 / c) ^ 2 := by positivity
    have h₂₉ : (1 / a - 1 / c) ^ 2 ≥ 0 := by positivity
    have h₃₀ : 1 / a ^ 2 + 1 / c ^ 2 - 2 / (a * c) ≥ 0 := by
      field_simp [h₂₁.ne', h₂₂.ne']
      rw [le_div_iff (by positivity)]
      -- Simplify the expression to show it is non-negative
      nlinarith [sq_nonneg (a - c), sq_nonneg (a + c)]
    -- Combine the inequalities to get the final result
    linarith
  
  have h₃ : 1 / b ^ 2 + 1 / c ^ 2 ≥ 2 / (b * c) := by
    have h₃₁ : 0 < b := by linarith
    have h₃₂ : 0 < c := by linarith
    have h₃₃ : 0 < b * c := by positivity
    have h₃₄ : 0 < b ^ 2 := by positivity
    have h₃₅ : 0 < c ^ 2 := by positivity
    have h₃₆ : 0 < b ^ 2 * c ^ 2 := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    have h₃₇ : 0 ≤ (b - c) ^ 2 := by positivity
    have h₃₈ : 0 ≤ (1 / b - 1 / c) ^ 2 := by positivity
    have h₃₉ : (1 / b - 1 / c) ^ 2 ≥ 0 := by positivity
    have h₄₀ : 1 / b ^ 2 + 1 / c ^ 2 - 2 / (b * c) ≥ 0 := by
      field_simp [h₃₁.ne', h₃₂.ne']
      rw [le_div_iff (by positivity)]
      -- Simplify the expression to show it is non-negative
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c)]
    -- Combine the inequalities to get the final result
    linarith
  
  have h₄ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ 1 / (a * b) + 1 / (a * c) + 1 / (b * c) := by
    have h₄₁ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ 1 / (a * b) + 1 / (a * c) + 1 / (b * c) := by
      have h₄₂ : 1 / a ^ 2 + 1 / b ^ 2 ≥ 2 / (a * b) := h₁
      have h₄₃ : 1 / a ^ 2 + 1 / c ^ 2 ≥ 2 / (a * c) := h₂
      have h₄₄ : 1 / b ^ 2 + 1 / c ^ 2 ≥ 2 / (b * c) := h₃
      have h₄₅ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ 1 / (a * b) + 1 / (a * c) + 1 / (b * c) := by
        calc
          1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 = (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) := by rfl
          _ ≥ (2 / (a * b) + 2 / (a * c) + 2 / (b * c)) / 2 := by
            -- Summing the three inequalities and dividing by 2
            linarith
          _ = 1 / (a * b) + 1 / (a * c) + 1 / (b * c) := by
            -- Simplifying the right-hand side
            ring_nf
            <;> field_simp [h.1.ne', h.2.1.ne', h.2.2.ne']
            <;> ring_nf
            <;> linarith
      exact h₄₅
    exact h₄₁
  
  have h₅ : 1 / (a * b) + 1 / (a * c) + 1 / (b * c) = (a + b + c) / (a * b * c) := by
    have h₅₁ : 0 < a := by linarith
    have h₅₂ : 0 < b := by linarith
    have h₅₃ : 0 < c := by linarith
    have h₅₄ : 0 < a * b := by positivity
    have h₅₅ : 0 < a * c := by positivity
    have h₅₆ : 0 < b * c := by positivity
    have h₅₇ : 0 < a * b * c := by positivity
    -- Simplify the left side to match the right side
    have h₅₈ : 1 / (a * b) + 1 / (a * c) + 1 / (b * c) = (a + b + c) / (a * b * c) := by
      field_simp [h₅₁.ne', h₅₂.ne', h₅₃.ne', h₅₄.ne', h₅₅.ne', h₅₆.ne', h₅₇.ne']
      <;> ring_nf
      <;> field_simp [h₅₁.ne', h₅₂.ne', h₅₃.ne', h₅₄.ne', h₅₅.ne', h₅₆.ne', h₅₇.ne']
      <;> ring_nf
      <;> nlinarith
    rw [h₅₈]
  
  have h₆ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c) := by
    have h₆₁ : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ 1 / (a * b) + 1 / (a * c) + 1 / (b * c) := h₄
    have h₆₂ : 1 / (a * b) + 1 / (a * c) + 1 / (b * c) = (a + b + c) / (a * b * c) := h₅
    linarith
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_64 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a → a / (b + c - a) + b / (c + a - b) + c / (a + b - c) ≥ 3 := by
  intro a b c h
  have h₁ : b + c - a > 0 := by
    have h₁₁ : b + c > a := by linarith
    linarith
  
  have h₂ : c + a - b > 0 := by
    have h₂₁ : c + a > b := by linarith
    linarith
  
  have h₃ : a + b - c > 0 := by
    have h₃₁ : a + b > c := by linarith
    linarith
  
  have h₄ : a / (b + c - a) + b / (c + a - b) + c / (a + b - c) ≥ 3 := by
    have h₅ : 0 < (b + c - a) := by linarith
    have h₆ : 0 < (c + a - b) := by linarith
    have h₇ : 0 < (a + b - c) := by linarith
    have h₈ : 0 < (b + c - a) * (c + a - b) := by positivity
    have h₉ : 0 < (b + c - a) * (a + b - c) := by positivity
    have h₁₀ : 0 < (c + a - b) * (a + b - c) := by positivity
    have h₁₁ : 0 < (b + c - a) * (c + a - b) * (a + b - c) := by positivity
    field_simp [h₅.ne', h₆.ne', h₇.ne']
    rw [le_div_iff (by positivity)]
    -- Use nlinarith to handle the inequality after expanding and simplifying
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₅ h₆, mul_pos h₅ h₇, mul_pos h₆ h₇,
      sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b)]
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_69 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → a * b + b * c + c * a ≤ 1 / 3 := by
  intro a b c h
  have h_sum_sq : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) = 1 := by
    have h₁ : a + b + c = 1 := h.2.2.2
    have h₂ : (a + b + c) ^ 2 = 1 := by rw [h₁]; norm_num
    have h₃ : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
      ring
    linarith
  
  have h_sq_ineq : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by positivity
    have h₂ : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      ring
    have h₃ : 0 ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by linarith
    linarith
  
  have h_main_ineq : 3 * (a * b + b * c + c * a) ≤ 1 := by
    have h₁ : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) = 1 := h_sum_sq
    have h₂ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := h_sq_ineq
    nlinarith [h₁, h₂]
  
  have h_final : a * b + b * c + c * a ≤ 1 / 3 := by
    have h₁ : 3 * (a * b + b * c + c * a) ≤ 1 := h_main_ineq
    have h₂ : a * b + b * c + c * a ≤ 1 / 3 := by
      linarith
    exact h₂
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_73_1 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) < 5 := by
  have h_main_lemma : ∀ (x : ℝ), x > 0 → Real.sqrt (4 * x + 1) < 2 * x + 1 := by
    intro x hx
    have h₁ : 0 < 2 * x + 1 := by linarith
    have h₂ : 0 ≤ 4 * x + 1 := by linarith
    have h₃ : 0 ≤ (2 * x + 1 : ℝ) := by linarith
    have h₄ : (Real.sqrt (4 * x + 1)) ^ 2 = 4 * x + 1 := by
      rw [Real.sq_sqrt] <;> linarith
    have h₅ : (2 * x + 1 : ℝ) ^ 2 = 4 * x ^ 2 + 4 * x + 1 := by
      ring
    have h₆ : (2 * x + 1 : ℝ) ^ 2 > 4 * x + 1 := by
      nlinarith [sq_pos_of_pos hx]
    have h₇ : Real.sqrt (4 * x + 1) < 2 * x + 1 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (by linarith : 0 ≤ (4 * x + 1 : ℝ))]
    exact h₇
  
  have h_final : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) < 5 := by
    intro a b c h
    have h₁ : a > 0 := h.1
    have h₂ : b > 0 := h.2.1
    have h₃ : c > 0 := h.2.2.1
    have h₄ : a + b + c = 1 := h.2.2.2
    have h₅ : Real.sqrt (4 * a + 1) < 2 * a + 1 := h_main_lemma a h₁
    have h₆ : Real.sqrt (4 * b + 1) < 2 * b + 1 := h_main_lemma b h₂
    have h₇ : Real.sqrt (4 * c + 1) < 2 * c + 1 := h_main_lemma c h₃
    have h₈ : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) < (2 * a + 1) + (2 * b + 1) + (2 * c + 1) := by
      linarith
    have h₉ : (2 * a + 1) + (2 * b + 1) + (2 * c + 1) = 2 * (a + b + c) + 3 := by ring
    have h₁₀ : (2 * a + 1) + (2 * b + 1) + (2 * c + 1) = 5 := by
      rw [h₉]
      rw [h₄]
      <;> norm_num
    linarith
  
  exact h_final

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
  
  have h₄ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ^ 2 ≤ 3 * ((4 * a + 1) + (4 * b + 1) + (4 * c + 1)) := by
    have h₄₁ : 0 ≤ Real.sqrt (4 * a + 1) := Real.sqrt_nonneg _
    have h₄₂ : 0 ≤ Real.sqrt (4 * b + 1) := Real.sqrt_nonneg _
    have h₄₃ : 0 ≤ Real.sqrt (4 * c + 1) := Real.sqrt_nonneg _
    have h₄₄ : 0 ≤ Real.sqrt (4 * a + 1) * Real.sqrt (4 * b + 1) := by positivity
    have h₄₅ : 0 ≤ Real.sqrt (4 * a + 1) * Real.sqrt (4 * c + 1) := by positivity
    have h₄₆ : 0 ≤ Real.sqrt (4 * b + 1) * Real.sqrt (4 * c + 1) := by positivity
    nlinarith [Real.sq_sqrt (show 0 ≤ 4 * a + 1 by linarith [h.1]),
      Real.sq_sqrt (show 0 ≤ 4 * b + 1 by linarith [h.2.1]),
      Real.sq_sqrt (show 0 ≤ 4 * c + 1 by linarith [h.2.2.1]),
      sq_nonneg (Real.sqrt (4 * a + 1) - Real.sqrt (4 * b + 1)),
      sq_nonneg (Real.sqrt (4 * a + 1) - Real.sqrt (4 * c + 1)),
      sq_nonneg (Real.sqrt (4 * b + 1) - Real.sqrt (4 * c + 1))]
  
  have h₅ : 3 * ((4 * a + 1) + (4 * b + 1) + (4 * c + 1)) = 21 := by
    have h₅₁ : a + b + c = 1 := h.2.2.2
    ring_nf at h₄ ⊢
    linarith
  
  have h₆ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ^ 2 ≤ 21 := by
    linarith [h₄, h₅]
  
  have h₇ : Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) ≤ Real.sqrt 21 := by
    have h₇₁ : 0 ≤ Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1) := by positivity
    have h₇₂ : 0 ≤ Real.sqrt 21 := Real.sqrt_nonneg 21
    have h₇₃ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ^ 2 ≤ 21 := h₆
    have h₇₄ : (Real.sqrt 21 : ℝ) ≥ 0 := Real.sqrt_nonneg 21
    have h₇₅ : (Real.sqrt (4 * a + 1) + Real.sqrt (4 * b + 1) + Real.sqrt (4 * c + 1)) ≤ Real.sqrt 21 := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h₇₅
  
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_5_8_1 : ∀ (a b : ℝ), a ≥ 0 ∧ b ≥ 0 → (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
  intro a b h
  have h₁ : 0 ≤ (a + b) / 2 := by
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    have h₄ : 0 ≤ a + b := by linarith
    linarith
  
  have h₂ : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h₃ : 0 ≤ (a - b) ^ 2 := by nlinarith
    have h₄ : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
    have h₅ : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by linarith
    have h₆ : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
    have h₇ : ((a + b) / 2) ^ 2 = (a + b) ^ 2 / 4 := by
      ring_nf
      <;> field_simp
      <;> ring_nf
    rw [h₇]
    have h₈ : (a + b) ^ 2 / 4 ≤ (a ^ 2 + b ^ 2) / 2 := by
      nlinarith [sq_nonneg (a - b)]
    linarith
  
  have h₃ : (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
    have h₄ : 0 ≤ (a ^ 2 + b ^ 2) / 2 := by
      have h₅ : 0 ≤ a ^ 2 := by nlinarith
      have h₆ : 0 ≤ b ^ 2 := by nlinarith
      nlinarith
    -- Use the property of square roots to compare the squares of both sides
    have h₅ : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := h₂
    -- Apply the lemma that if x^2 ≤ y and y ≥ 0, then x ≤ sqrt(y)
    have h₆ : (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h₆
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_77_1 : ∀ (a b : ℝ), a > 0 ∧ b > 0 ∧ a + b = 1 → (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
  intro a b h
  have h₁ : a > 0 := by
    linarith [h.1]

  have h₂ : b > 0 := by
    linarith [h.2.1]

  have h₃ : a + b = 1 := by
    linarith [h.2.2]

  have h₄ : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ ((a + 1 / a) + (b + 1 / b)) ^ 2 / 2 := by
    have h₄₁ : 0 ≤ (a + 1 / a - (b + 1 / b)) ^ 2 := sq_nonneg _
    have h₄₂ : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ ((a + 1 / a) + (b + 1 / b)) ^ 2 / 2 := by
      nlinarith [sq_nonneg (a + 1 / a - (b + 1 / b))]
    exact h₄₂

  have h₅ : (a + 1 / a) + (b + 1 / b) = 1 + 1 / (a * b) := by
    have h₅₁ : (a + 1 / a) + (b + 1 / b) = (a + b) + (1 / a + 1 / b) := by ring
    rw [h₅₁]
    have h₅₂ : a + b = 1 := h₃
    rw [h₅₂]
    have h₅₃ : 1 / a + 1 / b = 1 / (a * b) := by
      have h₅₄ : 1 / a + 1 / b = (a + b) / (a * b) := by
        field_simp [h₁.ne', h₂.ne']
        <;> ring
        <;> field_simp [h₁.ne', h₂.ne']
        <;> ring
      rw [h₅₄]
      have h₅₅ : a + b = 1 := h₃
      rw [h₅₅]
      <;> field_simp [h₁.ne', h₂.ne']
      <;> ring
    rw [h₅₃]
    <;> ring

  have h₆ : a * b ≤ 1 / 4 := by
    have h₆₁ : (a + b) ^ 2 = 1 := by
      rw [h₃]
      <;> norm_num
    have h₆₂ : 0 < a * b := mul_pos h₁ h₂
    nlinarith [sq_nonneg (a - b)]

  have h₇ : 1 / (a * b) ≥ 4 := by
    have h₇₁ : 0 < a * b := mul_pos h₁ h₂
    have h₇₂ : a * b ≤ 1 / 4 := h₆
    have h₇₃ : 1 / (a * b) ≥ 4 := by
      have h₇₄ : 0 < a * b := mul_pos h₁ h₂
      have h₇₅ : 0 < 1 / (a * b) := by positivity
      -- Use the fact that if x ≤ y, then 1/x ≥ 1/y for positive x, y
      have h₇₆ : 1 / (a * b) ≥ 4 := by
        calc
          1 / (a * b) ≥ 1 / (1 / 4) := by
            apply one_div_le_one_div_of_le
            · positivity
            · linarith
          _ = 4 := by norm_num
      exact h₇₆
    exact h₇₃

  have h₈ : (a + 1 / a) + (b + 1 / b) ≥ 5 := by
    have h₈₁ : (a + 1 / a) + (b + 1 / b) = 1 + 1 / (a * b) := h₅
    rw [h₈₁]
    have h₈₂ : 1 / (a * b) ≥ 4 := h₇
    linarith

  have h₉ : ((a + 1 / a) + (b + 1 / b)) ^ 2 / 2 ≥ 25 / 2 := by
    have h₉₁ : (a + 1 / a) + (b + 1 / b) ≥ 5 := h₈
    have h₉₂ : ((a + 1 / a) + (b + 1 / b)) ^ 2 ≥ 25 := by
      nlinarith
    have h₉₃ : ((a + 1 / a) + (b + 1 / b)) ^ 2 / 2 ≥ 25 / 2 := by
      linarith
    exact h₉₃

  have h₁₀ : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 25 / 2 := by
    have h₁₀₁ : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ ((a + 1 / a) + (b + 1 / b)) ^ 2 / 2 := h₄
    have h₁₀₂ : ((a + 1 / a) + (b + 1 / b)) ^ 2 / 2 ≥ 25 / 2 := h₉
    linarith

  exact h₁₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

lemma sq_ineq (x y : ℝ) : (1 + x^2) * (1 + y^2) ≥ (1 + x*y)^2 :=
  by nlinarith [sq_nonneg (x - y)]

lemma helper_ineq (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
  (1 - x * y) * (x - y)^2 ≥ 0 :=
  by
  have h₁ : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
  have h₂ : 0 ≤ 1 - x * y := by
    nlinarith [mul_nonneg hx0 hy0]
  nlinarith

lemma sum_recip_ineq (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
  1 / (1 + x^2) + 1 / (1 + y^2) ≤ 2 / (1 + x * y) :=
  by
  have h₁ : 0 ≤ x * y := mul_nonneg hx0 hy0
  have h₂ : 0 < 1 + x ^ 2 := by nlinarith
  have h₃ : 0 < 1 + y ^ 2 := by nlinarith
  have h₄ : 0 < 1 + x * y := by nlinarith
  have h₅ : 0 < (1 + x ^ 2) * (1 + y ^ 2) := by positivity
  have h₆ : 0 < (1 + x ^ 2) * (1 + y ^ 2) * (1 + x * y) := by positivity
  field_simp [h₂.ne', h₃.ne', h₄.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (x - y), mul_nonneg hx0 hy0, mul_nonneg (sq_nonneg (x - y)) (sub_nonneg.mpr h₁),
    helper_ineq x y hx0 hx1 hy0 hy1]

lemma sqrt_ineq (x y : ℝ) : Real.sqrt ((1 + x^2) * (1 + y^2)) ≥ 1 + x * y := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (x - y)]

theorem radmila_exercise_1_79 : ∀ (x y : ℝ), 0 ≤ x ∧ 0 ≤ y ∧ x ≤ 1 ∧ y ≤ 1 → 1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2) ≤ 2 / Real.sqrt (1 + x * y) := by
  intro x y h
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have h₁ : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h₂ : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h₃ : 0 < Real.sqrt (1 + x * y) := Real.sqrt_pos.mpr (by nlinarith)
  have h₄ : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by positivity
  have h₅ : (1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2)) ^ 2 ≤ (2 / Real.sqrt (1 + x * y)) ^ 2 := by
    have h₆ : 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) ≤ 2 / (1 + x * y) := sum_recip_ineq x y hx0 hx1 hy0 hy1
    have h₇ : Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) ≥ 1 + x * y := sqrt_ineq x y
    have h₈ : 2 / Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) ≤ 2 / (1 + x * y) := by
      apply div_le_div_of_le_left (by positivity) (by positivity)
      <;> nlinarith [Real.sqrt_nonneg ((1 + x ^ 2) * (1 + y ^ 2)), Real.sq_sqrt (show 0 ≤ (1 + x ^ 2) * (1 + y ^ 2) by positivity)]
    calc
      (1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2)) ^ 2 = (1 / Real.sqrt (1 + x ^ 2)) ^ 2 + (1 / Real.sqrt (1 + y ^ 2)) ^ 2 + 2 * (1 / Real.sqrt (1 + x ^ 2)) * (1 / Real.sqrt (1 + y ^ 2)) := by
        ring_nf
        <;> field_simp <;> ring_nf
        <;> field_simp <;> ring_nf
      _ = 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 2 / Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) := by
        have h₉ : (1 / Real.sqrt (1 + x ^ 2)) ^ 2 = 1 / (1 + x ^ 2) := by
          field_simp [Real.sqrt_sq, hx0, Real.sqrt_nonneg]
          <;> ring_nf
          <;> field_simp [hx0]
          <;> ring_nf
        have h₁₀ : (1 / Real.sqrt (1 + y ^ 2)) ^ 2 = 1 / (1 + y ^ 2) := by
          field_simp [Real.sqrt_sq, hy0, Real.sqrt_nonneg]
          <;> ring_nf
          <;> field_simp [hy0]
          <;> ring_nf
        have h₁₁ : 2 * (1 / Real.sqrt (1 + x ^ 2)) * (1 / Real.sqrt (1 + y ^ 2)) = 2 / Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) := by
          have h₁₂ : Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) = Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + y ^ 2) := by
            rw [Real.sqrt_mul] <;> positivity
          rw [h₁₂]
          field_simp [h₁, h₂, Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> field_simp <;> ring_nf <;>
            nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + y ^ 2),
              Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity),
              Real.sq_sqrt (show 0 ≤ 1 + y ^ 2 by positivity)]
        rw [h₉, h₁₀, h₁₁]
        <;> ring_nf
      _ ≤ 1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 2 / (1 + x * y) := by
        gcongr <;> nlinarith
      _ ≤ 2 / (1 + x * y) + 2 / (1 + x * y) := by
        linarith [h₆]
      _ = 4 / (1 + x * y) := by ring
      _ = (2 / Real.sqrt (1 + x * y)) ^ 2 := by
        have h₁₃ : 0 < 1 + x * y := by nlinarith
        have h₁₄ : (2 / Real.sqrt (1 + x * y)) ^ 2 = 4 / (1 + x * y) := by
          calc
            (2 / Real.sqrt (1 + x * y)) ^ 2 = 4 / (Real.sqrt (1 + x * y)) ^ 2 := by
              field_simp [h₃.ne'] <;> ring_nf <;> field_simp [h₃.ne']
              <;> ring_nf
            _ = 4 / (1 + x * y) := by
              rw [Real.sq_sqrt (by nlinarith)]
              <;> field_simp [h₃.ne']
              <;> ring_nf
        linarith
  have h₆ : 0 ≤ 1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2) := by positivity
  have h₇ : 0 ≤ 2 / Real.sqrt (1 + x * y) := by positivity
  nlinarith [sq_nonneg (1 / Real.sqrt (1 + x ^ 2) + 1 / Real.sqrt (1 + y ^ 2)),
    sq_nonneg (2 / Real.sqrt (1 + x * y))]

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_85 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 ≥ 9 / (4 * (a + b + c)) := by
  intro a b c h
  have h₁ : a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 ≥ (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) := by
    have h₁₀ : 0 < a := by linarith
    have h₁₁ : 0 < b := by linarith
    have h₁₂ : 0 < c := by linarith
    have h₁₃ : 0 < a * (b + c) ^ 2 := by positivity
    have h₁₄ : 0 < b * (c + a) ^ 2 := by positivity
    have h₁₅ : 0 < c * (a + b) ^ 2 := by positivity
    have h₁₆ : 0 < a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2 := by positivity
    have h₁₇ : (a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2) ≥ (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) := by
      -- Use Titu's lemma to prove the inequality
      have h₁₈ : 0 < (b + c) ^ 2 := by positivity
      have h₁₉ : 0 < (c + a) ^ 2 := by positivity
      have h₂₀ : 0 < (a + b) ^ 2 := by positivity
      -- Apply Titu's lemma: sum (x_i^2 / y_i) ≥ (sum x_i)^2 / (sum y_i)
      have h₂₁ : (a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2) = (a^2 / (a * (b + c) ^ 2) + b^2 / (b * (c + a) ^ 2) + c^2 / (c * (a + b) ^ 2)) := by
        have h₂₂ : a^2 / (a * (b + c) ^ 2) = a / (b + c) ^ 2 := by
          have h₂₃ : a ≠ 0 := by linarith
          have h₂₄ : a * (b + c) ^ 2 ≠ 0 := by positivity
          field_simp [h₂₃, h₂₄]
          <;> ring
          <;> field_simp [h₂₃, h₂₄]
          <;> ring
        have h₂₅ : b^2 / (b * (c + a) ^ 2) = b / (c + a) ^ 2 := by
          have h₂₆ : b ≠ 0 := by linarith
          have h₂₇ : b * (c + a) ^ 2 ≠ 0 := by positivity
          field_simp [h₂₆, h₂₇]
          <;> ring
          <;> field_simp [h₂₆, h₂₇]
          <;> ring
        have h₂₈ : c^2 / (c * (a + b) ^ 2) = c / (a + b) ^ 2 := by
          have h₂₉ : c ≠ 0 := by linarith
          have h₃₀ : c * (a + b) ^ 2 ≠ 0 := by positivity
          field_simp [h₂₉, h₃₀]
          <;> ring
          <;> field_simp [h₂₉, h₃₀]
          <;> ring
        rw [h₂₂, h₂₅, h₂₈]
        <;> ring
      rw [h₂₁]
      -- Use the Titu's lemma inequality
      have h₃₁ : (a^2 / (a * (b + c) ^ 2) + b^2 / (b * (c + a) ^ 2) + c^2 / (c * (a + b) ^ 2)) ≥ (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) := by
        -- Use the Cauchy-Schwarz inequality in Engel form
        have h₃₂ : 0 < a * (b + c) ^ 2 := by positivity
        have h₃₃ : 0 < b * (c + a) ^ 2 := by positivity
        have h₃₄ : 0 < c * (a + b) ^ 2 := by positivity
        -- Use the Titu's lemma to get the inequality
        have h₃₅ : (a^2 / (a * (b + c) ^ 2) + b^2 / (b * (c + a) ^ 2) + c^2 / (c * (a + b) ^ 2)) ≥ (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) := by
          field_simp [h₃₂.ne', h₃₃.ne', h₃₄.ne']
          rw [div_le_div_iff (by positivity) (by positivity)]
          nlinarith [sq_nonneg (a * (b * (c + a) ^ 2) - b * (a * (b + c) ^ 2)),
            sq_nonneg (b * (c * (a + b) ^ 2) - c * (b * (c + a) ^ 2)),
            sq_nonneg (c * (a * (b + c) ^ 2) - a * (c * (a + b) ^ 2))]
        linarith
      linarith
    linarith
  
  have h₂ : (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) ≥ 9 / (4 * (a + b + c)) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2 := by positivity
    have h₂₅ : 0 < a + b + c := by linarith
    have h₂₆ : 0 < 4 * (a + b + c) := by positivity
    -- Use the division inequality to transform the goal into a polynomial inequality
    have h₂₇ : (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) ≥ 9 / (4 * (a + b + c)) := by
      -- Cross-multiply to eliminate denominators
      have h₂₈ : 0 < a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2 := by positivity
      have h₂₉ : 0 < 4 * (a + b + c) := by positivity
      -- Use the division inequality to transform the goal into a polynomial inequality
      have h₃₀ : (a + b + c) ^ 2 * (4 * (a + b + c)) ≥ 9 * (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) := by
        -- Expand both sides and simplify
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg h₂₁.le h₂₂.le, mul_nonneg h₂₂.le h₂₃.le, mul_nonneg h₂₃.le h₂₁.le,
          mul_nonneg (sq_nonneg (a - b)) h₂₃.le, mul_nonneg (sq_nonneg (b - c)) h₂₁.le,
          mul_nonneg (sq_nonneg (c - a)) h₂₂.le, mul_nonneg (sq_nonneg (a - b)) h₂₁.le,
          mul_nonneg (sq_nonneg (b - c)) h₂₂.le, mul_nonneg (sq_nonneg (c - a)) h₂₃.le]
      -- Use the division inequality to conclude the proof
      have h₃₁ : 0 < a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2 := by positivity
      have h₃₂ : 0 < 4 * (a + b + c) := by positivity
      have h₃₃ : 0 < (a + b + c) ^ 2 := by positivity
      have h₃₄ : 0 < (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) * (4 * (a + b + c)) := by positivity
      -- Use the division inequality to conclude the proof
      rw [ge_iff_le]
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith
    exact h₂₇
  
  have h_main : a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 ≥ 9 / (4 * (a + b + c)) := by
    have h₃ : a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 ≥ (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) := h₁
    have h₄ : (a + b + c) ^ 2 / (a * (b + c) ^ 2 + b * (c + a) ^ 2 + c * (a + b) ^ 2) ≥ 9 / (4 * (a + b + c)) := h₂
    linarith
  
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_86 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
  intro a b c h
  have h₁ : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    have h₁₁ : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
    nlinarith [sq_nonneg (a + b + c)]
  
  have h₂ : 3 / (a * b + b * c + c * a) ≥ 9 / (a + b + c) ^ 2 := by
    have h₂₁ : 0 < a * b + b * c + c * a := by
      nlinarith [h.1, h.2.1, h.2.2]
    have h₂₂ : 0 < (a + b + c) ^ 2 := by
      have h₂₂₁ : 0 < a + b + c := by nlinarith [h.1, h.2.1, h.2.2]
      positivity
    have h₂₃ : 0 < a + b + c := by nlinarith [h.1, h.2.1, h.2.2]
    -- Use the fact that (a + b + c)^2 ≥ 3(ab + bc + ca) to establish the inequality
    have h₂₄ : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by linarith
    -- Use the division inequality to compare the reciprocals
    have h₂₅ : 3 / (a * b + b * c + c * a) ≥ 9 / (a + b + c) ^ 2 := by
      -- Use the fact that the denominators are positive to cross-multiply
      have h₂₅₁ : 0 < a * b + b * c + c * a := by positivity
      have h₂₅₂ : 0 < (a + b + c) ^ 2 := by positivity
      -- Use the division inequality to compare the reciprocals
      calc
        3 / (a * b + b * c + c * a) ≥ 3 / ((a + b + c) ^ 2 / 3) := by
          -- Use the fact that (a + b + c)^2 ≥ 3(ab + bc + ca)
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        _ = 9 / (a + b + c) ^ 2 := by
          -- Simplify the expression
          field_simp
          <;> ring_nf
          <;> field_simp
          <;> ring_nf
    exact h₂₅
  
  have h₃ : 9 / (a + b + c) ^ 2 - 6 / (a + b + c) ≥ -1 := by
    have h₃₁ : 0 < a + b + c := by
      nlinarith [h.1, h.2.1, h.2.2]
    have h₃₂ : 0 < (a + b + c) ^ 2 := by positivity
    have h₃₃ : (a + b + c - 3) ^ 2 ≥ 0 := by nlinarith
    have h₃₄ : 9 / (a + b + c) ^ 2 - 6 / (a + b + c) + 1 ≥ 0 := by
      field_simp [h₃₁.ne']
      rw [le_div_iff (by positivity)]
      nlinarith [sq_nonneg (a + b + c - 3)]
    linarith
  
  have h₄ : 3 / (a * b + b * c + c * a) - 6 / (a + b + c) ≥ -1 := by
    have h₄₁ : 3 / (a * b + b * c + c * a) - 6 / (a + b + c) ≥ 9 / (a + b + c) ^ 2 - 6 / (a + b + c) := by
      -- Use the fact that 3 / (a * b + b * c + c * a) ≥ 9 / (a + b + c) ^ 2 to establish the inequality
      have h₄₁₁ : 3 / (a * b + b * c + c * a) ≥ 9 / (a + b + c) ^ 2 := h₂
      have h₄₁₂ : 6 / (a + b + c) = 6 / (a + b + c) := rfl
      -- Subtract 6 / (a + b + c) from both sides of the inequality
      have h₄₁₃ : 3 / (a * b + b * c + c * a) - 6 / (a + b + c) ≥ 9 / (a + b + c) ^ 2 - 6 / (a + b + c) := by
        linarith
      exact h₄₁₃
    -- Use the fact that 9 / (a + b + c) ^ 2 - 6 / (a + b + c) ≥ -1 to establish the final inequality
    linarith
  
  have h₅ : 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
    have h₅₁ : 3 / (a * b + b * c + c * a) - 6 / (a + b + c) ≥ -1 := h₄
    have h₅₂ : 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by
      linarith
    exact h₅₂
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_91 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
  intro a b c h
  have h_main : (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) := by
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
    have h₁₄ : 0 < a ^ 3 := by positivity
    have h₁₅ : 0 < b ^ 3 := by positivity
    have h₁₆ : 0 < c ^ 3 := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * c),
      sq_nonneg (a ^ 2 * b - a ^ 2 * c), sq_nonneg (b ^ 2 * c - b ^ 2 * a), sq_nonneg (c ^ 2 * a - c ^ 2 * b),
      sq_nonneg (a * b * c * (a - b)), sq_nonneg (a * b * c * (b - c)), sq_nonneg (a * b * c * (c - a)),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁, mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂),
      mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃), mul_pos (sq_pos_of_pos h₃) (sq_pos_of_pos h₁)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_92 : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ |x * y + y * z + z * x| := by
  intro x y z
  have h_main : x ^ 2 + y ^ 2 + z ^ 2 ≥ |x * y + y * z + z * x| := by
    by_cases h : x * y + y * z + z * x ≥ 0
    · -- Case 1: S ≥ 0
      have h₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      -- Since S ≥ 0, |S| = S
      have h₂ : |x * y + y * z + z * x| = x * y + y * z + z * x := by
        rw [abs_of_nonneg h]
      rw [h₂]
      linarith
    · -- Case 2: S < 0
      have h₁ : x ^ 2 + y ^ 2 + z ^ 2 ≥ -(x * y + y * z + z * x) := by
        have h₂ : 0 ≤ (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 := by positivity
        nlinarith
      -- Since S < 0, |S| = -S
      have h₂ : |x * y + y * z + z * x| = -(x * y + y * z + z * x) := by
        rw [abs_of_nonpos (by linarith)]
        <;> linarith
      rw [h₂]
      linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_93 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ 1 / a + 1 / b + 1 / c := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b * c := by positivity
  have h₅ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₅₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by positivity
    have h₅₂ : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      ring_nf
      <;>
      linarith
    have h₅₃ : 0 ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by linarith
    have h₅₄ : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a) := by linarith
    linarith
  
  have h₆ : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ (a * b + b * c + c * a) / (a * b * c) := by
    -- Use the fact that a² + b² + c² ≥ ab + bc + ca and divide both sides by abc (positive)
    have h₆₁ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := h₅
    have h₆₂ : 0 < a * b * c := h₄
    -- Divide both sides by abc to get the desired inequality
    have h₆₃ : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ (a * b + b * c + c * a) / (a * b * c) := by
      -- Use the property of inequalities with positive denominators
      exact (div_le_div_iff (by positivity) (by positivity)).mpr (by nlinarith)
    exact h₆₃
  
  have h₇ : (a * b + b * c + c * a) / (a * b * c) = 1 / a + 1 / b + 1 / c := by
    have h₇₁ : (a * b + b * c + c * a) / (a * b * c) = 1 / a + 1 / b + 1 / c := by
      have h₇₂ : 0 < a * b := by positivity
      have h₇₃ : 0 < b * c := by positivity
      have h₇₄ : 0 < c * a := by positivity
      calc
        (a * b + b * c + c * a) / (a * b * c) = (a * b + b * c + c * a) / (a * b * c) := by rfl
        _ = (a * b) / (a * b * c) + (b * c) / (a * b * c) + (c * a) / (a * b * c) := by
          have h₇₅ : (a * b + b * c + c * a) / (a * b * c) = (a * b) / (a * b * c) + (b * c) / (a * b * c) + (c * a) / (a * b * c) := by
            field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> ring_nf
            <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> ring_nf
            <;> nlinarith
          rw [h₇₅]
        _ = 1 / c + 1 / a + 1 / b := by
          have h₇₆ : (a * b) / (a * b * c) = 1 / c := by
            field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> ring_nf
            <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> nlinarith
          have h₇₇ : (b * c) / (a * b * c) = 1 / a := by
            field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> ring_nf
            <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> nlinarith
          have h₇₈ : (c * a) / (a * b * c) = 1 / b := by
            field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> ring_nf
            <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
            <;> nlinarith
          rw [h₇₆, h₇₇, h₇₈]
          <;> ring_nf
        _ = 1 / a + 1 / b + 1 / c := by ring
    rw [h₇₁]
  
  have h₈ : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ 1 / a + 1 / b + 1 / c := by
    have h₈₁ : (a ^ 2 + b ^ 2 + c ^ 2) / (a * b * c) ≥ (a * b + b * c + c * a) / (a * b * c) := h₆
    have h₈₂ : (a * b + b * c + c * a) / (a * b * c) = 1 / a + 1 / b + 1 / c := h₇
    linarith
  
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_94 : ∀ (x y z : ℝ), x < y ∧ y < z → (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0 := by
  intro x y z h
  have h₁ : y - x > 0 := by
    have h₁₁ : x < y := h.1
    linarith
  
  have h₂ : z - y > 0 := by
    have h₂₁ : y < z := h.2
    linarith
  
  have h₃ : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 = 3 * (y - x) * (z - y) * ((y - x) + (z - y)) := by
    have h₃₁ : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 = 3 * (y - x) * (z - y) * ((y - x) + (z - y)) := by
      have h₃₂ : (x - y) = -(y - x) := by ring
      have h₃₃ : (y - z) = -(z - y) := by ring
      have h₃₄ : (z - x) = (z - y) + (y - x) := by ring
      rw [h₃₂, h₃₃, h₃₄]
      ring_nf
      <;>
      nlinarith [sq_nonneg (y - x), sq_nonneg (z - y), sq_nonneg ((y - x) + (z - y))]
    rw [h₃₁]
  
  have h₄ : 3 * (y - x) * (z - y) * ((y - x) + (z - y)) > 0 := by
    have h₄₁ : y - x > 0 := h₁
    have h₄₂ : z - y > 0 := h₂
    have h₄₃ : (y - x) + (z - y) > 0 := by linarith
    have h₄₄ : 3 * (y - x) * (z - y) * ((y - x) + (z - y)) > 0 := by
      have h₄₅ : 0 < y - x := by linarith
      have h₄₆ : 0 < z - y := by linarith
      have h₄₇ : 0 < (y - x) + (z - y) := by linarith
      have h₄₈ : 0 < (y - x) * (z - y) := by positivity
      have h₄₉ : 0 < 3 * (y - x) * (z - y) := by positivity
      have h₅₀ : 0 < 3 * (y - x) * (z - y) * ((y - x) + (z - y)) := by positivity
      linarith
    exact h₄₄
  
  have h₅ : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0 := by
    rw [h₃]
    exact h₄
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_helpful_inequality : ∀ (a b x y : ℝ), x > 0 ∧ y > 0 → a ^ 2 / x + b ^ 2 / y ≥ (a + b) ^ 2 / (x + y) := by
  intro a b x y hxy
  have h_denom_pos : x > 0 ∧ y > 0 ∧ x + y > 0 := by
    have hx : x > 0 := hxy.1
    have hy : y > 0 := hxy.2
    refine' ⟨hx, hy, _⟩
    -- Prove that x + y > 0 using the fact that x > 0 and y > 0
    linarith
  
  have h_common_denom : a ^ 2 / x + b ^ 2 / y - (a + b) ^ 2 / (x + y) = (a * y - b * x) ^ 2 / (x * y * (x + y)) := by
    have hx : x > 0 := h_denom_pos.1
    have hy : y > 0 := h_denom_pos.2.1
    have hxy : x + y > 0 := h_denom_pos.2.2
    have h1 : a ^ 2 / x + b ^ 2 / y - (a + b) ^ 2 / (x + y) = (a ^ 2 / x + b ^ 2 / y) - (a + b) ^ 2 / (x + y) := by ring
    rw [h1]
    have h2 : a ^ 2 / x + b ^ 2 / y = (a ^ 2 * y + b ^ 2 * x) / (x * y) := by
      have h3 : a ^ 2 / x + b ^ 2 / y = (a ^ 2 * y) / (x * y) + (b ^ 2 * x) / (x * y) := by
        field_simp [hx.ne', hy.ne']
        <;> ring
        <;> field_simp [hx.ne', hy.ne']
        <;> ring
      rw [h3]
      have h4 : (a ^ 2 * y) / (x * y) + (b ^ 2 * x) / (x * y) = (a ^ 2 * y + b ^ 2 * x) / (x * y) := by
        field_simp [hx.ne', hy.ne']
        <;> ring
      rw [h4]
      <;> ring
    rw [h2]
    have h3 : (a ^ 2 * y + b ^ 2 * x) / (x * y) - (a + b) ^ 2 / (x + y) = ((a ^ 2 * y + b ^ 2 * x) * (x + y) - (a + b) ^ 2 * (x * y)) / (x * y * (x + y)) := by
      have h4 : x * y > 0 := mul_pos hx hy
      have h5 : x + y > 0 := hxy
      field_simp [h4.ne', h5.ne', hx.ne', hy.ne']
      <;> ring
      <;> field_simp [h4.ne', h5.ne', hx.ne', hy.ne']
      <;> ring
    rw [h3]
    have h4 : ((a ^ 2 * y + b ^ 2 * x) * (x + y) - (a + b) ^ 2 * (x * y)) = (a * y - b * x) ^ 2 := by
      nlinarith [sq_nonneg (a * y - b * x)]
    rw [h4]
    <;> field_simp [hx.ne', hy.ne', h_denom_pos.2.2.ne']
    <;> ring
    <;> field_simp [hx.ne', hy.ne', h_denom_pos.2.2.ne']
    <;> ring
  
  have h_main : (a * y - b * x) ^ 2 / (x * y * (x + y)) ≥ 0 := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have hxy : 0 < x + y := by linarith
    have hxy_pos : 0 < x * y * (x + y) := by positivity
    have h_num_nonneg : (a * y - b * x) ^ 2 ≥ 0 := by nlinarith
    -- The square of any real number is non-negative, so the numerator is non-negative.
    -- The denominator is positive because x, y, and x + y are positive.
    -- Therefore, the fraction is non-negative.
    exact div_nonneg h_num_nonneg (by positivity)
  
  have h_final : a ^ 2 / x + b ^ 2 / y ≥ (a + b) ^ 2 / (x + y) := by
    have h₁ : a ^ 2 / x + b ^ 2 / y - (a + b) ^ 2 / (x + y) ≥ 0 := by
      linarith
    linarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_6_6 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 :=
  by
  have h_main_inequality : ∀ (x y : ℝ), x > 0 → y > 0 → x / y + y / x ≥ 2 := by
    intro x y hx hy
    have hxy : 0 < x * y := mul_pos hx hy
    field_simp [hx.ne', hy.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (x - y)]
  
  intro a b c h
  have h₁ : a > 0 := by
    linarith
  
  have h₂ : b > 0 := by
    linarith
  
  have h₃ : c > 0 := by
    linarith
  
  have h₄ : (b + c) > 0 := by
    linarith
  
  have h₅ : (a + c) > 0 := by
    linarith
  
  have h₆ : (a + b) > 0 := by
    linarith
  
  have h₇ : 2 * (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 := by
    have h₇₁ : 0 < (b + c) := by linarith
    have h₇₂ : 0 < (a + c) := by linarith
    have h₇₃ : 0 < (a + b) := by linarith
    have h₇₄ : (b + c) / (a + c) + (a + c) / (b + c) ≥ 2 := by
      apply h_main_inequality
      <;> linarith
    have h₇₅ : (b + c) / (a + b) + (a + b) / (b + c) ≥ 2 := by
      apply h_main_inequality
      <;> linarith
    have h₇₆ : (a + c) / (a + b) + (a + b) / (a + c) ≥ 2 := by
      apply h_main_inequality
      <;> linarith
    have h₇₇ : 2 * (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 := by
      have h₇₈ : 0 < (b + c) * (a + c) := by positivity
      have h₇₉ : 0 < (b + c) * (a + b) := by positivity
      have h₇₁₀ : 0 < (a + c) * (a + b) := by positivity
      field_simp [h₇₁.ne', h₇₂.ne', h₇₃.ne']
      rw [le_div_iff (by positivity)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃,
        mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
        mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃),
        mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃)]
    exact h₇₇
  
  have h₈ : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 / 2 := by
    have h₈₁ : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 / 2 := by
      -- Use the given inequality h₇ to deduce the desired inequality
      have h₈₂ : 2 * (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 := h₇
      -- Divide both sides of the inequality by 2 to get the desired result
      linarith
    exact h₈₁
  
  have h₉ : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = 3 + (a / (b + c) + b / (a + c) + c / (a + b)) := by
    have h₉₁ : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = (a + b + c) * (1 / (b + c)) + (a + b + c) * (1 / (a + c)) + (a + b + c) * (1 / (a + b)) := by
      ring
    rw [h₉₁]
    have h₉₂ : (a + b + c) * (1 / (b + c)) = (a + b + c) / (b + c) := by
      field_simp
      <;> ring
    have h₉₃ : (a + b + c) * (1 / (a + c)) = (a + b + c) / (a + c) := by
      field_simp
      <;> ring
    have h₉₄ : (a + b + c) * (1 / (a + b)) = (a + b + c) / (a + b) := by
      field_simp
      <;> ring
    rw [h₉₂, h₉₃, h₉₄]
    have h₉₅ : (a + b + c) / (b + c) = 1 + a / (b + c) := by
      have h₉₅₁ : (a + b + c) / (b + c) = (a + (b + c)) / (b + c) := by ring
      rw [h₉₅₁]
      field_simp [h₄.ne']
      <;> ring
      <;> field_simp [h₄.ne']
      <;> ring
    have h₉₆ : (a + b + c) / (a + c) = 1 + b / (a + c) := by
      have h₉₆₁ : (a + b + c) / (a + c) = (b + (a + c)) / (a + c) := by ring
      rw [h₉₆₁]
      field_simp [h₅.ne']
      <;> ring
      <;> field_simp [h₅.ne']
      <;> ring
    have h₉₇ : (a + b + c) / (a + b) = 1 + c / (a + b) := by
      have h₉₇₁ : (a + b + c) / (a + b) = (c + (a + b)) / (a + b) := by ring
      rw [h₉₇₁]
      field_simp [h₆.ne']
      <;> ring
      <;> field_simp [h₆.ne']
      <;> ring
    rw [h₉₅, h₉₆, h₉₇]
    <;> ring
    <;> field_simp [h₄.ne', h₅.ne', h₆.ne']
    <;> ring
  
  have h₁₀ : 3 + (a / (b + c) + b / (a + c) + c / (a + b)) ≥ 9 / 2 := by
    have h₁₀₁ : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) = 3 + (a / (b + c) + b / (a + c) + c / (a + b)) := by
      linarith
    have h₁₀₂ : (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 / 2 := by
      linarith
    linarith
  
  have h₁₁ : a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
    linarith
  
  have h₁₂ : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    have h₁₃ : b / (a + c) = b / (c + a) := by
      ring_nf
    have h₁₄ : a / (b + c) + b / (a + c) + c / (a + b) = a / (b + c) + b / (c + a) + c / (a + b) := by
      rw [h₁₃]
      <;> ring_nf
    rw [h₁₄] at h₁₁
    linarith
  
  exact h₁₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_6_7 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1 := by
  intro a b c h
  have h_main : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    field_simp
    rw [le_div_iff (by positivity)]
    -- Use nlinarith to handle the inequality after simplification
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
      sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_98 : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
  intro a b c d h
  have h₁ : 1 / a + 1 / b ≥ 4 / (a + b) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < a + b := by linarith
    have h₁₄ : 0 < a * b := by positivity
    field_simp [h₁₁.ne', h₁₂.ne', h₁₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

  have h₂ : 1 / c + 4 / d ≥ 9 / (c + d) := by
    have h₂₁ : 0 < c := by linarith
    have h₂₂ : 0 < d := by linarith
    have h₂₃ : 0 < c + d := by linarith
    have h₂₄ : 0 < c * d := by positivity
    field_simp [h₂₁.ne', h₂₂.ne', h₂₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (c - 2 * d), sq_nonneg (c + d), sq_nonneg (2 * c - d)]

  have h₃ : 4 / c + 16 / d ≥ 36 / (c + d) := by
    have h₃₁ : 0 < c := by linarith
    have h₃₂ : 0 < d := by linarith
    have h₃₃ : 0 < c + d := by linarith
    have h₃₄ : 0 < c * d := by positivity
    have h₃₅ : 1 / c + 4 / d ≥ 9 / (c + d) := h₂
    have h₃₆ : 4 / c + 16 / d = 4 * (1 / c + 4 / d) := by
      ring
      <;> field_simp [h₃₁.ne', h₃₂.ne']
      <;> ring
    rw [h₃₆]
    have h₃₇ : 4 * (1 / c + 4 / d) ≥ 4 * (9 / (c + d)) := by
      gcongr
    have h₃₈ : 4 * (9 / (c + d)) = 36 / (c + d) := by
      ring
      <;> field_simp [h₃₃.ne']
      <;> ring
    linarith

  have h₄ : 1 / a + 1 / b + 4 / c + 16 / d ≥ 4 / (a + b) + 36 / (c + d) := by
    have h₄₁ : 1 / a + 1 / b + 4 / c + 16 / d = (1 / a + 1 / b) + (4 / c + 16 / d) := by ring
    rw [h₄₁]
    linarith

  have h₅ : ∀ (x y : ℝ), x > 0 → y > 0 → 4 / x + 36 / y ≥ 64 / (x + y) := by
    intro x y hx hy
    have h₅₁ : 0 < x := hx
    have h₅₂ : 0 < y := hy
    have h₅₃ : 0 < x + y := by positivity
    have h₅₄ : 0 < x * y := by positivity
    have h₅₅ : 0 < x * y * (x + y) := by positivity
    field_simp [h₅₁.ne', h₅₂.ne', h₅₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (3 * x - y), sq_nonneg (x - 3 * y), sq_nonneg (x + y)]

  have h₆ : 4 / (a + b) + 36 / (c + d) ≥ 64 / (a + b + c + d) := by
    have h₆₁ : 0 < a + b := by linarith
    have h₆₂ : 0 < c + d := by linarith
    have h₆₃ : 0 < a + b + c + d := by linarith
    have h₆₄ : 4 / (a + b) + 36 / (c + d) ≥ 64 / (a + b + c + d) := by
      have h₆₅ : 4 / (a + b) + 36 / (c + d) ≥ 64 / ((a + b) + (c + d)) := by
        have h₆₆ := h₅ (a + b) (c + d) (by linarith) (by linarith)
        have h₆₇ : (a + b) + (c + d) = (a + b) + (c + d) := rfl
        have h₆₈ : 64 / ((a + b) + (c + d)) = 64 / ((a + b) + (c + d)) := rfl
        -- Use the given inequality h₅ to get the desired result
        calc
          4 / (a + b) + 36 / (c + d) ≥ 64 / ((a + b) + (c + d)) := by
            -- Apply the inequality from h₅
            have h₆₉ := h₅ (a + b) (c + d) (by linarith) (by linarith)
            -- Simplify the right-hand side to match the form in h₅
            have h₇₀ : 64 / ((a + b) + (c + d)) = 64 / ((a + b) + (c + d)) := rfl
            linarith
          _ = 64 / ((a + b) + (c + d)) := by rfl
      have h₆₉ : (a + b) + (c + d) = a + b + c + d := by ring
      rw [h₆₉] at h₆₅
      linarith
    exact h₆₄

  have h₇ : 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
    linarith

  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_99 : ∀ (a b : ℝ), a > 0 ∧ b > 0 → 8 * (a ^ 4 + b ^ 4) ≥ (a + b) ^ 4 := by
  intro a b h
  have h_main : 8 * (a ^ 4 + b ^ 4) - (a + b) ^ 4 = 3 * (a ^ 2 - b ^ 2) ^ 2 + 4 * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) := by
    have h₁ : (a + b) ^ 4 = a ^ 4 + 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 + b ^ 4 := by
      ring
    rw [h₁]
    have h₂ : 8 * (a ^ 4 + b ^ 4) - (a ^ 4 + 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 + b ^ 4) = 3 * (a ^ 2 - b ^ 2) ^ 2 + 4 * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) := by
      ring_nf
      <;>
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
        sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a ^ 2 - a * b), sq_nonneg (a * b - b ^ 2)]
    linarith
  
  have h_nonneg : 3 * (a ^ 2 - b ^ 2) ^ 2 + 4 * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) ≥ 0 := by
    have h₁ : 3 * (a ^ 2 - b ^ 2) ^ 2 ≥ 0 := by positivity
    have h₂ : 4 * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) ≥ 0 := by
      have h₃ : (a - b) ^ 2 ≥ 0 := by positivity
      have h₄ : a ^ 2 + a * b + b ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
      have h₅ : 4 * (a - b) ^ 2 ≥ 0 := by positivity
      have h₆ : 4 * (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) ≥ 0 := by
        nlinarith
      exact h₆
    nlinarith
  
  have h_final : 8 * (a ^ 4 + b ^ 4) ≥ (a + b) ^ 4 := by
    have h₁ : 8 * (a ^ 4 + b ^ 4) - (a + b) ^ 4 ≥ 0 := by
      linarith
    linarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_100 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 9 / (x + y + z) := by
  intro x y z h
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < z := by linarith
  have h₄ : 0 < x + y := by linarith
  have h₅ : 0 < y + z := by linarith
  have h₆ : 0 < z + x := by linarith
  have h₇ : 0 < x + y + z := by linarith
  have h₈ : 0 < (x + y) * (y + z) * (z + x) := by positivity
  -- Use the AM-HM inequality to prove the main inequality
  have h₉ : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 9 / (x + y + z) := by
    have h₁₀ : 0 < x + y + z := by linarith
    have h₁₁ : 0 < (x + y) * (y + z) * (z + x) := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to prove the inequality after clearing denominators
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
      mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂),
      mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃),
      mul_pos (sq_pos_of_pos h₃) (sq_pos_of_pos h₁)]
  exact h₉

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
  have h₆ : 0 < a + b := by linarith
  have h₇ : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h₈ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y) := by
    have h₈₁ : x / (a * y + b * z) = x ^ 2 / (a * x * y + b * x * z) := by
      have h₈₁₁ : 0 < a * y + b * z := by positivity
      have h₈₁₂ : 0 < a * x * y + b * x * z := by positivity
      have h₈₁₃ : 0 < x := by positivity
      have h₈₁₄ : 0 < a * x * y + b * x * z := by positivity
      -- We need to show that x / (a * y + b * z) = x ^ 2 / (a * x * y + b * x * z)
      -- This can be done by showing that (a * x * y + b * x * z) = x * (a * y + b * z)
      have h₈₁₅ : a * x * y + b * x * z = x * (a * y + b * z) := by ring
      rw [h₈₁₅]
      field_simp [h₈₁₁.ne', h₈₁₃.ne']
      <;> ring_nf
      <;> field_simp [h₈₁₁.ne', h₈₁₃.ne']
      <;> ring_nf
      <;> nlinarith
    have h₈₂ : y / (a * z + b * x) = y ^ 2 / (a * y * z + b * y * x) := by
      have h₈₂₁ : 0 < a * z + b * x := by positivity
      have h₈₂₂ : 0 < a * y * z + b * y * x := by positivity
      have h₈₂₃ : 0 < y := by positivity
      have h₈₂₄ : 0 < a * y * z + b * y * x := by positivity
      -- We need to show that y / (a * z + b * x) = y ^ 2 / (a * y * z + b * y * x)
      -- This can be done by showing that (a * y * z + b * y * x) = y * (a * z + b * x)
      have h₈₂₅ : a * y * z + b * y * x = y * (a * z + b * x) := by ring
      rw [h₈₂₅]
      field_simp [h₈₂₁.ne', h₈₂₃.ne']
      <;> ring_nf
      <;> field_simp [h₈₂₁.ne', h₈₂₃.ne']
      <;> ring_nf
      <;> nlinarith
    have h₈₃ : z / (a * x + b * y) = z ^ 2 / (a * z * x + b * z * y) := by
      have h₈₃₁ : 0 < a * x + b * y := by positivity
      have h₈₃₂ : 0 < a * z * x + b * z * y := by positivity
      have h₈₃₃ : 0 < z := by positivity
      have h₈₃₄ : 0 < a * z * x + b * z * y := by positivity
      -- We need to show that z / (a * x + b * y) = z ^ 2 / (a * z * x + b * z * y)
      -- This can be done by showing that (a * z * x + b * z * y) = z * (a * x + b * y)
      have h₈₃₅ : a * z * x + b * z * y = z * (a * x + b * y) := by ring
      rw [h₈₃₅]
      field_simp [h₈₃₁.ne', h₈₃₃.ne']
      <;> ring_nf
      <;> field_simp [h₈₃₁.ne', h₈₃₃.ne']
      <;> ring_nf
      <;> nlinarith
    -- Combine the results
    calc
      x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = x ^ 2 / (a * x * y + b * x * z) + y / (a * z + b * x) + z / (a * x + b * y) := by rw [h₈₁]
      _ = x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z / (a * x + b * y) := by rw [h₈₂]
      _ = x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y) := by rw [h₈₃]
  
  have h₉ : x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y) ≥ (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) := by
    have h₉₁ : 0 < a * x * y + b * x * z := by positivity
    have h₉₂ : 0 < a * y * z + b * y * x := by positivity
    have h₉₃ : 0 < a * z * x + b * z * y := by positivity
    have h₉₄ : 0 < (a * x * y + b * x * z) * (a * y * z + b * y * x) := by positivity
    have h₉₅ : 0 < (a * x * y + b * x * z) * (a * z * x + b * z * y) := by positivity
    have h₉₆ : 0 < (a * y * z + b * y * x) * (a * z * x + b * z * y) := by positivity
    -- Use the Titu's lemma (a special case of Cauchy-Schwarz) to bound the sum of squares
    have h₉₇ : (x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y)) ≥ (x + y + z) ^ 2 / ((a * x * y + b * x * z) + (a * y * z + b * y * x) + (a * z * x + b * z * y)) := by
      -- Prove the inequality using the Titu's lemma
      have h₉₇₁ : 0 < a * x * y + b * x * z := by positivity
      have h₉₇₂ : 0 < a * y * z + b * y * x := by positivity
      have h₉₇₃ : 0 < a * z * x + b * z * y := by positivity
      -- Use the Titu's lemma to bound the sum of squares
      have h₉₇₄ : (x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y)) ≥ (x + y + z) ^ 2 / ((a * x * y + b * x * z) + (a * y * z + b * y * x) + (a * z * x + b * z * y)) := by
        -- Use the Titu's lemma to bound the sum of squares
        field_simp [h₉₇₁.ne', h₉₇₂.ne', h₉₇₃.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x * (a * y * z + b * y * x) - y * (a * x * y + b * x * z)),
          sq_nonneg (y * (a * z * x + b * z * y) - z * (a * y * z + b * y * x)),
          sq_nonneg (z * (a * x * y + b * x * z) - x * (a * z * x + b * z * y))]
      linarith
    -- Simplify the denominator
    have h₉₈ : (a * x * y + b * x * z) + (a * y * z + b * y * x) + (a * z * x + b * z * y) = (a + b) * (x * y + y * z + z * x) := by
      ring_nf
      <;>
      nlinarith
    -- Combine the results to get the final inequality
    have h₉₉ : (x + y + z) ^ 2 / ((a * x * y + b * x * z) + (a * y * z + b * y * x) + (a * z * x + b * z * y)) = (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) := by
      rw [h₉₈]
    linarith
  
  have h₁₀ : (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
    have h₁₀₁ : 0 < x * y + y * z + z * x := by positivity
    have h₁₀₂ : 0 < (a + b) * (x * y + y * z + z * x) := by positivity
    have h₁₀₃ : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := h₇
    have h₁₀₄ : (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
      -- Use the fact that (x + y + z)^2 ≥ 3(xy + yz + zx) to prove the inequality
      calc
        (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) ≥ (3 * (x * y + y * z + z * x)) / ((a + b) * (x * y + y * z + z * x)) := by
          -- Since (x + y + z)^2 ≥ 3(xy + yz + zx), we can replace the numerator
          gcongr
          <;> nlinarith
        _ = 3 / (a + b) := by
          -- Simplify the fraction
          have h₁₀₅ : (3 * (x * y + y * z + z * x)) / ((a + b) * (x * y + y * z + z * x)) = 3 / (a + b) := by
            have h₁₀₅₁ : (a + b) * (x * y + y * z + z * x) ≠ 0 := by positivity
            field_simp [h₁₀₅₁]
            <;> ring_nf
            <;> field_simp [h₁₀₁.ne']
            <;> ring_nf
          rw [h₁₀₅]
    exact h₁₀₄
  
  have h₁₁ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
    calc
      x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y) := by rw [h₈]
      _ ≥ (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) := by exact h₉
      _ ≥ 3 / (a + b) := by exact h₁₀
  
  exact h₁₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_102 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) ≥ a + b + c := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : (a ^ 2 + b ^ 2) / (a + b) ≥ (a + b) / 2 := by
    -- Use the AM-GM inequality to show that (a² + b²)/(a + b) ≥ (a + b)/2
    have h₄₁ : 0 < a + b := by linarith
    have h₄₂ : 0 < a * b := by positivity
    field_simp [h₄₁.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  have h₅ : (b ^ 2 + c ^ 2) / (b + c) ≥ (b + c) / 2 := by
    -- Use the AM-GM inequality to show that (b² + c²)/(b + c) ≥ (b + c)/2
    have h₅₁ : 0 < b + c := by linarith
    have h₅₂ : 0 < b * c := by positivity
    field_simp [h₅₁.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (b - c)]
  have h₆ : (c ^ 2 + a ^ 2) / (c + a) ≥ (c + a) / 2 := by
    -- Use the AM-GM inequality to show that (c² + a²)/(c + a) ≥ (c + a)/2
    have h₆₁ : 0 < c + a := by linarith
    have h₆₂ : 0 < c * a := by positivity
    field_simp [h₆₁.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (c - a)]
  -- Sum the three inequalities to get the final result
  have h₇ : (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) ≥ (a + b) / 2 + (b + c) / 2 + (c + a) / 2 := by
    linarith
  have h₈ : (a + b) / 2 + (b + c) / 2 + (c + a) / 2 = a + b + c := by
    ring
  linarith

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
    have h₅ : 0 < x * z := by positivity
    have h₆ : 0 < y * z := by positivity
    have h₇ : 0 < x + y + z := by positivity
    have h₈ : 0 < x + 2 * y + 3 * z := by positivity
    have h₉ : 0 < y + 2 * z + 3 * x := by positivity
    have h₁₀ : 0 < z + 2 * x + 3 * y := by positivity
    -- Use Titu's lemma to get a lower bound
    have h₁₁ : (x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y)) ≥ (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 5 * (x * y + x * z + y * z)) := by
      have h₁₁₁ : 0 < x + 2 * y + 3 * z := by positivity
      have h₁₁₂ : 0 < y + 2 * z + 3 * x := by positivity
      have h₁₁₃ : 0 < z + 2 * x + 3 * y := by positivity
      have h₁₁₄ : 0 < x * (x + 2 * y + 3 * z) := by positivity
      have h₁₁₅ : 0 < y * (y + 2 * z + 3 * x) := by positivity
      have h₁₁₆ : 0 < z * (z + 2 * x + 3 * y) := by positivity
      -- Use the Cauchy-Schwarz inequality to prove the Titu's lemma form
      have h₁₁₇ : (x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y)) = (x ^ 2 / (x ^ 2 + 2 * x * y + 3 * x * z) + y ^ 2 / (y ^ 2 + 2 * y * z + 3 * y * x) + z ^ 2 / (z ^ 2 + 2 * z * x + 3 * z * y)) := by
        have h₁₁₇₁ : x ^ 2 / (x ^ 2 + 2 * x * y + 3 * x * z) = x / (x + 2 * y + 3 * z) := by
          have h₁₁₇₁₁ : x ^ 2 + 2 * x * y + 3 * x * z = x * (x + 2 * y + 3 * z) := by ring
          rw [h₁₁₇₁₁]
          field_simp [h₁.ne']
          <;> ring
          <;> field_simp [h₁.ne']
          <;> ring
        have h₁₁₇₂ : y ^ 2 / (y ^ 2 + 2 * y * z + 3 * y * x) = y / (y + 2 * z + 3 * x) := by
          have h₁₁₇₂₁ : y ^ 2 + 2 * y * z + 3 * y * x = y * (y + 2 * z + 3 * x) := by ring
          rw [h₁₁₇₂₁]
          field_simp [h₂.ne']
          <;> ring
          <;> field_simp [h₂.ne']
          <;> ring
        have h₁₁₇₃ : z ^ 2 / (z ^ 2 + 2 * z * x + 3 * z * y) = z / (z + 2 * x + 3 * y) := by
          have h₁₁₇₃₁ : z ^ 2 + 2 * z * x + 3 * z * y = z * (z + 2 * x + 3 * y) := by ring
          rw [h₁₁₇₃₁]
          field_simp [h₃.ne']
          <;> ring
          <;> field_simp [h₃.ne']
          <;> ring
        calc
          (x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y)) = (x / (x + 2 * y + 3 * z) + y / (y + 2 * z + 3 * x) + z / (z + 2 * x + 3 * y)) := rfl
          _ = (x ^ 2 / (x ^ 2 + 2 * x * y + 3 * x * z) + y ^ 2 / (y ^ 2 + 2 * y * z + 3 * y * x) + z ^ 2 / (z ^ 2 + 2 * z * x + 3 * z * y)) := by
            rw [h₁₁₇₁, h₁₁₇₂, h₁₁₇₃]
            <;> ring
      rw [h₁₁₇]
      have h₁₁₈ : (x ^ 2 / (x ^ 2 + 2 * x * y + 3 * x * z) + y ^ 2 / (y ^ 2 + 2 * y * z + 3 * y * x) + z ^ 2 / (z ^ 2 + 2 * z * x + 3 * z * y)) ≥ (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 5 * (x * y + x * z + y * z)) := by
        -- Use the Cauchy-Schwarz inequality to prove the Titu's lemma form
        have h₁₁₈₁ : 0 < x ^ 2 + 2 * x * y + 3 * x * z := by positivity
        have h₁₁₈₂ : 0 < y ^ 2 + 2 * y * z + 3 * y * x := by positivity
        have h₁₁₈₃ : 0 < z ^ 2 + 2 * z * x + 3 * z * y := by positivity
        have h₁₁₈₄ : 0 < (x ^ 2 + 2 * x * y + 3 * x * z) * (y ^ 2 + 2 * y * z + 3 * y * x) * (z ^ 2 + 2 * z * x + 3 * z * y) := by positivity
        field_simp
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x * (y ^ 2 + 2 * y * z + 3 * y * x) - y * (x ^ 2 + 2 * x * y + 3 * x * z)),
          sq_nonneg (y * (z ^ 2 + 2 * z * x + 3 * z * y) - z * (y ^ 2 + 2 * y * z + 3 * y * x)),
          sq_nonneg (z * (x ^ 2 + 2 * x * y + 3 * x * z) - x * (z ^ 2 + 2 * z * x + 3 * z * y))]
      linarith
    -- Prove that (x + y + z)^2 / (x^2 + y^2 + z^2 + 5(xy + xz + yz)) ≥ 1/2
    have h₁₂ : (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 5 * (x * y + x * z + y * z)) ≥ 1 / 2 := by
      have h₁₂₁ : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 5 * (x * y + x * z + y * z) := by positivity
      have h₁₂₂ : 2 * (x + y + z) ^ 2 ≥ x ^ 2 + y ^ 2 + z ^ 2 + 5 * (x * y + x * z + y * z) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      have h₁₂₃ : (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 5 * (x * y + x * z + y * z)) ≥ 1 / 2 := by
        rw [ge_iff_le]
        rw [le_div_iff (by positivity)]
        nlinarith
      exact h₁₂₃
    -- Combine the inequalities
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_104 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x ^ 2 / ((x + y) * (x + z)) + y ^ 2 / ((y + z) * (y + x)) + z ^ 2 / ((z + x) * (z + y)) ≥ 3 / 4 := by
  intro x y z h
  have h₁ : 0 < x := by linarith
  have h₂ : 0 < y := by linarith
  have h₃ : 0 < z := by linarith
  have h₄ : 0 < x * y := by positivity
  have h₅ : 0 < y * z := by positivity
  have h₆ : 0 < z * x := by positivity
  have h₇ : x * (y^2 + z^2) + y * (z^2 + x^2) + z * (x^2 + y^2) ≥ 6 * x * y * z := by
    have h₇₁ : x * (y^2 + z^2) ≥ x * (2 * y * z) := by
      have h₇₁₁ : y^2 + z^2 ≥ 2 * y * z := by
        nlinarith [sq_nonneg (y - z)]
      have h₇₁₂ : 0 ≤ x := by linarith
      nlinarith
    have h₇₂ : y * (z^2 + x^2) ≥ y * (2 * z * x) := by
      have h₇₂₁ : z^2 + x^2 ≥ 2 * z * x := by
        nlinarith [sq_nonneg (z - x)]
      have h₇₂₂ : 0 ≤ y := by linarith
      nlinarith
    have h₇₃ : z * (x^2 + y^2) ≥ z * (2 * x * y) := by
      have h₇₃₁ : x^2 + y^2 ≥ 2 * x * y := by
        nlinarith [sq_nonneg (x - y)]
      have h₇₃₂ : 0 ≤ z := by linarith
      nlinarith
    nlinarith
  
  have h₈ : x^2 * (y + z) + y^2 * (z + x) + z^2 * (x + y) ≥ 6 * x * y * z := by
    have h₈₁ : x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y) = x * (y ^ 2 + z ^ 2) + y * (z ^ 2 + x ^ 2) + z * (x ^ 2 + y ^ 2) := by
      ring
    rw [h₈₁]
    linarith
  
  have h₉ : 4 * (x^2 * (y + z) + y^2 * (z + x) + z^2 * (x + y)) ≥ 3 * ((x + y) * (y + z) * (z + x)) := by
    have h₉₁ : (x + y) * (y + z) * (z + x) = x^2 * (y + z) + y^2 * (z + x) + z^2 * (x + y) + 2 * x * y * z := by
      ring
    have h₉₂ : 4 * (x^2 * (y + z) + y^2 * (z + x) + z^2 * (x + y)) - 3 * ((x + y) * (y + z) * (z + x)) = x^2 * (y + z) + y^2 * (z + x) + z^2 * (x + y) - 6 * x * y * z := by
      rw [h₉₁]
      ring
    have h₉₃ : x^2 * (y + z) + y^2 * (z + x) + z^2 * (x + y) - 6 * x * y * z ≥ 0 := by
      linarith
    linarith
  
  have h₁₀ : x ^ 2 / ((x + y) * (x + z)) + y ^ 2 / ((y + z) * (y + x)) + z ^ 2 / ((z + x) * (z + y)) ≥ 3 / 4 := by
    have h₁₀₁ : 0 < (x + y) := by linarith
    have h₁₀₂ : 0 < (y + z) := by linarith
    have h₁₀₃ : 0 < (z + x) := by linarith
    have h₁₀₄ : 0 < (x + y) * (y + z) := by positivity
    have h₁₀₅ : 0 < (x + y) * (y + z) * (z + x) := by positivity
    have h₁₀₆ : 0 < (x + y) * (x + z) := by positivity
    have h₁₀₇ : 0 < (y + z) * (y + x) := by positivity
    have h₁₀₈ : 0 < (z + x) * (z + y) := by positivity
    have h₁₀₉ : x ^ 2 / ((x + y) * (x + z)) + y ^ 2 / ((y + z) * (y + x)) + z ^ 2 / ((z + x) * (z + y)) = (x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)) / ((x + y) * (y + z) * (z + x)) := by
      have h₁₀₉₁ : x ^ 2 / ((x + y) * (x + z)) = x ^ 2 * (y + z) / ((x + y) * (y + z) * (z + x)) := by
        field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
        <;> field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
      have h₁₀₉₂ : y ^ 2 / ((y + z) * (y + x)) = y ^ 2 * (z + x) / ((x + y) * (y + z) * (z + x)) := by
        field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
        <;> field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
      have h₁₀₉₃ : z ^ 2 / ((z + x) * (z + y)) = z ^ 2 * (x + y) / ((x + y) * (y + z) * (z + x)) := by
        field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
        <;> field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
      rw [h₁₀₉₁, h₁₀₉₂, h₁₀₉₃]
      have h₁₀₉₄ : x ^ 2 * (y + z) / ((x + y) * (y + z) * (z + x)) + y ^ 2 * (z + x) / ((x + y) * (y + z) * (z + x)) + z ^ 2 * (x + y) / ((x + y) * (y + z) * (z + x)) = (x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)) / ((x + y) * (y + z) * (z + x)) := by
        field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
        <;> field_simp [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄, h₁₀₅]
        <;> ring
      rw [h₁₀₉₄]
    rw [h₁₀₉]
    have h₁₀₁₀ : (x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)) / ((x + y) * (y + z) * (z + x)) ≥ 3 / 4 := by
      rw [ge_iff_le]
      rw [le_div_iff (by positivity)]
      nlinarith [h₉]
    linarith
  
  exact h₁₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_7_5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a + b) * (a + c) ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
  intro a b c h
  have h₁ : (a + b) * (a + c) = a * (a + b + c) + b * c := by
    have h₁₀ : (a + b) * (a + c) = a ^ 2 + a * c + a * b + b * c := by
      ring
    have h₁₁ : a * (a + b + c) + b * c = a ^ 2 + a * b + a * c + b * c := by
      ring
    linarith
  
  have h₂ : a * (a + b + c) + b * c ≥ 2 * Real.sqrt (a * (a + b + c) * (b * c)) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < a + b + c := by linarith
    have h₂₅ : 0 < a * (a + b + c) := by positivity
    have h₂₆ : 0 < b * c := by positivity
    have h₂₇ : 0 < a * (a + b + c) * (b * c) := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    have h₂₈ : a * (a + b + c) + b * c ≥ 2 * Real.sqrt (a * (a + b + c) * (b * c)) := by
      -- Apply the AM-GM inequality: for non-negative x, y, x + y ≥ 2 * sqrt(x * y)
      have h₂₉ : Real.sqrt (a * (a + b + c) * (b * c)) ≤ (a * (a + b + c) + b * c) / 2 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [sq_nonneg (a * (a + b + c) - b * c)]
      -- Multiply both sides by 2 to get the desired inequality
      nlinarith [h₂₉]
    exact h₂₈
  
  have h₃ : a * (a + b + c) * (b * c) = a * b * c * (a + b + c) := by
    have h₃₁ : a * (a + b + c) * (b * c) = a * (a + b + c) * b * c := by ring
    have h₃₂ : a * (a + b + c) * b * c = a * b * c * (a + b + c) := by ring
    linarith
  
  have h₄ : 2 * Real.sqrt (a * (a + b + c) * (b * c)) = 2 * Real.sqrt (a * b * c * (a + b + c)) := by
    have h₄₁ : a * (a + b + c) * (b * c) = a * b * c * (a + b + c) := by
      linarith
    have h₄₂ : Real.sqrt (a * (a + b + c) * (b * c)) = Real.sqrt (a * b * c * (a + b + c)) := by
      rw [h₄₁]
    linarith
  
  have h₅ : (a + b) * (a + c) ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
    have h₅₁ : (a + b) * (a + c) = a * (a + b + c) + b * c := by rw [h₁]
    have h₅₂ : a * (a + b + c) + b * c ≥ 2 * Real.sqrt (a * (a + b + c) * (b * c)) := by
      exact h₂
    have h₅₃ : 2 * Real.sqrt (a * (a + b + c) * (b * c)) = 2 * Real.sqrt (a * b * c * (a + b + c)) := by
      exact h₄
    have h₅₄ : a * (a + b + c) + b * c ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
      linarith
    linarith
  
  exact h₅

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
  have h₇ : Real.sqrt (a * b * c) ≤ (a * b + c) / 2 := by
    have h₇₁ : 0 ≤ a * b := by positivity
    have h₇₂ : 0 ≤ c := by positivity
    have h₇₃ : 0 ≤ a * b * c := by positivity
    -- Use the inequality involving squares to prove the desired inequality
    have h₇₄ : Real.sqrt (a * b * c) ≤ (a * b + c) / 2 := by
      -- Use the fact that the square of the difference is non-negative to derive the inequality
      have h₇₄₁ : 0 ≤ (a * b - c) ^ 2 := sq_nonneg (a * b - c)
      have h₇₄₂ : Real.sqrt (a * b * c) ≤ (a * b + c) / 2 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [sq_nonneg (a * b - c)]
      exact h₇₄₂
    exact h₇₄
  
  have h₈ : Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ ((1 - a) * (1 - b) + (1 - c)) / 2 := by
    have h₈₁ : 0 ≤ (1 - a) := by linarith
    have h₈₂ : 0 ≤ (1 - b) := by linarith
    have h₈₃ : 0 ≤ (1 - c) := by linarith
    have h₈₄ : 0 ≤ (1 - a) * (1 - b) := by positivity
    have h₈₅ : 0 ≤ (1 - a) * (1 - b) * (1 - c) := by positivity
    -- Use the AM-GM inequality to bound the square root term
    have h₈₆ : Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ ((1 - a) * (1 - b) + (1 - c)) / 2 := by
      -- Use the fact that the square of the difference is non-negative
      have h₈₆₁ : 0 ≤ ((1 - a) * (1 - b) - (1 - c)) ^ 2 := sq_nonneg _
      have h₈₆₂ : Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ ((1 - a) * (1 - b) + (1 - c)) / 2 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [sq_nonneg ((1 - a) * (1 - b) - (1 - c))]
      exact h₈₆₂
    exact h₈₆
  
  have h₉ : Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ 1 + a * b - (a + b) / 2 := by
    have h₉₁ : Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ (a * b + c) / 2 + ((1 - a) * (1 - b) + (1 - c)) / 2 := by
      linarith
    have h₉₂ : (a * b + c) / 2 + ((1 - a) * (1 - b) + (1 - c)) / 2 = 1 + a * b - (a + b) / 2 := by
      have h₉₂₁ : (a * b + c) / 2 + ((1 - a) * (1 - b) + (1 - c)) / 2 = (a * b + c + ((1 - a) * (1 - b) + (1 - c))) / 2 := by ring
      rw [h₉₂₁]
      have h₉₂₂ : a * b + c + ((1 - a) * (1 - b) + (1 - c)) = 2 + 2 * (a * b) - a - b := by
        ring_nf
        <;>
        nlinarith
      rw [h₉₂₂]
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
      <;> nlinarith
    linarith
  
  have h₁₀ : a * b < (a + b) / 2 := by
    have h₁₀₁ : 0 < a := by linarith
    have h₁₀₂ : 0 < b := by linarith
    by_cases h₁₀₃ : b ≤ 1 / 2
    · -- Case: b ≤ 1/2
      have h₁₀₄ : 0 < 1 - b := by linarith
      have h₁₀₅ : 0 < a * (1 - b) := by positivity
      nlinarith [mul_pos h₁₀₁ h₁₀₂]
    · -- Case: b > 1/2
      have h₁₀₄ : b > 1 / 2 := by linarith
      have h₁₀₅ : a < 1 := by linarith
      have h₁₀₆ : 0 < 1 - a := by linarith
      nlinarith [mul_pos h₁₀₆ h₁₀₂]
  
  have h₁₁ : 1 + a * b - (a + b) / 2 < 1 := by
    have h₁₁₁ : a * b < (a + b) / 2 := h₁₀
    linarith
  
  have h₁₂ : Real.sqrt (a * b * c) + Real.sqrt ((1 - a) * (1 - b) * (1 - c)) < 1 := by
    linarith
  
  exact h₁₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_109 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x ^ 3 / (x ^ 3 + 2 * y ^ 3) + y ^ 3 / (y ^ 3 + 2 * z ^ 3) + z ^ 3 / (z ^ 3 + 2 * x ^ 3) ≥ 1 := by
  intro x y z h
  have h₁ : x > 0 := by linarith
  have h₂ : y > 0 := by linarith
  have h₃ : z > 0 := by linarith
  have h₄ : x ^ 3 > 0 := by positivity
  have h₅ : y ^ 3 > 0 := by positivity
  have h₆ : z ^ 3 > 0 := by positivity
  have h₇ : x ^ 3 / (x ^ 3 + 2 * y ^ 3) + y ^ 3 / (y ^ 3 + 2 * z ^ 3) + z ^ 3 / (z ^ 3 + 2 * x ^ 3) ≥ 1 := by
    have h₈ : 0 < x ^ 3 := by positivity
    have h₉ : 0 < y ^ 3 := by positivity
    have h₁₀ : 0 < z ^ 3 := by positivity
    have h₁₁ : 0 < x ^ 3 * y ^ 3 := by positivity
    have h₁₂ : 0 < y ^ 3 * z ^ 3 := by positivity
    have h₁₃ : 0 < z ^ 3 * x ^ 3 := by positivity
    -- Use the identity a / (a + 2b) = a² / (a² + 2ab) and Titu's lemma
    have h₁₄ : (x ^ 3) ^ 2 / ((x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3)) + (y ^ 3) ^ 2 / ((y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3)) + (z ^ 3) ^ 2 / ((z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3)) ≥ 1 := by
      -- Apply Titu's lemma
      have h₁₅ : 0 < (x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3) := by positivity
      have h₁₆ : 0 < (y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3) := by positivity
      have h₁₇ : 0 < (z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3) := by positivity
      have h₁₈ : ((x ^ 3) ^ 2 / ((x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3)) + (y ^ 3) ^ 2 / ((y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3)) + (z ^ 3) ^ 2 / ((z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3))) ≥ (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 / ((x ^ 3) ^ 2 + (y ^ 3) ^ 2 + (z ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3) + 2 * (y ^ 3) * (z ^ 3) + 2 * (z ^ 3) * (x ^ 3)) := by
        -- Prove the inequality using the Cauchy-Schwarz inequality (Titu's lemma)
        have h₁₉ : 0 < (x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3) := by positivity
        have h₂₀ : 0 < (y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3) := by positivity
        have h₂₁ : 0 < (z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3) := by positivity
        -- Use the fact that the square of any real number is non-negative to prove the inequality
        have h₂₂ : 0 ≤ (x ^ 3 * ((y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3)) - y ^ 3 * ((x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3))) ^ 2 := by positivity
        have h₂₃ : 0 ≤ (y ^ 3 * ((z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3)) - z ^ 3 * ((y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3))) ^ 2 := by positivity
        have h₂₄ : 0 ≤ (z ^ 3 * ((x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3)) - x ^ 3 * ((z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3))) ^ 2 := by positivity
        -- Use the above inequalities to prove the desired result
        field_simp [h₁₅.ne', h₁₆.ne', h₁₇.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x ^ 3 * (y ^ 3) - y ^ 3 * (x ^ 3)),
          sq_nonneg (y ^ 3 * (z ^ 3) - z ^ 3 * (y ^ 3)),
          sq_nonneg (z ^ 3 * (x ^ 3) - x ^ 3 * (z ^ 3))]
      -- Simplify the denominator on the right side
      have h₂₅ : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 / ((x ^ 3) ^ 2 + (y ^ 3) ^ 2 + (z ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3) + 2 * (y ^ 3) * (z ^ 3) + 2 * (z ^ 3) * (x ^ 3)) = 1 := by
        have h₂₆ : (x ^ 3) ^ 2 + (y ^ 3) ^ 2 + (z ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3) + 2 * (y ^ 3) * (z ^ 3) + 2 * (z ^ 3) * (x ^ 3) = (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 := by
          ring
        rw [h₂₆]
        have h₂₇ : x ^ 3 + y ^ 3 + z ^ 3 > 0 := by positivity
        field_simp [h₂₇.ne']
        <;> ring_nf
        <;> field_simp [h₂₇.ne']
        <;> linarith
      -- Combine the inequalities to get the final result
      linarith
    -- Relate the expression using squares to the original expression
    have h₂₈ : (x ^ 3) ^ 2 / ((x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3)) = x ^ 3 / (x ^ 3 + 2 * y ^ 3) := by
      have h₂₉ : (x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3) = (x ^ 3) * (x ^ 3 + 2 * y ^ 3) := by ring
      rw [h₂₉]
      have h₃₀ : 0 < x ^ 3 + 2 * y ^ 3 := by positivity
      have h₃₁ : 0 < x ^ 3 := by positivity
      field_simp [h₃₀.ne', h₃₁.ne']
      <;> ring_nf
      <;> field_simp [h₃₀.ne', h₃₁.ne']
      <;> linarith
    have h₃₂ : (y ^ 3) ^ 2 / ((y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3)) = y ^ 3 / (y ^ 3 + 2 * z ^ 3) := by
      have h₃₃ : (y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3) = (y ^ 3) * (y ^ 3 + 2 * z ^ 3) := by ring
      rw [h₃₃]
      have h₃₄ : 0 < y ^ 3 + 2 * z ^ 3 := by positivity
      have h₃₅ : 0 < y ^ 3 := by positivity
      field_simp [h₃₄.ne', h₃₅.ne']
      <;> ring_nf
      <;> field_simp [h₃₄.ne', h₃₅.ne']
      <;> linarith
    have h₃₆ : (z ^ 3) ^ 2 / ((z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3)) = z ^ 3 / (z ^ 3 + 2 * x ^ 3) := by
      have h₃₇ : (z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3) = (z ^ 3) * (z ^ 3 + 2 * x ^ 3) := by ring
      rw [h₃₇]
      have h₃₈ : 0 < z ^ 3 + 2 * x ^ 3 := by positivity
      have h₃₉ : 0 < z ^ 3 := by positivity
      field_simp [h₃₈.ne', h₃₉.ne']
      <;> ring_nf
      <;> field_simp [h₃₈.ne', h₃₉.ne']
      <;> linarith
    -- Substitute back to the original expression
    calc
      x ^ 3 / (x ^ 3 + 2 * y ^ 3) + y ^ 3 / (y ^ 3 + 2 * z ^ 3) + z ^ 3 / (z ^ 3 + 2 * x ^ 3) = (x ^ 3) ^ 2 / ((x ^ 3) ^ 2 + 2 * (x ^ 3) * (y ^ 3)) + (y ^ 3) ^ 2 / ((y ^ 3) ^ 2 + 2 * (y ^ 3) * (z ^ 3)) + (z ^ 3) ^ 2 / ((z ^ 3) ^ 2 + 2 * (z ^ 3) * (x ^ 3)) := by
        rw [h₂₈, h₃₂, h₃₆]
      _ ≥ 1 := by
        linarith
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_110 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1 → 1 / (y * z + z) + 1 / (z * x + x) + 1 / (x * y + y) ≥ 3 / 2 := by
  intro x y z h
  have h₁ : 1 / (y * z + z) + 1 / (z * x + x) + 1 / (x * y + y) ≥ 3 / 2 := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have hz : 0 < z := by linarith
    have h₂ : x * y * z = 1 := by linarith
    have h₃ : 0 < x * y := by positivity
    have h₄ : 0 < y * z := by positivity
    have h₅ : 0 < z * x := by positivity
    -- Use the substitution a = x, b = 1, c = x * z to transform the inequality into Nesbitt's inequality
    have h₆ : 1 / (y * z + z) = x / (1 + x * z) := by
      have h₆₁ : y * z + z = (1 + x * z) / x := by
        have h₆₂ : x * y * z = 1 := by linarith
        field_simp [hx.ne', hy.ne', hz.ne']
        nlinarith [h₂]
      have h₆₃ : 1 / (y * z + z) = x / (1 + x * z) := by
        have h₆₄ : y * z + z > 0 := by positivity
        have h₆₅ : 1 + x * z > 0 := by positivity
        field_simp [h₆₄.ne', h₆₅.ne', h₆₁]
        <;> ring_nf at *
        <;> nlinarith [h₂]
      exact h₆₃
    have h₇ : 1 / (z * x + x) = y / (1 + y * x) := by
      have h₇₁ : z * x + x = (1 + y * x) / y := by
        have h₇₂ : x * y * z = 1 := by linarith
        field_simp [hx.ne', hy.ne', hz.ne']
        nlinarith [h₂]
      have h₇₃ : 1 / (z * x + x) = y / (1 + y * x) := by
        have h₇₄ : z * x + x > 0 := by positivity
        have h₇₅ : 1 + y * x > 0 := by positivity
        field_simp [h₇₄.ne', h₇₅.ne', h₇₁]
        <;> ring_nf at *
        <;> nlinarith [h₂]
      exact h₇₃
    have h₈ : 1 / (x * y + y) = z / (1 + z * y) := by
      have h₈₁ : x * y + y = (1 + z * y) / z := by
        have h₈₂ : x * y * z = 1 := by linarith
        field_simp [hx.ne', hy.ne', hz.ne']
        nlinarith [h₂]
      have h₈₃ : 1 / (x * y + y) = z / (1 + z * y) := by
        have h₈₄ : x * y + y > 0 := by positivity
        have h₈₅ : 1 + z * y > 0 := by positivity
        field_simp [h₈₄.ne', h₈₅.ne', h₈₁]
        <;> ring_nf at *
        <;> nlinarith [h₂]
      exact h₈₃
    rw [h₆, h₇, h₈]
    -- Prove that x / (1 + x * z) + y / (1 + y * x) + z / (1 + z * y) ≥ 3 / 2
    have h₉ : 0 < x * z := by positivity
    have h₁₀ : 0 < y * x := by positivity
    have h₁₁ : 0 < z * y := by positivity
    have h₁₂ : 0 < 1 + x * z := by positivity
    have h₁₃ : 0 < 1 + y * x := by positivity
    have h₁₄ : 0 < 1 + z * y := by positivity
    -- Use the fact that for positive reals a, b, c, the sum of a/(1+bc) etc. is at least 3/2 when abc = 1
    -- We can use the Titu's lemma or other inequalities to prove this
    have h₁₅ : x / (1 + x * z) + y / (1 + y * x) + z / (1 + z * y) ≥ 3 / 2 := by
      have h₁₆ : 0 < x * y := by positivity
      have h₁₇ : 0 < x * z := by positivity
      have h₁₈ : 0 < y * z := by positivity
      have h₁₉ : 0 < x * y * z := by positivity
      field_simp [h₁₂.ne', h₁₃.ne', h₁₄.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg hx.le hy.le, mul_nonneg hx.le hz.le, mul_nonneg hy.le hz.le,
        mul_nonneg (sq_nonneg (x - 1)) hz.le, mul_nonneg (sq_nonneg (y - 1)) hx.le,
        mul_nonneg (sq_nonneg (z - 1)) hy.le, mul_nonneg (sq_nonneg (x - 1)) (mul_nonneg hy.le hz.le),
        mul_nonneg (sq_nonneg (y - 1)) (mul_nonneg hx.le hz.le), mul_nonneg (sq_nonneg (z - 1)) (mul_nonneg hx.le hy.le)]
    linarith
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_112 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c + c * a = a * b * c → (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) + (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) + (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 := by
  intro a b c h
  have h₁ : 1 / a + 1 / b + 1 / c = 1 := by
    have h₂ : a > 0 := h.1
    have h₃ : b > 0 := h.2.1
    have h₄ : c > 0 := h.2.2.1
    have h₅ : a * b + b * c + c * a = a * b * c := h.2.2.2
    have h₆ : a * b * c > 0 := by positivity
    have h₇ : 1 / a + 1 / b + 1 / c = 1 := by
      field_simp [h₂.ne', h₃.ne', h₄.ne']
      nlinarith [h₅]
    exact h₇
  
  have h₂ : ∀ (x y : ℝ), x > 0 → y > 0 → (x ^ 4 + y ^ 4) / (x * y * (x ^ 3 + y ^ 3)) ≥ 1 / (2 * y) + 1 / (2 * x) := by
    intro x y hx hy
    have h₃ : 0 < x * y := mul_pos hx hy
    have h₄ : 0 < x ^ 3 + y ^ 3 := by positivity
    have h₅ : 0 < x * y * (x ^ 3 + y ^ 3) := by positivity
    have h₆ : x ^ 4 + y ^ 4 ≥ (x + y) * (x ^ 3 + y ^ 3) / 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2),
        sq_nonneg (x ^ 2 + y ^ 2), mul_nonneg hx.le hy.le, mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (x + y))]
    have h₇ : (x ^ 4 + y ^ 4) / (x * y * (x ^ 3 + y ^ 3)) ≥ 1 / (2 * y) + 1 / (2 * x) := by
      have h₈ : (x ^ 4 + y ^ 4) / (x * y * (x ^ 3 + y ^ 3)) ≥ (x + y) / (2 * (x * y)) := by
        -- Use the inequality x⁴ + y⁴ ≥ (x + y)(x³ + y³)/2 to bound the numerator
        calc
          (x ^ 4 + y ^ 4) / (x * y * (x ^ 3 + y ^ 3)) ≥ ((x + y) * (x ^ 3 + y ^ 3) / 2) / (x * y * (x ^ 3 + y ^ 3)) := by
            gcongr
            <;> nlinarith
          _ = (x + y) / (2 * (x * y)) := by
            field_simp [h₃.ne', h₄.ne']
            <;> ring
            <;> field_simp [h₃.ne', h₄.ne']
            <;> ring
      have h₉ : (x + y) / (2 * (x * y)) = 1 / (2 * y) + 1 / (2 * x) := by
        field_simp [hx.ne', hy.ne']
        <;> ring
        <;> field_simp [hx.ne', hy.ne']
        <;> ring
      linarith
    exact h₇
  
  have h₃ : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) ≥ 1 / (2 * b) + 1 / (2 * a) := by
    have h₃₁ : a > 0 := h.1
    have h₃₂ : b > 0 := h.2.1
    have h₃₃ : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) ≥ 1 / (2 * b) + 1 / (2 * a) := by
      exact h₂ a b h₃₁ h₃₂
    exact h₃₃
  
  have h₄ : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) ≥ 1 / (2 * c) + 1 / (2 * b) := by
    have h₄₁ : b > 0 := h.2.1
    have h₄₂ : c > 0 := h.2.2.1
    have h₄₃ : (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) ≥ 1 / (2 * c) + 1 / (2 * b) := by
      exact h₂ b c h₄₁ h₄₂
    exact h₄₃
  
  have h₅ : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 / (2 * a) + 1 / (2 * c) := by
    have h₅₁ : c > 0 := h.2.2.1
    have h₅₂ : a > 0 := h.1
    have h₅₃ : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 / (2 * a) + 1 / (2 * c) := by
      have h₅₄ : (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 / (2 * a) + 1 / (2 * c) := by
        exact h₂ c a h₅₁ h₅₂
      linarith
    exact h₅₃
  
  have h₆ : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) + (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) + (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 := by
    have h₆₁ : (a ^ 4 + b ^ 4) / (a * b * (a ^ 3 + b ^ 3)) + (b ^ 4 + c ^ 4) / (b * c * (b ^ 3 + c ^ 3)) + (c ^ 4 + a ^ 4) / (c * a * (c ^ 3 + a ^ 3)) ≥ 1 / (2 * b) + 1 / (2 * a) + (1 / (2 * c) + 1 / (2 * b)) + (1 / (2 * a) + 1 / (2 * c)) := by
      linarith [h₃, h₄, h₅]
    have h₆₂ : 1 / (2 * b) + 1 / (2 * a) + (1 / (2 * c) + 1 / (2 * b)) + (1 / (2 * a) + 1 / (2 * c)) = 1 / a + 1 / b + 1 / c := by
      ring_nf
      <;> field_simp [h.1.ne', h.2.1.ne', h.2.2.1.ne']
      <;> ring_nf
      <;> linarith
    have h₆₃ : 1 / (2 * b) + 1 / (2 * a) + (1 / (2 * c) + 1 / (2 * b)) + (1 / (2 * a) + 1 / (2 * c)) = 1 := by
      linarith [h₁, h₆₂]
    linarith [h₆₁, h₆₃]
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_114 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 8 → (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) ≤ 0 := by
  intro a b c h
  have h₁ : a + b + c ≥ 6 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < c := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < a * c := by positivity
    have h₇ : 0 < b * c := by positivity
    -- Use AM-GM inequality to prove that a + b + c ≥ 6
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]
  
  have h₂ : 0 < a + 1 := by
    have h₃ : a > 0 := by linarith
    linarith
  
  have h₃ : 0 < b + 1 := by
    have h₄ : b > 0 := by linarith
    linarith
  
  have h₄ : 0 < c + 1 := by
    have h₅ : c > 0 := by linarith
    linarith
  
  have h₅ : 0 < (a + 1) * (b + 1) * (c + 1) := by
    have h₅₁ : 0 < a + 1 := by linarith
    have h₅₂ : 0 < b + 1 := by linarith
    have h₅₃ : 0 < c + 1 := by linarith
    positivity
  
  have h₆ : (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) ≤ 0 := by
    have h₇ : 0 < (a + 1) * (b + 1) * (c + 1) := by positivity
    -- Combine the fractions and simplify the inequality
    have h₈ : (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) ≤ 0 := by
      -- Use the fact that a + b + c ≥ 6 to prove the inequality
      have h₉ : (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) = ((a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
        field_simp [h₂, h₃, h₄]
        <;> ring
        <;> field_simp [h₂, h₃, h₄]
        <;> ring
      rw [h₉]
      -- Prove that the numerator is less than or equal to 0
      have h₁₀ : ((a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1)) ≤ 0 := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos h.1 h.2.1, mul_pos h.1 h.2.2.1, mul_pos h.2.1 h.2.2.1]
      -- Since the denominator is positive, the fraction is less than or equal to 0
      have h₁₁ : 0 < (a + 1) * (b + 1) * (c + 1) := by positivity
      have h₁₂ : ((a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg h₁₀ (by positivity)
      linarith
    exact h₈
  
  exact h₆

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_8_6 : ∀ (a b : ℝ), a > 0 ∧ b > 0 → Real.sqrt (a ^ 2 / b) + Real.sqrt (b ^ 2 / a) ≥ Real.sqrt a + Real.sqrt b := by
  have h_main : ∀ (x y : ℝ), x > 0 → y > 0 → x^3 + y^3 ≥ x^2 * y + x * y^2 := by
    intro x y hx hy
    have h₁ : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
    have h₂ : 0 < x + y := by linarith
    have h₃ : 0 < x * y := by positivity
    nlinarith [sq_nonneg (x - y), mul_pos hx hy, mul_pos (sq_pos_of_pos hx) hy, mul_pos hx (sq_pos_of_pos hy)]
  
  have h_subst : ∀ (a b : ℝ), a > 0 → b > 0 → Real.sqrt (a ^ 2 / b) + Real.sqrt (b ^ 2 / a) ≥ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h₁ : Real.sqrt (a ^ 2 / b) = a / Real.sqrt b := by
      have h₁ : Real.sqrt (a ^ 2 / b) = Real.sqrt (a ^ 2) / Real.sqrt b := by
        rw [Real.sqrt_div (by positivity)]
        <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> field_simp [ha.ne', hb.ne']
        <;> nlinarith
      rw [h₁]
      have h₂ : Real.sqrt (a ^ 2) = a := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
      rw [h₂]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq, ha.ne', hb.ne']
      <;> ring_nf
      <;> field_simp [ha.ne', hb.ne']
      <;> nlinarith
    have h₂ : Real.sqrt (b ^ 2 / a) = b / Real.sqrt a := by
      have h₁ : Real.sqrt (b ^ 2 / a) = Real.sqrt (b ^ 2) / Real.sqrt a := by
        rw [Real.sqrt_div (by positivity)]
        <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> field_simp [ha.ne', hb.ne']
        <;> nlinarith
      rw [h₁]
      have h₂ : Real.sqrt (b ^ 2) = b := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
      rw [h₂]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq, ha.ne', hb.ne']
      <;> ring_nf
      <;> field_simp [ha.ne', hb.ne']
      <;> nlinarith
    rw [h₁, h₂]
    have h₃ : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have h₄ : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have h₅ : 0 < Real.sqrt a * Real.sqrt b := by positivity
    have h₆ : (Real.sqrt a) ^ 3 + (Real.sqrt b) ^ 3 ≥ (Real.sqrt a) ^ 2 * Real.sqrt b + Real.sqrt a * (Real.sqrt b) ^ 2 := by
      apply h_main (Real.sqrt a) (Real.sqrt b) h₃ h₄
    have h₇ : a / Real.sqrt b + b / Real.sqrt a ≥ Real.sqrt a + Real.sqrt b := by
      have h₈ : a / Real.sqrt b + b / Real.sqrt a = (a / Real.sqrt b + b / Real.sqrt a) := rfl
      have h₉ : (Real.sqrt a) ^ 3 + (Real.sqrt b) ^ 3 ≥ (Real.sqrt a) ^ 2 * Real.sqrt b + Real.sqrt a * (Real.sqrt b) ^ 2 := h₆
      have h₁₀ : a = (Real.sqrt a) ^ 2 := by
        nlinarith [Real.sq_sqrt (le_of_lt ha)]
      have h₁₁ : b = (Real.sqrt b) ^ 2 := by
        nlinarith [Real.sq_sqrt (le_of_lt hb)]
      have h₁₂ : a / Real.sqrt b + b / Real.sqrt a = (Real.sqrt a) ^ 2 / Real.sqrt b + (Real.sqrt b) ^ 2 / Real.sqrt a := by
        rw [h₁₀, h₁₁]
        <;> field_simp [h₃.ne', h₄.ne']
        <;> ring_nf
      rw [h₁₂]
      have h₁₃ : (Real.sqrt a) ^ 2 / Real.sqrt b + (Real.sqrt b) ^ 2 / Real.sqrt a ≥ Real.sqrt a + Real.sqrt b := by
        have h₁₄ : 0 < Real.sqrt a := h₃
        have h₁₅ : 0 < Real.sqrt b := h₄
        have h₁₆ : 0 < Real.sqrt a * Real.sqrt b := by positivity
        field_simp [h₁₄.ne', h₁₅.ne']
        rw [le_div_iff (by positivity)]
        nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
      linarith
    linarith
  
  have h_final : ∀ (a b : ℝ), a > 0 ∧ b > 0 → Real.sqrt (a ^ 2 / b) + Real.sqrt (b ^ 2 / a) ≥ Real.sqrt a + Real.sqrt b := by
    intro a b h
    have h₁ : a > 0 := h.1
    have h₂ : b > 0 := h.2
    exact h_subst a b h₁ h₂
  
  intro a b h
  exact h_final a b h

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_example_1_8_7 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥ 1 / 7 * (a + b + c) ^ 3 := by
  intro a b c h
  have h_main : a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥ 1 / 7 * (a + b + c) ^ 3 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_nonneg h.1 h.2.1, mul_nonneg h.1 h.2.2, mul_nonneg h.2.1 h.2.2,
      sq_nonneg (a + b - 2 * c), sq_nonneg (a + c - 2 * b), sq_nonneg (b + c - 2 * a),
      mul_nonneg (sq_nonneg (a - b)) h.2.2, mul_nonneg (sq_nonneg (a - c)) h.2.1,
      mul_nonneg (sq_nonneg (b - c)) h.1]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_115 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
  have h_main : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
    intro a b c h
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a * c := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
        sq_nonneg (a ^ 2 - a * b), sq_nonneg (a ^ 2 - a * c), sq_nonneg (b ^ 2 - a * b),
        sq_nonneg (b ^ 2 - b * c), sq_nonneg (c ^ 2 - a * c), sq_nonneg (c ^ 2 - b * c),
        sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
        mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₂ h₃, mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂),
        mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₃), mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃)]
    exact h₇
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_117 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a / ((a + b) * (a + c)) + b / ((b + c) * (b + a)) + c / ((c + a) * (c + b)) ≤ 9 / (4 * (a + b + c)) := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 < b * c := by positivity
  have h₆ : 0 < c * a := by positivity
  have h₇ : 0 < a + b + c := by positivity
  have h₈ : 0 < (a + b) * (a + c) * (b + c) := by positivity
  have h₉ : 9 * (a + b) * (a + c) * (b + c) - 8 * (a * b + b * c + c * a) * (a + b + c) ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  
  have h₁₀ : a / ((a + b) * (a + c)) + b / ((b + c) * (b + a)) + c / ((c + a) * (c + b)) = 2 * (a * b + b * c + c * a) / ((a + b) * (a + c) * (b + c)) := by
    have h₁₀₁ : a / ((a + b) * (a + c)) + b / ((b + c) * (b + a)) + c / ((c + a) * (c + b)) = (a * (b + c) + b * (a + c) + c * (a + b)) / ((a + b) * (a + c) * (b + c)) := by
      have h₁₀₂ : 0 < (a + b) * (a + c) := by positivity
      have h₁₀₃ : 0 < (b + c) * (b + a) := by positivity
      have h₁₀₄ : 0 < (c + a) * (c + b) := by positivity
      have h₁₀₅ : 0 < (a + b) * (a + c) * (b + c) := by positivity
      field_simp [h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne', h₁₀₅.ne']
      <;> ring
      <;> field_simp [h₁₀₂.ne', h₁₀₃.ne', h₁₀₄.ne', h₁₀₅.ne']
      <;> ring
      <;> linarith
    have h₁₀₆ : (a * (b + c) + b * (a + c) + c * (a + b)) = 2 * (a * b + b * c + c * a) := by ring
    rw [h₁₀₁]
    rw [h₁₀₆]
    <;> field_simp [h₈.ne']
    <;> ring
    <;> linarith
  
  have h₁₁ : 2 * (a * b + b * c + c * a) / ((a + b) * (a + c) * (b + c)) ≤ 9 / (4 * (a + b + c)) := by
    have h₁₁₁ : 0 < (a + b) * (a + c) * (b + c) := by positivity
    have h₁₁₂ : 0 < 4 * (a + b + c) := by positivity
    have h₁₁₃ : 0 < (a + b) * (a + c) * (b + c) * (4 * (a + b + c)) := by positivity
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [h₉]
  
  have h₁₂ : a / ((a + b) * (a + c)) + b / ((b + c) * (b + a)) + c / ((c + a) * (c + b)) ≤ 9 / (4 * (a + b + c)) := by
    linarith
  
  exact h₁₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem radmila_exercise_1_118 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
  intro a b c h
  have h₁ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) = a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
    have h₁₀ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) = a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2) := by
      ring_nf
      <;>
      (try
        norm_num) <;>
      (try
        linarith [h.1, h.2.1, h.2.2]) <;>
      (try
        nlinarith [h.1, h.2.1, h.2.2])
    rw [h₁₀]
    have h₁₁ : a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) = a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2) := by
      ring_nf
      <;>
      (try
        norm_num) <;>
      (try
        linarith [h.1, h.2.1, h.2.2]) <;>
      (try
        nlinarith [h.1, h.2.1, h.2.2])
    linarith
  
  have h₂ : a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) ≥ 0 := by
    cases' le_total a b with h₂ h₂ <;>
    cases' le_total b c with h₃ h₃ <;>
    cases' le_total c a with h₄ h₄ <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h.1.le h.2.1.le, mul_nonneg h.2.1.le h.2.2.le,
      mul_nonneg h.2.2.le h.1.le,
      mul_nonneg (sq_nonneg (a - b)) h.2.2.le,
      mul_nonneg (sq_nonneg (b - c)) h.1.le,
      mul_nonneg (sq_nonneg (c - a)) h.2.1.le]
  
  have h₃ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
    have h₃₁ : a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) ≥ 0 := by
      linarith
    linarith
  
  exact h₃
