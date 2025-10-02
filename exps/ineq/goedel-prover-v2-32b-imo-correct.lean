import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic


theorem imo_1960_p2 : ∀ (x : ℝ), x ≥ -1 / 2 ∧ x < 45 / 8 ∧ ¬ (x = 0) → 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 < 2 * x + 9 := by
  intro x hx
  have h_main : 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 = (1 + Real.sqrt (2 * x + 1)) ^ 2 := by
    have h₁ : x ≥ -1 / 2 := hx.1
    have h₂ : x ≠ 0 := hx.2.2
    have h₃ : 2 * x + 1 ≥ 0 := by linarith
    have h₄ : Real.sqrt (2 * x + 1) ≥ 0 := Real.sqrt_nonneg (2 * x + 1)
    have h₅ : (1 - Real.sqrt (2 * x + 1)) * (1 + Real.sqrt (2 * x + 1)) = -2 * x := by
      have h₅₁ : (1 - Real.sqrt (2 * x + 1)) * (1 + Real.sqrt (2 * x + 1)) = 1 - (Real.sqrt (2 * x + 1)) ^ 2 := by
        ring_nf
      rw [h₅₁]
      have h₅₂ : (Real.sqrt (2 * x + 1)) ^ 2 = 2 * x + 1 := by
        rw [Real.sq_sqrt] <;> linarith
      rw [h₅₂]
      <;> ring_nf <;> linarith
    have h₆ : (1 - Real.sqrt (2 * x + 1)) ^ 2 * (1 + Real.sqrt (2 * x + 1)) ^ 2 = 4 * x ^ 2 := by
      calc
        (1 - Real.sqrt (2 * x + 1)) ^ 2 * (1 + Real.sqrt (2 * x + 1)) ^ 2 =
            ((1 - Real.sqrt (2 * x + 1)) * (1 + Real.sqrt (2 * x + 1))) ^ 2 := by
          ring_nf
        _ = (-2 * x) ^ 2 := by rw [h₅]
        _ = 4 * x ^ 2 := by ring
    have h₇ : 1 + Real.sqrt (2 * x + 1) > 0 := by
      nlinarith [Real.sqrt_nonneg (2 * x + 1)]
    have h₈ : (1 - Real.sqrt (2 * x + 1)) ^ 2 = 4 * x ^ 2 / (1 + Real.sqrt (2 * x + 1)) ^ 2 := by
      have h₈₁ : (1 + Real.sqrt (2 * x + 1)) ≠ 0 := by linarith
      have h₈₂ : (1 + Real.sqrt (2 * x + 1)) ^ 2 ≠ 0 := by positivity
      field_simp [h₈₂] at h₆ ⊢
      nlinarith [sq_nonneg (1 - Real.sqrt (2 * x + 1)), sq_nonneg (1 + Real.sqrt (2 * x + 1))]
    have h₉ : 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 = (1 + Real.sqrt (2 * x + 1)) ^ 2 := by
      have h₉₁ : (1 - Real.sqrt (2 * x + 1)) ≠ 0 := by
        by_contra h
        have h₉₂ : 1 - Real.sqrt (2 * x + 1) = 0 := by linarith
        have h₉₃ : Real.sqrt (2 * x + 1) = 1 := by linarith
        have h₉₄ : 2 * x + 1 = 1 := by
          have h₉₄₁ : Real.sqrt (2 * x + 1) = 1 := by linarith
          have h₉₄₂ : 2 * x + 1 ≥ 0 := by linarith
          nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (by linarith : 0 ≤ (2 : ℝ) * x + 1)]
        have h₉₅ : x = 0 := by linarith
        contradiction
      have h₉₂ : (1 - Real.sqrt (2 * x + 1)) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact h₉₁
      have h₉₃ : 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 = (1 + Real.sqrt (2 * x + 1)) ^ 2 := by
        have h₉₄ : (1 - Real.sqrt (2 * x + 1)) ^ 2 = 4 * x ^ 2 / (1 + Real.sqrt (2 * x + 1)) ^ 2 := h₈
        have h₉₅ : 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 = 4 * x ^ 2 / (4 * x ^ 2 / (1 + Real.sqrt (2 * x + 1)) ^ 2) := by rw [h₉₄]
        rw [h₉₅]
        have h₉₆ : 4 * x ^ 2 ≠ 0 := by
          have h₉₆₁ : x ≠ 0 := h₂
          have h₉₆₂ : x ^ 2 > 0 := by
            exact sq_pos_of_ne_zero h₉₆₁
          positivity
        have h₉₇ : (1 + Real.sqrt (2 * x + 1)) ^ 2 ≠ 0 := by positivity
        field_simp [h₉₆, h₉₇]
        <;> ring_nf
        <;> field_simp [h₉₆, h₉₇]
        <;> nlinarith [Real.sqrt_nonneg (2 * x + 1)]
      exact h₉₃
    exact h₉
  
  have h_ineq : (1 + Real.sqrt (2 * x + 1)) ^ 2 < 2 * x + 9 := by
    have h₁ : x < 45 / 8 := hx.2.1
    have h₂ : x ≥ -1 / 2 := hx.1
    have h₃ : 2 * x + 1 ≥ 0 := by linarith
    have h₄ : Real.sqrt (2 * x + 1) ≥ 0 := Real.sqrt_nonneg _
    have h₅ : Real.sqrt (2 * x + 1) < 7 / 2 := by
      apply Real.sqrt_lt' (by positivity) |>.mpr
      nlinarith
    have h₆ : (1 + Real.sqrt (2 * x + 1)) ^ 2 = 2 + 2 * x + 2 * Real.sqrt (2 * x + 1) := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ (2 : ℝ) * x + 1)]
    rw [h₆]
    nlinarith [Real.sqrt_nonneg (2 * x + 1)]
  
  have h_final : 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 < 2 * x + 9 := by
    have h₁ : 4 * x ^ 2 / (1 - Real.sqrt (2 * x + 1)) ^ 2 = (1 + Real.sqrt (2 * x + 1)) ^ 2 := h_main
    rw [h₁]
    exact h_ineq
  
  exact h_final


theorem usamo_1997_p5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    have h₄₁ : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    have h₄₂ : 0 ≤ (a + b) := by linarith
    nlinarith [sq_nonneg (a - b), mul_pos h₁ h₂]
  
  have h₅ : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
    have h₅₁ : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
    have h₅₂ : 0 ≤ (b + c) := by linarith
    nlinarith [sq_nonneg (b - c), mul_pos h₂ h₃]
  
  have h₆ : a ^ 3 + c ^ 3 ≥ a * c * (a + c) := by
    have h₆₁ : 0 ≤ (a - c) ^ 2 := sq_nonneg (a - c)
    have h₆₂ : 0 ≤ (a + c) := by linarith
    nlinarith [sq_nonneg (a - c), mul_pos h₁ h₃]
  
  have h₇ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    have h₇₁ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b) + a * b * c := by
      linarith
    have h₇₂ : a * b * (a + b) + a * b * c = a * b * (a + b + c) := by
      ring
    linarith
  
  have h₈ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    have h₈₁ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (b + c) + a * b * c := by
      linarith
    have h₈₂ : b * c * (b + c) + a * b * c = b * c * (a + b + c) := by
      ring
    linarith
  
  have h₉ : a ^ 3 + c ^ 3 + a * b * c ≥ a * c * (a + b + c) := by
    have h₉₁ : a ^ 3 + c ^ 3 + a * b * c ≥ a * c * (a + c) + a * b * c := by
      linarith
    have h₉₂ : a * c * (a + c) + a * b * c = a * c * (a + b + c) := by
      ring
    linarith
  
  have h₁₀ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₁₀₁ : 0 < a * b * (a + b + c) := by positivity
    have h₁₀₂ : 0 < a ^ 3 + b ^ 3 + a * b * c := by positivity
    have h₁₀₃ : 0 < a * b * (a + b + c) := by positivity
    have h₁₀₄ : 0 < a ^ 3 + b ^ 3 + a * b * c := by positivity
    -- Use the fact that if x ≤ y and both are positive, then 1/y ≤ 1/x
    have h₁₀₅ : a * b * (a + b + c) ≤ a ^ 3 + b ^ 3 + a * b * c := by linarith
    -- Apply the reciprocal inequality
    have h₁₀₆ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₀₆
  
  have h₁₁ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₁₁₁ : 0 < b * c * (a + b + c) := by positivity
    have h₁₁₂ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₁₁₃ : 0 < b * c * (a + b + c) := by positivity
    have h₁₁₄ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    -- Use the fact that if x ≤ y and both are positive, then 1/y ≤ 1/x
    have h₁₁₅ : b * c * (a + b + c) ≤ b ^ 3 + c ^ 3 + a * b * c := by linarith
    -- Apply the reciprocal inequality
    have h₁₁₆ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₁₆
  
  have h₁₂ : 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
    have h₁₂₁ : 0 < a * c * (a + b + c) := by positivity
    have h₁₂₂ : 0 < a ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₁₂₃ : 0 < a * c * (a + b + c) := by positivity
    have h₁₂₄ : 0 < a ^ 3 + c ^ 3 + a * b * c := by positivity
    -- Use the fact that if x ≤ y and both are positive, then 1/y ≤ 1/x
    have h₁₂₅ : a * c * (a + b + c) ≤ a ^ 3 + c ^ 3 + a * b * c := by linarith
    -- Apply the reciprocal inequality
    have h₁₂₆ : 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₂₆
  
  have h₁₃ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = 1 / (a * b * c) := by
    have h₁₃₁ : 0 < a * b * c := by positivity
    have h₁₃₂ : 0 < a + b + c := by positivity
    have h₁₃₃ : 0 < a * b * (a + b + c) := by positivity
    have h₁₃₄ : 0 < b * c * (a + b + c) := by positivity
    have h₁₃₅ : 0 < a * c * (a + b + c) := by positivity
    have h₁₃₆ : 0 < a * b * c * (a + b + c) := by positivity
    -- Simplify each term by finding a common denominator
    have h₁₃₇ : 1 / (a * b * (a + b + c)) = c / (a * b * c * (a + b + c)) := by
      have h₁₃₇₁ : 1 / (a * b * (a + b + c)) = c / (a * b * c * (a + b + c)) := by
        field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₃.ne']
        <;> ring_nf
        <;> field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₃.ne']
        <;> ring_nf
      rw [h₁₃₇₁]
    have h₁₃₈ : 1 / (b * c * (a + b + c)) = a / (a * b * c * (a + b + c)) := by
      have h₁₃₈₁ : 1 / (b * c * (a + b + c)) = a / (a * b * c * (a + b + c)) := by
        field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₄.ne']
        <;> ring_nf
        <;> field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₄.ne']
        <;> ring_nf
      rw [h₁₃₈₁]
    have h₁₃₉ : 1 / (a * c * (a + b + c)) = b / (a * b * c * (a + b + c)) := by
      have h₁₃₉₁ : 1 / (a * c * (a + b + c)) = b / (a * b * c * (a + b + c)) := by
        field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₅.ne']
        <;> ring_nf
        <;> field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₅.ne']
        <;> ring_nf
      rw [h₁₃₉₁]
    rw [h₁₃₇, h₁₃₈, h₁₃₉]
    -- Combine the terms
    have h₁₃₁₀ : c / (a * b * c * (a + b + c)) + a / (a * b * c * (a + b + c)) + b / (a * b * c * (a + b + c)) = (c + a + b) / (a * b * c * (a + b + c)) := by
      have h₁₃₁₀₁ : c / (a * b * c * (a + b + c)) + a / (a * b * c * (a + b + c)) + b / (a * b * c * (a + b + c)) = (c + a + b) / (a * b * c * (a + b + c)) := by
        field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₆.ne']
        <;> ring_nf
        <;> field_simp [h₁₃₁.ne', h₁₃₂.ne', h₁₃₆.ne']
        <;> ring_nf
      rw [h₁₃₁₀₁]
    rw [h₁₃₁₀]
    -- Simplify the numerator and denominator
    have h₁₃₁₁ : (c + a + b) / (a * b * c * (a + b + c)) = 1 / (a * b * c) := by
      have h₁₃₁₁₁ : (c + a + b) / (a * b * c * (a + b + c)) = 1 / (a * b * c) := by
        have h₁₃₁₁₂ : a + b + c ≠ 0 := by linarith
        have h₁₃₁₁₃ : a * b * c ≠ 0 := by positivity
        field_simp [h₁₃₁₁₂, h₁₃₁₁₃]
        <;> ring_nf
        <;> field_simp [h₁₃₁₁₂, h₁₃₁₁₃]
        <;> ring_nf
        <;> nlinarith
      rw [h₁₃₁₁₁]
    rw [h₁₃₁₁]
  
  have h₁₄ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    have h₁₄₁ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (a ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) := by
      linarith
    have h₁₄₂ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (a * c * (a + b + c)) = 1 / (a * b * c) := by
      exact h₁₃
    linarith
  
  exact h₁₄


theorem usamo_2001_p3_left : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4 → 0 ≤ a * b + b * c + c * a - a * b * c := by
  intro a b c h
  have h₁ : a ≥ 0 := by linarith
  have h₂ : b ≥ 0 := by linarith
  have h₃ : c ≥ 0 := by linarith
  have h₄ : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4 := by linarith
  have h₅ : a ≤ 1 ∨ b ≤ 1 ∨ c ≤ 1 := by
    by_contra! h₅
    have h₅₁ : a > 1 := by linarith
    have h₅₂ : b > 1 := by linarith
    have h₅₃ : c > 1 := by linarith
    have h₅₄ : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c > 4 := by
      have h₅₄₁ : a ^ 2 > 1 := by nlinarith
      have h₅₄₂ : b ^ 2 > 1 := by nlinarith
      have h₅₄₃ : c ^ 2 > 1 := by nlinarith
      have h₅₄₄ : a * b > 1 := by nlinarith
      have h₅₄₅ : a * b * c > 1 := by nlinarith
      nlinarith
    linarith
  
  have h₆ : 0 ≤ a * b + b * c + c * a - a * b * c := by
    -- Consider the three cases from h₅
    rcases h₅ with (h₅ | h₅ | h₅)
    · -- Case 1: a ≤ 1
      have h₆₁ : a * b * c ≤ b * c := by
        -- Since a ≤ 1 and b, c ≥ 0, we have a * b * c ≤ b * c
        have h₆₁₁ : 0 ≤ b * c := by positivity
        nlinarith
      -- Therefore, a * b + b * c + c * a - a * b * c ≥ a * b + c * a ≥ 0
      nlinarith [mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁]
    · -- Case 2: b ≤ 1
      have h₆₁ : a * b * c ≤ a * c := by
        -- Since b ≤ 1 and a, c ≥ 0, we have a * b * c ≤ a * c
        have h₆₁₁ : 0 ≤ a * c := by positivity
        nlinarith
      -- Therefore, a * b + b * c + c * a - a * b * c ≥ b * c + a * b ≥ 0
      nlinarith [mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁]
    · -- Case 3: c ≤ 1
      have h₆₁ : a * b * c ≤ a * b := by
        -- Since c ≤ 1 and a, b ≥ 0, we have a * b * c ≤ a * b
        have h₆₁₁ : 0 ≤ a * b := by positivity
        nlinarith
      -- Therefore, a * b + b * c + c * a - a * b * c ≥ c * a + b * c ≥ 0
      nlinarith [mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁]
  
  exact h₆


theorem idmo_2008_p2 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / (x + y + 2) := by
  intro x y hxy
  have h₁ : (1 + Real.sqrt x) ^ 2 ≤ 2 * (1 + x) := by
    have h₁₁ : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h₁₂ : 0 ≤ (Real.sqrt x - 1) ^ 2 := by positivity
    nlinarith [Real.sq_sqrt (le_of_lt hxy.1), sq_nonneg (Real.sqrt x - 1)]

  have h₂ : 1 / (1 + Real.sqrt x) ^ 2 ≥ 1 / (2 * (1 + x)) := by
    have h₂₁ : 0 < (1 + Real.sqrt x) ^ 2 := by
      have h₂₁₁ : 0 < 1 + Real.sqrt x := by
        have h₂₁₂ : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
        linarith
      positivity
    have h₂₂ : 0 < 2 * (1 + x) := by
      have h₂₂₁ : 0 < x := hxy.1
      linarith
    have h₂₃ : (1 + Real.sqrt x) ^ 2 ≤ 2 * (1 + x) := h₁
    have h₂₄ : 1 / (1 + Real.sqrt x) ^ 2 ≥ 1 / (2 * (1 + x)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₂₄

  have h₃ : (1 + Real.sqrt y) ^ 2 ≤ 2 * (1 + y) := by
    have h₃₁ : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have h₃₂ : 0 ≤ (Real.sqrt y - 1) ^ 2 := by positivity
    nlinarith [Real.sq_sqrt (le_of_lt hxy.2), sq_nonneg (Real.sqrt y - 1)]

  have h₄ : 1 / (1 + Real.sqrt y) ^ 2 ≥ 1 / (2 * (1 + y)) := by
    have h₄₁ : 0 < (1 + Real.sqrt y) ^ 2 := by
      have h₄₁₁ : 0 < 1 + Real.sqrt y := by
        have h₄₁₂ : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
        linarith
      positivity
    have h₄₂ : 0 < 2 * (1 + y) := by
      have h₄₂₁ : 0 < y := hxy.2
      linarith
    have h₄₃ : (1 + Real.sqrt y) ^ 2 ≤ 2 * (1 + y) := h₃
    have h₄₄ : 1 / (1 + Real.sqrt y) ^ 2 ≥ 1 / (2 * (1 + y)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₄₄

  have h₅ : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 1 / (2 * (1 + x)) + 1 / (2 * (1 + y)) := by
    linarith

  have h₆ : (2 + x + y) ^ 2 ≥ 4 * (1 + x) * (1 + y) := by
    nlinarith [sq_nonneg (x - y)]

  have h₇ : (2 + x + y) / (2 * (1 + x) * (1 + y)) ≥ 2 / (x + y + 2) := by
    have h₇₁ : 0 < x := hxy.1
    have h₇₂ : 0 < y := hxy.2
    have h₇₃ : 0 < 1 + x := by linarith
    have h₇₄ : 0 < 1 + y := by linarith
    have h₇₅ : 0 < 2 * (1 + x) * (1 + y) := by positivity
    have h₇₆ : 0 < x + y + 2 := by linarith
    have h₇₇ : 0 < (2 * (1 + x) * (1 + y)) * (x + y + 2) := by positivity
    have h₇₈ : (2 + x + y) ^ 2 ≥ 4 * (1 + x) * (1 + y) := h₆
    have h₇₉ : (2 + x + y) / (2 * (1 + x) * (1 + y)) ≥ 2 / (x + y + 2) := by
      rw [ge_iff_le]
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg (x - y)]
    exact h₇₉

  have h₈ : 1 / (2 * (1 + x)) + 1 / (2 * (1 + y)) = (2 + x + y) / (2 * (1 + x) * (1 + y)) := by
    have h₈₁ : 0 < x := hxy.1
    have h₈₂ : 0 < y := hxy.2
    have h₈₃ : 0 < 1 + x := by linarith
    have h₈₄ : 0 < 1 + y := by linarith
    have h₈₅ : 0 < 2 * (1 + x) := by positivity
    have h₈₆ : 0 < 2 * (1 + y) := by positivity
    have h₈₇ : 0 < 2 * (1 + x) * (1 + y) := by positivity
    field_simp [h₈₅.ne', h₈₆.ne', h₈₇.ne']
    <;> ring_nf
    <;> field_simp [h₈₃.ne', h₈₄.ne']
    <;> ring_nf
    <;> nlinarith

  have h₉ : 1 / (2 * (1 + x)) + 1 / (2 * (1 + y)) ≥ 2 / (x + y + 2) := by
    have h₉₁ : 1 / (2 * (1 + x)) + 1 / (2 * (1 + y)) = (2 + x + y) / (2 * (1 + x) * (1 + y)) := h₈
    rw [h₉₁]
    have h₉₂ : (2 + x + y) / (2 * (1 + x) * (1 + y)) ≥ 2 / (x + y + 2) := h₇
    linarith

  have h₁₀ : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 ≥ 2 / (x + y + 2) := by
    linarith

  exact h₁₀


theorem imosl_2008_p2 : ∀ (x y z : ℝ), ¬ (x = 1) ∧ ¬ (y = 1) ∧ ¬ (z = 1) ∧ x * y * z = 1 → x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 ≥ 1 := by
  intro x y z h
  have hx : x ≠ 1 := by
    have h₁ : ¬(x = 1) := h.1
    exact h₁
  
  have hy : y ≠ 1 := by
    have h₁ : ¬(y = 1) := h.2.1
    exact h₁
  
  have hz : z ≠ 1 := by
    have h₁ : ¬(z = 1) := h.2.2.1
    exact h₁
  
  have hxyz : x * y * z = 1 := by
    have h₁ : x * y * z = 1 := h.2.2.2
    exact h₁
  
  have h₁ : x - 1 ≠ 0 := by
    intro h₂
    apply hx
    linarith
  
  have h₂ : y - 1 ≠ 0 := by
    intro h₃
    apply hy
    linarith
  
  have h₃ : z - 1 ≠ 0 := by
    intro h₄
    apply hz
    linarith
  
  set a := x / (x - 1) with ha
  set b := y / (y - 1) with hb
  set c := z / (z - 1) with hc
  
  have h₄ : a - 1 = 1 / (x - 1) := by
    have h₅ : a - 1 = x / (x - 1) - 1 := by rw [ha]
    rw [h₅]
    have h₆ : x / (x - 1) - 1 = 1 / (x - 1) := by
      have h₇ : x / (x - 1) - 1 = (x - (x - 1)) / (x - 1) := by
        field_simp [h₁]
        <;> ring
        <;> field_simp [h₁]
        <;> ring
      rw [h₇]
      have h₈ : (x - (x - 1)) / (x - 1) = 1 / (x - 1) := by
        have h₉ : x - (x - 1) = 1 := by ring
        rw [h₉]
        <;> field_simp [h₁]
        <;> ring
      rw [h₈]
    rw [h₆]
    <;> field_simp [h₁]
    <;> ring
  
  have h₅ : b - 1 = 1 / (y - 1) := by
    have h₅ : b - 1 = y / (y - 1) - 1 := by rw [hb]
    rw [h₅]
    have h₆ : y / (y - 1) - 1 = 1 / (y - 1) := by
      have h₇ : y / (y - 1) - 1 = (y - (y - 1)) / (y - 1) := by
        field_simp [h₂]
        <;> ring
        <;> field_simp [h₂]
        <;> ring
      rw [h₇]
      have h₈ : (y - (y - 1)) / (y - 1) = 1 / (y - 1) := by
        have h₉ : y - (y - 1) = 1 := by ring
        rw [h₉]
        <;> field_simp [h₂]
        <;> ring
      rw [h₈]
    rw [h₆]
    <;> field_simp [h₂]
    <;> ring
  
  have h₆ : c - 1 = 1 / (z - 1) := by
    have h₅ : c - 1 = z / (z - 1) - 1 := by rw [hc]
    rw [h₅]
    have h₆ : z / (z - 1) - 1 = 1 / (z - 1) := by
      have h₇ : z / (z - 1) - 1 = (z - (z - 1)) / (z - 1) := by
        field_simp [h₃]
        <;> ring
        <;> field_simp [h₃]
        <;> ring
      rw [h₇]
      have h₈ : (z - (z - 1)) / (z - 1) = 1 / (z - 1) := by
        have h₉ : z - (z - 1) = 1 := by ring
        rw [h₉]
        <;> field_simp [h₃]
        <;> ring
      rw [h₈]
    rw [h₆]
    <;> field_simp [h₃]
    <;> ring
  
  have h₇ : (a - 1) * (b - 1) * (c - 1) = a * b * c := by
    calc
      (a - 1) * (b - 1) * (c - 1) = (1 / (x - 1)) * (1 / (y - 1)) * (1 / (z - 1)) := by
        rw [h₄, h₅, h₆]
        <;> ring
      _ = 1 / ((x - 1) * (y - 1) * (z - 1)) := by
        field_simp [h₁, h₂, h₃]
        <;> ring
      _ = a * b * c := by
        have h₇ : a * b * c = (x / (x - 1)) * (y / (y - 1)) * (z / (z - 1)) := by
          simp [ha, hb, hc]
          <;> ring
        rw [h₇]
        have h₈ : (x / (x - 1)) * (y / (y - 1)) * (z / (z - 1)) = (x * y * z) / ((x - 1) * (y - 1) * (z - 1)) := by
          field_simp [h₁, h₂, h₃]
          <;> ring
        rw [h₈]
        have h₉ : x * y * z = 1 := hxyz
        rw [h₉]
        <;> field_simp [h₁, h₂, h₃]
        <;> ring
        <;> simp_all
        <;> field_simp [h₁, h₂, h₃]
        <;> ring
  
  have h₈ : a * b + b * c + c * a = a + b + c - 1 := by
    have h₈₁ : (a - 1) * (b - 1) * (c - 1) = a * b * c := h₇
    have h₈₂ : (a - 1) * (b - 1) * (c - 1) = a * b * c - (a * b + b * c + c * a) + (a + b + c) - 1 := by
      ring_nf
      <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try ring_nf at h₈₁ ⊢) <;>
      (try nlinarith)
    have h₈₃ : a * b * c - (a * b + b * c + c * a) + (a + b + c) - 1 = a * b * c := by
      linarith
    have h₈₄ : a * b + b * c + c * a = a + b + c - 1 := by
      linarith
    exact h₈₄
  
  have h₉ : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c - 1) ^ 2 + 1 := by
    have h₉₁ : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by
      ring
    have h₉₂ : (a + b + c - 1) ^ 2 + 1 = (a + b + c) ^ 2 - 2 * (a + b + c) + 2 := by
      ring
    have h₉₃ : a * b + b * c + c * a = a + b + c - 1 := h₈
    calc
      a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by rw [h₉₁]
      _ = (a + b + c) ^ 2 - 2 * (a + b + c - 1) := by rw [h₉₃]
      _ = (a + b + c) ^ 2 - 2 * (a + b + c) + 2 := by ring
      _ = (a + b + c - 1) ^ 2 + 1 := by
        nlinarith [sq_nonneg (a + b + c - 1)]
  
  have h₁₀ : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 := by
    have h₁₀₁ : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c - 1) ^ 2 + 1 := h₉
    have h₁₀₂ : (a + b + c - 1) ^ 2 ≥ 0 := by nlinarith
    nlinarith
  
  have h₁₁ : a ^ 2 = x ^ 2 / (x - 1) ^ 2 := by
    have h₁₁₁ : a = x / (x - 1) := by rw [ha]
    rw [h₁₁₁]
    have h₁₁₂ : (x / (x - 1)) ^ 2 = x ^ 2 / (x - 1) ^ 2 := by
      field_simp [h₁]
      <;> ring_nf
      <;> field_simp [h₁]
      <;> ring_nf
    rw [h₁₁₂]
  
  have h₁₂ : b ^ 2 = y ^ 2 / (y - 1) ^ 2 := by
    have h₁₂₁ : b = y / (y - 1) := by rw [hb]
    rw [h₁₂₁]
    have h₁₂₂ : (y / (y - 1)) ^ 2 = y ^ 2 / (y - 1) ^ 2 := by
      field_simp [h₂]
      <;> ring_nf
      <;> field_simp [h₂]
      <;> ring_nf
    rw [h₁₂₂]
  
  have h₁₃ : c ^ 2 = z ^ 2 / (z - 1) ^ 2 := by
    have h₁₃₁ : c = z / (z - 1) := by rw [hc]
    rw [h₁₃₁]
    have h₁₃₂ : (z / (z - 1)) ^ 2 = z ^ 2 / (z - 1) ^ 2 := by
      field_simp [h₃]
      <;> ring_nf
      <;> field_simp [h₃]
      <;> ring_nf
    rw [h₁₃₂]
  
  have h₁₄ : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 ≥ 1 := by
    have h₁₄₁ : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
      calc
        x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = a ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
          rw [h₁₁]
        _ = a ^ 2 + b ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
          rw [h₁₂]
        _ = a ^ 2 + b ^ 2 + c ^ 2 := by
          rw [h₁₃]
    rw [h₁₄₁]
    exact h₁₀
  
  exact h₁₄


theorem imosl_2010_p2_right : ∀ (a b c d : ℝ), a + b + c + d = 6 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12 → 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48 := by
  intro a b c d h
  have h_main : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    have h₁ : 4 * a ^ 3 - a ^ 4 ≤ 4 * a ^ 2 := by
      have h₁₀ : 0 ≤ a ^ 2 * (a - 2) ^ 2 := by
        nlinarith [sq_nonneg (a - 2), sq_nonneg a]
      nlinarith [sq_nonneg (a - 2), sq_nonneg a]
    have h₂ : 4 * b ^ 3 - b ^ 4 ≤ 4 * b ^ 2 := by
      have h₂₀ : 0 ≤ b ^ 2 * (b - 2) ^ 2 := by
        nlinarith [sq_nonneg (b - 2), sq_nonneg b]
      nlinarith [sq_nonneg (b - 2), sq_nonneg b]
    have h₃ : 4 * c ^ 3 - c ^ 4 ≤ 4 * c ^ 2 := by
      have h₃₀ : 0 ≤ c ^ 2 * (c - 2) ^ 2 := by
        nlinarith [sq_nonneg (c - 2), sq_nonneg c]
      nlinarith [sq_nonneg (c - 2), sq_nonneg c]
    have h₄ : 4 * d ^ 3 - d ^ 4 ≤ 4 * d ^ 2 := by
      have h₄₀ : 0 ≤ d ^ 2 * (d - 2) ^ 2 := by
        nlinarith [sq_nonneg (d - 2), sq_nonneg d]
      nlinarith [sq_nonneg (d - 2), sq_nonneg d]
    -- Summing up the inequalities for a, b, c, d
    linarith
  
  have h_final : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48 := by
    have h₁ : 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 48 := by
      have h₂ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12 := h.2
      linarith
    linarith
  
  exact h_final


theorem imosl_2016_p1 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b ≥ 1 ∧ b * c ≥ 1 ∧ c * a ≥ 1 → ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ (1 / 3) ≤ ((a + b + c) / 3) ^ 2 + 1 := by
  intro a b c h
  have h₁ : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) : ℝ) ^ (1 / 3 : ℕ) = 1 := by
    norm_num [pow_one]
    <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try linarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]) <;>
    (try field_simp) <;>
    (try ring_nf) <;>
    (try norm_num)
    <;>
    simp_all [pow_one]
    <;>
    norm_num
    <;>
    linarith
  
  have h₂ : ((a + b + c) / 3 : ℝ) ^ 2 + 1 ≥ 1 := by
    have h₃ : ((a + b + c) / 3 : ℝ) ^ 2 ≥ 0 := by
      -- The square of any real number is non-negative.
      apply pow_two_nonneg
    -- Adding 1 to both sides of the inequality preserves the inequality.
    linarith
  
  have h₃ : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ (1 / 3) ≤ ((a + b + c) / 3) ^ 2 + 1 := by
    have h₄ : ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) : ℝ) ^ (1 / 3 : ℕ) = 1 := h₁
    have h₅ : ((a + b + c) / 3 : ℝ) ^ 2 + 1 ≥ 1 := h₂
    norm_num [h₄] at h₅ ⊢
    <;>
    (try ring_nf at h₅ ⊢) <;>
    (try norm_num at h₅ ⊢) <;>
    (try linarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]) <;>
    (try nlinarith)
    <;>
    (try
      {
        simp_all [pow_one]
        <;>
        norm_num
        <;>
        linarith
      })
  
  exact h₃


theorem imosl_2018_p7 : ∀ (a b c d : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ a + b + c + d = 100 → (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) ≤ 8 / 7 ^ (1 / 3) := by
  intro a b c d h
  have h₁ : (a / (b + 7)) ^ (1 / 3) = 1 := by
    norm_num [pow_one]
    <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try field_simp) <;>
    (try ring_nf) <;>
    (try nlinarith)
  
  have h₂ : (b / (c + 7)) ^ (1 / 3) = 1 := by
    norm_num [pow_one]
    <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try field_simp) <;>
    (try ring_nf) <;>
    (try nlinarith)
  
  have h₃ : (c / (d + 7)) ^ (1 / 3) = 1 := by
    norm_num [pow_one]
    <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try field_simp) <;>
    (try ring_nf) <;>
    (try nlinarith)
  
  have h₄ : (d / (a + 7)) ^ (1 / 3) = 1 := by
    norm_num [pow_one]
    <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try field_simp) <;>
    (try ring_nf) <;>
    (try nlinarith)
  
  have h₅ : (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) = 4 := by
    rw [h₁, h₂, h₃, h₄]
    <;> norm_num
  
  have h₆ : (8 : ℝ) / (7 : ℝ) ^ (1 / 3) = 8 := by
    norm_num
    <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try field_simp) <;>
    (try ring_nf) <;>
    (try nlinarith)
  
  have h₇ : (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) ≤ 8 / 7 ^ (1 / 3) := by
    have h₈ : (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) = 4 := h₅
    have h₉ : (8 : ℝ) / (7 : ℝ) ^ (1 / 3) = 8 := h₆
    have h₁₀ : (4 : ℝ) ≤ 8 := by norm_num
    have h₁₁ : (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) ≤ 8 / 7 ^ (1 / 3) := by
      calc
        (a / (b + 7)) ^ (1 / 3) + (b / (c + 7)) ^ (1 / 3) + (c / (d + 7)) ^ (1 / 3) + (d / (a + 7)) ^ (1 / 3) = 4 := by rw [h₈]
        _ ≤ 8 := by norm_num
        _ = 8 / 7 ^ (1 / 3) := by
          norm_num [h₆]
          <;>
          (try simp_all) <;>
          (try norm_num) <;>
          (try linarith) <;>
          (try field_simp) <;>
          (try ring_nf) <;>
          (try nlinarith)
    exact h₁₁
  
  exact h₇


theorem imo_1962_p2 : ∀ (x : ℝ), x ≥ -1 ∧ x < 1 - Real.sqrt 127 / 32 → Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
  have h_main : ∀ (x : ℝ), x ≥ -1 ∧ x < 1 - Real.sqrt 127 / 32 → Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 4 := by
    intro x hx
    have h₀ : x ≥ -1 := hx.1
    have h₁ : x < 1 - Real.sqrt 127 / 32 := hx.2
    have h₂ : 3 - x ≥ 0 := by
      have h₃ : x < 1 - Real.sqrt 127 / 32 := h₁
      have h₄ : Real.sqrt 127 ≥ 0 := Real.sqrt_nonneg 127
      nlinarith [Real.sqrt_nonneg 127, Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
    have h₃ : x + 1 ≥ 0 := by linarith
    have h₄ : Real.sqrt (3 - x) ≥ 0 := Real.sqrt_nonneg (3 - x)
    have h₅ : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
    have h₆ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≥ 0 := by
      have h₇ : 3 - x ≥ x + 1 := by
        nlinarith [Real.sqrt_nonneg 127, Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
      have h₈ : Real.sqrt (3 - x) ≥ Real.sqrt (x + 1) := by
        apply Real.sqrt_le_sqrt
        linarith
      linarith
    by_contra! h
    have h₇ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≤ 1 / 4 := by linarith
    have h₈ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 ≤ (1 / 4) ^ 2 := by
      have h₉ : 0 ≤ Real.sqrt (3 - x) - Real.sqrt (x + 1) := by linarith
      have h₁₀ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≤ 1 / 4 := h₇
      nlinarith
    have h₉ : (3 - x) + (x + 1) - 2 * Real.sqrt ((3 - x) * (x + 1)) ≤ 1 / 16 := by
      have h₁₀ : (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 = (3 - x) + (x + 1) - 2 * Real.sqrt ((3 - x) * (x + 1)) := by
        have h₁₁ : 0 ≤ Real.sqrt (3 - x) := Real.sqrt_nonneg (3 - x)
        have h₁₂ : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
        have h₁₃ : 0 ≤ Real.sqrt (3 - x) * Real.sqrt (x + 1) := by positivity
        have h₁₄ : 0 ≤ (3 - x) := by linarith
        have h₁₅ : 0 ≤ (x + 1) := by linarith
        have h₁₆ : 0 ≤ (3 - x) * (x + 1) := by positivity
        have h₁₇ : Real.sqrt ((3 - x) * (x + 1)) = Real.sqrt (3 - x) * Real.sqrt (x + 1) := by
          rw [Real.sqrt_mul] <;> linarith
        calc
          (Real.sqrt (3 - x) - Real.sqrt (x + 1)) ^ 2 = (Real.sqrt (3 - x)) ^ 2 + (Real.sqrt (x + 1)) ^ 2 - 2 * (Real.sqrt (3 - x) * Real.sqrt (x + 1)) := by
            ring_nf
            <;>
            linarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1)]
          _ = (3 - x) + (x + 1) - 2 * (Real.sqrt (3 - x) * Real.sqrt (x + 1)) := by
            have h₁₈ : (Real.sqrt (3 - x)) ^ 2 = 3 - x := by
              rw [Real.sq_sqrt] <;> linarith
            have h₁₉ : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by
              rw [Real.sq_sqrt] <;> linarith
            rw [h₁₈, h₁₉]
            <;>
            ring_nf
          _ = (3 - x) + (x + 1) - 2 * Real.sqrt ((3 - x) * (x + 1)) := by
            have h₂₀ : Real.sqrt ((3 - x) * (x + 1)) = Real.sqrt (3 - x) * Real.sqrt (x + 1) := by
              rw [Real.sqrt_mul] <;> linarith
            rw [h₂₀]
            <;>
            ring_nf
      rw [h₁₀] at h₈
      linarith
    have h₁₀ : Real.sqrt ((3 - x) * (x + 1)) ≥ 63 / 32 := by
      have h₁₁ : (3 - x) + (x + 1) - 2 * Real.sqrt ((3 - x) * (x + 1)) ≤ 1 / 16 := h₉
      have h₁₂ : (3 - x) + (x + 1) = 4 := by ring
      rw [h₁₂] at h₁₁
      have h₁₃ : 4 - 2 * Real.sqrt ((3 - x) * (x + 1)) ≤ 1 / 16 := by linarith
      have h₁₄ : 2 * Real.sqrt ((3 - x) * (x + 1)) ≥ 63 / 16 := by linarith
      have h₁₅ : Real.sqrt ((3 - x) * (x + 1)) ≥ 63 / 32 := by linarith
      exact h₁₅
    have h₁₁ : (3 - x) * (x + 1) ≥ (63 / 32 : ℝ) ^ 2 := by
      have h₁₂ : Real.sqrt ((3 - x) * (x + 1)) ≥ 63 / 32 := h₁₀
      have h₁₃ : 0 ≤ (3 - x) * (x + 1) := by
        have h₁₄ : 0 ≤ 3 - x := by linarith
        have h₁₅ : 0 ≤ x + 1 := by linarith
        positivity
      have h₁₄ : Real.sqrt ((3 - x) * (x + 1)) ^ 2 ≥ (63 / 32 : ℝ) ^ 2 := by
        exact pow_le_pow_of_le_left (by positivity) h₁₂ 2
      have h₁₅ : Real.sqrt ((3 - x) * (x + 1)) ^ 2 = (3 - x) * (x + 1) := by
        rw [Real.sq_sqrt] <;> linarith
      rw [h₁₅] at h₁₄
      linarith
    have h₁₂ : x ^ 2 - 2 * x + 897 / 1024 ≤ 0 := by
      have h₁₃ : (3 - x) * (x + 1) ≥ (63 / 32 : ℝ) ^ 2 := h₁₁
      have h₁₄ : x ^ 2 - 2 * x + 897 / 1024 ≤ 0 := by
        norm_num at h₁₃ ⊢
        nlinarith [sq_nonneg (x - 1)]
      exact h₁₄
    have h₁₃ : x ≥ 1 - Real.sqrt 127 / 32 := by
      nlinarith [Real.sqrt_nonneg 127, Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
    have h₁₄ : x < 1 - Real.sqrt 127 / 32 := h₁
    linarith
  
  have h_final : ∀ (x : ℝ), x ≥ -1 ∧ x < 1 - Real.sqrt 127 / 32 → Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
    intro x hx
    have h₁ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 4 := h_main x hx
    have h₂ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≥ 0 := by
      have h₃ : x ≥ -1 := hx.1
      have h₄ : x < 1 - Real.sqrt 127 / 32 := hx.2
      have h₅ : 3 - x ≥ 0 := by
        have h₆ : x < 1 - Real.sqrt 127 / 32 := hx.2
        have h₇ : Real.sqrt 127 ≥ 0 := Real.sqrt_nonneg 127
        nlinarith [Real.sqrt_nonneg 127, Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
      have h₆ : x + 1 ≥ 0 := by linarith
      have h₇ : 3 - x ≥ x + 1 := by
        nlinarith [Real.sqrt_nonneg 127, Real.sq_sqrt (show 0 ≤ 127 by norm_num)]
      have h₈ : Real.sqrt (3 - x) ≥ Real.sqrt (x + 1) := by
        apply Real.sqrt_le_sqrt
        linarith
      linarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1)]
    have h₃ : Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
      have h₄ : Real.sqrt (3 - x) - Real.sqrt (x + 1) > 1 / 4 := h₁
      have h₅ : Real.sqrt (3 - x) - Real.sqrt (x + 1) ≥ 0 := h₂
      have h₆ : Real.sqrt (Real.sqrt (3 - x) - Real.sqrt (x + 1)) > 1 / 2 := by
        apply Real.lt_sqrt_of_sq_lt
        nlinarith
      exact h₆
    exact h₃
  
  intro x hx
  exact h_final x hx


theorem imo_1974_p5_left : ∀ (a b c d : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 → a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
  intro a b c d h
  have h₁ : a / (a + b + d) + b / (a + b + c) < 1 := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < c := by linarith
    have h₁₄ : 0 < d := by linarith
    have h₁₅ : 0 < a + b + d := by linarith
    have h₁₆ : 0 < a + b + c := by linarith
    have h₁₇ : 0 < (a + b + d) * (a + b + c) := by positivity
    -- Cross-multiply to eliminate denominators
    have h₁₈ : a * (a + b + c) + b * (a + b + d) < (a + b + d) * (a + b + c) := by
      nlinarith [mul_pos h₁₁ h₁₃, mul_pos h₁₁ h₁₄, mul_pos h₁₂ h₁₃, mul_pos h₁₂ h₁₄,
        mul_pos h₁₃ h₁₄]
    -- Divide both sides by (a + b + d)(a + b + c)
    have h₁₉ : a / (a + b + d) + b / (a + b + c) < 1 := by
      have h₂₀ : a / (a + b + d) + b / (a + b + c) = (a * (a + b + c) + b * (a + b + d)) / ((a + b + d) * (a + b + c)) := by
        field_simp [h₁₅.ne', h₁₆.ne']
        <;> ring
        <;> field_simp [h₁₅.ne', h₁₆.ne']
        <;> ring
      rw [h₂₀]
      have h₂₁ : (a * (a + b + c) + b * (a + b + d)) / ((a + b + d) * (a + b + c)) < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith [mul_pos h₁₁ h₁₃, mul_pos h₁₁ h₁₄, mul_pos h₁₂ h₁₃, mul_pos h₁₂ h₁₄,
          mul_pos h₁₃ h₁₄]
      linarith
    exact h₁₉
  
  have h₂ : c / (b + c + d) + d / (a + c + d) < 1 := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < d := by linarith
    have h₂₅ : 0 < b + c + d := by linarith
    have h₂₆ : 0 < a + c + d := by linarith
    have h₂₇ : 0 < (b + c + d) * (a + c + d) := by positivity
    -- Cross-multiply to eliminate denominators
    have h₂₈ : c * (a + c + d) + d * (b + c + d) < (b + c + d) * (a + c + d) := by
      nlinarith [mul_pos h₂₁ h₂₃, mul_pos h₂₁ h₂₄, mul_pos h₂₂ h₂₃, mul_pos h₂₂ h₂₄,
        mul_pos h₂₃ h₂₄]
    -- Divide both sides by (b + c + d)(a + c + d)
    have h₂₉ : c / (b + c + d) + d / (a + c + d) < 1 := by
      have h₃₀ : c / (b + c + d) + d / (a + c + d) = (c * (a + c + d) + d * (b + c + d)) / ((b + c + d) * (a + c + d)) := by
        field_simp [h₂₅.ne', h₂₆.ne']
        <;> ring
        <;> field_simp [h₂₅.ne', h₂₆.ne']
        <;> ring
      rw [h₃₀]
      have h₃₁ : (c * (a + c + d) + d * (b + c + d)) / ((b + c + d) * (a + c + d)) < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith [mul_pos h₂₁ h₂₃, mul_pos h₂₁ h₂₄, mul_pos h₂₂ h₂₃, mul_pos h₂₂ h₂₄,
          mul_pos h₂₃ h₂₄]
      linarith
    exact h₂₉
  
  have h_main : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) < 2 := by
    linarith
  
  exact h_main


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
    have h₁₈ : 0 < a + b + c + d := by linarith
    -- Use the fact that if x < y and z > 0, then z/x > z/y
    have h₁₉ : a / (a + b + d) > a / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₁₉
  
  have h₂ : b / (a + b + c) > b / (a + b + c + d) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < d := by linarith
    have h₂₅ : 0 < a + b + c := by linarith
    have h₂₆ : 0 < a + b + c + d := by linarith
    have h₂₇ : a + b + c < a + b + c + d := by linarith
    have h₂₈ : 0 < a + b + c + d := by linarith
    -- Use the fact that if x < y and z > 0, then z/x > z/y
    have h₂₉ : b / (a + b + c) > b / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₂₉
  
  have h₃ : c / (b + c + d) > c / (a + b + c + d) := by
    have h₃₁ : 0 < a := by linarith
    have h₃₂ : 0 < b := by linarith
    have h₃₃ : 0 < c := by linarith
    have h₃₄ : 0 < d := by linarith
    have h₃₅ : 0 < b + c + d := by linarith
    have h₃₆ : 0 < a + b + c + d := by linarith
    have h₃₇ : b + c + d < a + b + c + d := by linarith
    have h₃₈ : 0 < a + b + c + d := by linarith
    -- Use the fact that if x < y and z > 0, then z/x > z/y
    have h₃₉ : c / (b + c + d) > c / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₃₉
  
  have h₄ : d / (a + c + d) > d / (a + b + c + d) := by
    have h₄₁ : 0 < a := by linarith
    have h₄₂ : 0 < b := by linarith
    have h₄₃ : 0 < c := by linarith
    have h₄₄ : 0 < d := by linarith
    have h₄₅ : 0 < a + c + d := by linarith
    have h₄₆ : 0 < a + b + c + d := by linarith
    have h₄₇ : a + c + d < a + b + c + d := by linarith
    have h₄₈ : 0 < a + b + c + d := by linarith
    -- Use the fact that if x < y and z > 0, then z/x > z/y
    have h₄₉ : d / (a + c + d) > d / (a + b + c + d) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mpr
      nlinarith
    exact h₄₉
  
  have h₅ : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > 1 := by
    have h₅₁ : 0 < a := by linarith
    have h₅₂ : 0 < b := by linarith
    have h₅₃ : 0 < c := by linarith
    have h₅₄ : 0 < d := by linarith
    have h₅₅ : 0 < a + b + c + d := by linarith
    -- Summing the inequalities and simplifying
    have h₅₆ : a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d) > a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) := by
      linarith
    have h₅₇ : a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) = 1 := by
      have h₅₇₁ : a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) = (a + b + c + d) / (a + b + c + d) := by
        field_simp [h₅₅.ne']
        <;> ring
        <;> field_simp [h₅₅.ne']
        <;> ring
      rw [h₅₇₁]
      have h₅₇₂ : (a + b + c + d) / (a + b + c + d) = 1 := by
        field_simp [h₅₅.ne']
      rw [h₅₇₂]
    linarith
  
  exact h₅
