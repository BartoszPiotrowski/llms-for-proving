
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_example_11 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    have h₄₁ : 0 ≤ (a - b) ^ 2 := by nlinarith
    have h₄₂ : 0 ≤ a + b := by nlinarith
    have h₄₃ : 0 ≤ (a + b) * (a - b) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (a - b), mul_pos h₁ h₂, mul_pos h₁ h₁, mul_pos h₂ h₂]
  
  have h₅ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    have h₅₁ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := h₄
    have h₅₂ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b) + a * b * c := by nlinarith
    have h₅₃ : a * b * (a + b) + a * b * c = a * b * (a + b + c) := by ring
    nlinarith
  
  have h₆ : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := by
    have h₆₁ : 0 ≤ (b - c) ^ 2 := by nlinarith
    have h₆₂ : 0 ≤ b + c := by nlinarith
    have h₆₃ : 0 ≤ (b + c) * (b - c) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (b - c), mul_pos h₂ h₃, mul_pos h₂ h₂, mul_pos h₃ h₃]
  
  have h₇ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    have h₇₁ : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := h₆
    have h₇₂ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (b + c) + a * b * c := by nlinarith
    have h₇₃ : b * c * (b + c) + a * b * c = b * c * (a + b + c) := by ring
    nlinarith
  
  have h₈ : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := by
    have h₈₁ : 0 ≤ (c - a) ^ 2 := by nlinarith
    have h₈₂ : 0 ≤ c + a := by nlinarith
    have h₈₃ : 0 ≤ (c + a) * (c - a) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (c - a), mul_pos h₃ h₁, mul_pos h₃ h₃, mul_pos h₁ h₁]
  
  have h₉ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    have h₉₁ : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := h₈
    have h₉₂ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (c + a) + a * b * c := by nlinarith
    have h₉₃ : c * a * (c + a) + a * b * c = c * a * (a + b + c) := by
      ring
    nlinarith
  
  have h₁₀ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₁₀₁ : 0 < a * b * (a + b + c) := by positivity
    have h₁₀₂ : 0 < a ^ 3 + b ^ 3 + a * b * c := by positivity
    have h₁₀₃ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := h₅
    have h₁₀₄ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₀₄
  
  have h₁₁ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₁₁₁ : 0 < b * c * (a + b + c) := by positivity
    have h₁₁₂ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₁₁₃ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := h₇
    have h₁₁₄ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₁₄
  
  have h₁₂ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    have h₁₂₁ : 0 < c * a * (a + b + c) := by positivity
    have h₁₂₂ : 0 < c ^ 3 + a ^ 3 + a * b * c := by positivity
    have h₁₂₃ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := h₉
    have h₁₂₄ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₂₄
  
  have h₁₃ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    have h₁₃₁ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
      linarith
    have h₁₃₂ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
      have h₁₃₃ : 0 < a * b := by positivity
      have h₁₃₄ : 0 < b * c := by positivity
      have h₁₃₅ : 0 < c * a := by positivity
      have h₁₃₆ : 0 < a * b * c := by positivity
      have h₁₃₇ : 0 < a * b * c * (a + b + c) := by positivity
      field_simp [h₁₃₃.ne', h₁₃₄.ne', h₁₃₅.ne', h₁₃₆.ne']
      ring_nf
      <;> field_simp [h₁₃₃.ne', h₁₃₄.ne', h₁₃₅.ne', h₁₃₆.ne']
      <;> ring_nf
      <;> nlinarith
    linarith
  
  exact h₁₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_example_13 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ 3 / 5 := by
  intro a b c h
  have h_main : (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ 3 / 5 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * c),
      sq_nonneg (a ^ 2 * c - c ^ 2 * a), sq_nonneg (b ^ 2 * a - a ^ 2 * b), sq_nonneg (c ^ 2 * b - b ^ 2 * c),
      mul_nonneg h₄.le (sq_nonneg (a - b)), mul_nonneg h₅.le (sq_nonneg (b - c)), mul_nonneg h₆.le (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃),
      mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁), mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_2_1 : ∀ (x y z : ℝ), x ≤ y ∧ y ≤ z ∧ z ≤ x → x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) ≥ 0 := by
  intro x y z h
  have h₁ : x = y ∧ y = z := by
    have h₂ : x ≤ y := h.1
    have h₃ : y ≤ z := h.2.1
    have h₄ : z ≤ x := h.2.2
    have h₅ : x = y := by
      linarith
    have h₆ : y = z := by
      linarith
    exact ⟨h₅, h₆⟩
  
  have h₂ : x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) = 0 := by
    have h₃ : x = y := h₁.1
    have h₄ : y = z := h₁.2
    have h₅ : x = z := by linarith
    have h₆ : x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) = 0 := by
      simp [h₃, h₄, h₅]
      <;> ring
      <;> nlinarith
    exact h₆
  
  have h₃ : x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) ≥ 0 := by
    rw [h₂]
    <;> norm_num
    <;> linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_2_2 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → (x * y + y * z + z * x) * (1 / (x + y) ^ 2 + 1 / (y + z) ^ 2 + 1 / (z + x) ^ 2) ≥ 9 / 4 := by
  intro x y z h
  have h_main : (x * y + y * z + z * x) * (1 / (x + y) ^ 2 + 1 / (y + z) ^ 2 + 1 / (z + x) ^ 2) ≥ 9 / 4 := by
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    have h₇ : 0 < x * y * z := by positivity
    have h₈ : 0 < x * y * z * x := by positivity
    have h₉ : 0 < x * y * z * y := by positivity
    have h₁₀ : 0 < x * y * z * z := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_nonneg h₄.le (sq_nonneg (x - y)), mul_nonneg h₅.le (sq_nonneg (y - z)), mul_nonneg h₆.le (sq_nonneg (z - x)),
      mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (x + y - z)), mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (y + z - x)),
      mul_nonneg (sq_nonneg (z - x)) (sq_nonneg (z + x - y)), mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_2_5 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) ≤ 9 / (4 * (x + y + z)) := by
  intro x y z h
  have h_main : x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) ≤ 9 / (4 * (x + y + z)) := by
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x * y := by positivity
    have h₅ : 0 < y * z := by positivity
    have h₆ : 0 < z * x := by positivity
    have h₇ : 0 < x * y * z := by positivity
    have h₈ : 0 < x * y * z * (x + y + z) := by positivity
    have h₉ : 0 < x * y * z * (x + y + z) * (x + y + z) := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
      sq_nonneg (x^2 - x * y), sq_nonneg (y^2 - y * z), sq_nonneg (z^2 - z * x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)), mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (z - x)),
      mul_nonneg (sq_nonneg (z - x)) (sq_nonneg (x - y)), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁,
      mul_pos (mul_pos h₁ h₂) (mul_pos h₂ h₃), mul_pos (mul_pos h₂ h₃) (mul_pos h₃ h₁),
      mul_pos (mul_pos h₃ h₁) (mul_pos h₁ h₂)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_1_left : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 → 0 ≤ y * z + z * x + x * y - 2 * x * y * z := by
  intro x y z h
  have h_main : 0 ≤ y * z + z * x + x * y - 2 * x * y * z := by
    have h₁ : x ≥ 0 := by linarith
    have h₂ : y ≥ 0 := by linarith
    have h₃ : z ≥ 0 := by linarith
    have h₄ : x + y + z = 1 := by linarith
    have h₅ : x * y ≥ 0 := by nlinarith
    have h₆ : y * z ≥ 0 := by nlinarith
    have h₇ : z * x ≥ 0 := by nlinarith
    have h₈ : x * y * z ≥ 0 := by positivity
    -- Consider the cases where one of the variables is zero or all are positive
    by_cases h₉ : x = 0
    · -- Case 1: x = 0
      simp [h₉]
      <;> nlinarith
    · -- Case 2: x ≠ 0
      by_cases h₁₀ : y = 0
      · -- Subcase 2.1: y = 0
        simp [h₁₀]
        <;> nlinarith
      · -- Subcase 2.2: y ≠ 0
        by_cases h₁₁ : z = 0
        · -- Subcase 2.2.1: z = 0
          simp [h₁₁]
          <;> nlinarith
        · -- Subcase 2.2.2: z ≠ 0
          -- All variables are positive
          have h₁₂ : 0 < x := by positivity
          have h₁₃ : 0 < y := by positivity
          have h₁₄ : 0 < z := by positivity
          have h₁₅ : x * y * z > 0 := by positivity
          -- Use non-linear arithmetic to prove the inequality
          nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁,
            mul_nonneg (sq_nonneg (x - y)) h₃, mul_nonneg (sq_nonneg (y - z)) h₁,
            mul_nonneg (sq_nonneg (z - x)) h₂]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_2 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c ≥ a * b * c → a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b * c := by
  intro a b c h
  have h₁ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₂ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₂ : a * b + b * c + c * a ≥ a * b * c := by
    have h₃ : 0 < a * b := by
      nlinarith
    have h₄ : 0 < b * c := by
      nlinarith
    have h₅ : 0 < c * a := by
      nlinarith
    have h₆ : 0 < a * b * c := by
      nlinarith
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos h₃ h₄, mul_pos h₄ h₅, mul_pos h₅ h₃,
      mul_pos (mul_pos h₃ h₄) h₅,
      mul_pos (mul_pos h₄ h₅) h₃,
      mul_pos (mul_pos h₅ h₃) h₄]
  
  have h₃ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b * c := by
    nlinarith [h₁, h₂]
    <;>
    (try nlinarith) <;>
    (try linarith) <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])
    <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)])
    <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2.1, mul_pos h.2.2.1 h.1])
    <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2.1, mul_pos h.2.2.1 h.1, mul_pos (mul_pos h.1 h.2.1) h.2.2.1])
    <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2.1, mul_pos h.2.2.1 h.1, mul_pos (mul_pos h.1 h.2.1) h.2.2.1, mul_pos (mul_pos h.2.1 h.2.2.1) h.1, mul_pos (mul_pos h.2.2.1 h.1) h.2.1])
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_3 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c) := by
  intro a b c h
  have h_main : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c) := by
    rcases h with ⟨ha, hb, hc, h⟩
    have h₁ : 0 < a * b := by positivity
    have h₂ : 0 < a * c := by positivity
    have h₃ : 0 < b * c := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a * b * c - 1), mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (b - 1)),
      mul_nonneg (sq_nonneg (a - 1)) (sq_nonneg (c - 1)), mul_nonneg (sq_nonneg (b - 1)) (sq_nonneg (c - 1)),
      mul_nonneg (sq_nonneg (a * b - 1)) (sq_nonneg (a * c - 1)),
      mul_nonneg (sq_nonneg (a * b - 1)) (sq_nonneg (b * c - 1)),
      mul_nonneg (sq_nonneg (a * c - 1)) (sq_nonneg (b * c - 1))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_3_1_1 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (x * y) := by
  intro x y h
  have h₁ : x ^ 4 + y ^ 2 ≥ 2 * x ^ 2 * y := by
    have h₁₀ : 0 < x := h.1
    have h₁₁ : 0 < y := h.2
    have h₁₂ : 0 < x ^ 2 := by positivity
    have h₁₃ : 0 < y := h₁₁
    have h₁₄ : 0 < x ^ 4 := by positivity
    have h₁₅ : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (x ^ 2 - y), sq_nonneg (x ^ 2 + y), sq_nonneg (x ^ 2 - 2 * x * y + y ^ 2),
      sq_nonneg (x ^ 2 + 2 * x * y + y ^ 2), mul_pos h₁₀ h₁₁, mul_pos h₁₂ h₁₃,
      mul_pos (sq_pos_of_pos h₁₀) (sq_pos_of_pos h₁₁)]

  have h₂ : x / (x ^ 4 + y ^ 2) ≤ 1 / (2 * x * y) := by
    have h₂₁ : 0 < x := h.1
    have h₂₂ : 0 < y := h.2
    have h₂₃ : 0 < x ^ 4 + y ^ 2 := by positivity
    have h₂₄ : 0 < 2 * x * y := by positivity
    have h₂₅ : 0 < x ^ 4 + y ^ 2 := by positivity
    -- Use the division inequality to transform the goal into a multiplication inequality
    have h₂₆ : x / (x ^ 4 + y ^ 2) ≤ 1 / (2 * x * y) := by
      -- Use the division inequality to transform the goal into a multiplication inequality
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to prove the inequality
      nlinarith [h₁, mul_nonneg h₂₁.le h₂₂.le, mul_nonneg (sq_nonneg x) h₂₂.le,
        mul_nonneg (sq_nonneg y) h₂₁.le]
    exact h₂₆
  
  have h₃ : y ^ 4 + x ^ 2 ≥ 2 * y ^ 2 * x := by
    have h₃₁ : 0 < x := h.1
    have h₃₂ : 0 < y := h.2
    have h₃₃ : 0 < x ^ 2 := by positivity
    have h₃₄ : 0 < y ^ 2 := by positivity
    have h₃₅ : 0 < y ^ 4 := by positivity
    have h₃₆ : 0 < x ^ 2 * y ^ 2 := by positivity
    nlinarith [sq_nonneg (y ^ 2 - x), sq_nonneg (y ^ 2 + x), sq_nonneg (y ^ 2 - 2 * y * x + x ^ 2),
      sq_nonneg (y ^ 2 + 2 * y * x + x ^ 2), mul_pos h₃₁ h₃₂, mul_pos h₃₃ h₃₁,
      mul_pos h₃₄ h₃₂, mul_pos (mul_pos h₃₁ h₃₂) h₃₁, mul_pos (mul_pos h₃₁ h₃₂) h₃₂]
  
  have h₄ : y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) := by
    have h₄₁ : 0 < x := h.1
    have h₄₂ : 0 < y := h.2
    have h₄₃ : 0 < y ^ 4 + x ^ 2 := by positivity
    have h₄₄ : 0 < 2 * x * y := by positivity
    have h₄₅ : y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [h₃, mul_pos h₄₁ h₄₂, mul_pos (sq_pos_of_pos h₄₁) (sq_pos_of_pos h₄₂),
        mul_pos (sq_pos_of_pos h₄₂) (sq_pos_of_pos h₄₁)]
    exact h₄₅
  
  have h₅ : x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (x * y) := by
    have h₅₁ : x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) + 1 / (2 * x * y) := by
      have h₅₂ : x / (x ^ 4 + y ^ 2) ≤ 1 / (2 * x * y) := h₂
      have h₅₃ : y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) := h₄
      have h₅₄ : x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) + 1 / (2 * x * y) := by
        linarith
      exact h₅₄
    have h₅₅ : 1 / (2 * x * y) + 1 / (2 * x * y) = 1 / (x * y) := by
      have h₅₅₁ : 0 < x := h.1
      have h₅₅₂ : 0 < y := h.2
      have h₅₅₃ : 0 < x * y := by positivity
      have h₅₅₄ : 0 < 2 * x * y := by positivity
      field_simp [h₅₅₁.ne', h₅₅₂.ne', h₅₅₃.ne', h₅₅₄.ne']
      <;> ring_nf
      <;> field_simp [h₅₅₁.ne', h₅₅₂.ne', h₅₅₃.ne', h₅₅₄.ne']
      <;> ring_nf
      <;> linarith
    have h₅₆ : x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (x * y) := by
      linarith
    exact h₅₆
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_5_2_1 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1 → x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  intro x y z h
  have h₁ : x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
    have h₂ : 0 < x := by linarith
    have h₃ : 0 < y := by linarith
    have h₄ : 0 < z := by linarith
    have h₅ : x * y * z = 1 := by linarith
    have h₆ : 0 < x * y := by positivity
    have h₇ : 0 < x * z := by positivity
    have h₈ : 0 < y * z := by positivity
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_nonneg (sub_nonneg.mpr h₂.le) (sub_nonneg.mpr h₃.le),
      mul_nonneg (sub_nonneg.mpr h₂.le) (sub_nonneg.mpr h₄.le),
      mul_nonneg (sub_nonneg.mpr h₃.le) (sub_nonneg.mpr h₄.le),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  exact h₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_5_2_4 : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 → x ^ 3 + y ^ 3 + z ^ 3 + 6 * x * y * z ≥ 1 / 4 := by
  intro x y z h
  have h_main : x ^ 3 + y ^ 3 + z ^ 3 + 6 * x * y * z ≥ 1 / 4 := by
    rcases h with ⟨hx, hy, hz, hsum⟩
    have h₁ : (x + y + z) ^ 2 = 1 := by
      rw [hsum]
      <;> ring
    have h₂ : 0 ≤ x * y := by positivity
    have h₃ : 0 ≤ y * z := by positivity
    have h₄ : 0 ≤ z * x := by positivity
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx,
      sq_nonneg (x + y + z), sq_nonneg (x - y + z), sq_nonneg (x + y - z),
      sq_nonneg (x - y - z)]
  exact h_main
