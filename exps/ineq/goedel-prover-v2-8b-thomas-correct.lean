
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_1 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
  intro a b c h
  have h_main : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_nonneg h.1.le h.2.1.le, mul_nonneg h.2.1.le h.2.2.le, mul_nonneg h.2.2.le h.1.le,
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)), mul_pos h.1 h.2.1, mul_pos h.2.1 h.2.2,
      mul_pos h.2.2 h.1, mul_pos (mul_pos h.1 h.2.1) (mul_pos h.2.1 h.2.2),
      mul_pos (mul_pos h.2.1 h.2.2) (mul_pos h.2.2 h.1), mul_pos (mul_pos h.2.2 h.1) (mul_pos h.1 h.2.1),
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

theorem thomas_example_2 : ∀ (a b c : ℝ), a * b * c = 1 → a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  intro a b c h
  have h_main : a ^ 2 + b ^ 2 + c ^ 2 - a - b - c ≥ 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_self_nonneg (a + b + c - 3)]
  
  have h_final : a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    have h₁ : a ^ 2 + b ^ 2 + c ^ 2 - a - b - c ≥ 0 := h_main
    have h₂ : a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
      linarith
    exact h₂
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_4 : ∀ (a b c d e : ℝ), a + b + c + d + e = 8 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 16 → e ≤ 16 / 5 := by
  intro a b c d e h
  have h₁ : e ≥ 0 := by
    by_contra h₁
    -- Assume for contradiction that e < 0
    have h₂ : e < 0 := by linarith
    have h₃ : a + b + c + d = 8 - e := by linarith
    have h₄ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by
      have h₅ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 16 := h.2
      linarith
    have h₅ : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have h₆ : (8 - e) ^ 2 ≤ 4 * (16 - e ^ 2) := by
      rw [h₃] at h₅
      rw [h₄] at h₅
      linarith
    have h₇ : e * (5 * e - 16) ≤ 0 := by
      nlinarith
    have h₈ : e * (5 * e - 16) > 0 := by
      have h₉ : e < 0 := h₂
      have h₁₀ : 5 * e - 16 < 0 := by nlinarith
      nlinarith
    linarith
  
  have h₂ : e * (5 * e - 16) ≤ 0 := by
    have h₃ : a + b + c + d = 8 - e := by linarith
    have h₄ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by
      have h₅ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 16 := h.2
      linarith
    have h₅ : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have h₆ : (8 - e) ^ 2 ≤ 4 * (16 - e ^ 2) := by
      rw [h₃] at h₅
      rw [h₄] at h₅
      linarith
    have h₇ : e * (5 * e - 16) ≤ 0 := by
      nlinarith
    exact h₇
  
  have h₃ : e ≤ 16 / 5 := by
    by_contra h₃
    have h₄ : e > 16 / 5 := by linarith
    have h₅ : e * (5 * e - 16) > 0 := by
      have h₅₁ : 5 * e - 16 > 0 := by linarith
      have h₅₂ : e > 0 := by linarith
      nlinarith
    linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_5 : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d → 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
  intro a b c d h
  have h₁ : 0 < a := by
    linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    <;> linarith
  
  have h₂ : 0 < b := by
    linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    <;> linarith
  
  have h₃ : 0 < c := by
    linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    <;> linarith
  
  have h₄ : 0 < d := by
    linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    <;> linarith
  
  have h₅ : 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
    have h₅₁ : 0 < a + b + c + d := by
      linarith [h₁, h₂, h₃, h₄]
    have h₅₂ : 0 < a * b := by positivity
    have h₅₃ : 0 < a * c := by positivity
    have h₅₄ : 0 < a * d := by positivity
    have h₅₅ : 0 < b * c := by positivity
    have h₅₆ : 0 < b * d := by positivity
    have h₅₇ : 0 < c * d := by positivity
    have h₅₈ : 0 < a * b * c := by positivity
    have h₅₉ : 0 < a * b * d := by positivity
    have h₅₁₀ : 0 < a * c * d := by positivity
    have h₅₁₁ : 0 < b * c * d := by positivity
    have h₅₁₂ : 0 < a * b * c * d := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 2), sq_nonneg (a - d / 4), sq_nonneg (b - c / 2), sq_nonneg (b - d / 4), sq_nonneg (c / 2 - d / 4),
      sq_nonneg (a + b - c / 2), sq_nonneg (a + b - d / 4), sq_nonneg (a + c / 2 - d / 4), sq_nonneg (b + c / 2 - d / 4)]
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_8 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 → a ^ 3 + b ^ 3 + c ^ 3 + 6 * a * b * c ≥ 1 / 4 := by
  intro a b c h
  have h_main : a ^ 3 + b ^ 3 + c ^ 3 + 6 * a * b * c ≥ 1 / 4 := by
    have h₁ : a + b + c = 1 := by linarith
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    have h₄ : 0 ≤ c := by linarith
    have h₅ : 0 ≤ a * b := by positivity
    have h₆ : 0 ≤ b * c := by positivity
    have h₇ : 0 ≤ a * c := by positivity
    have h₈ : (a + b + c) ^ 2 = 1 := by
      rw [h₁]
      <;> ring
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₂ h₃, mul_nonneg h₃ h₄, mul_nonneg h₄ h₂,
      sq_nonneg (a + b + c), sq_nonneg (a - b + c), sq_nonneg (a + b - c),
      sq_nonneg (a - b - c)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_9_left : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d → 1 < a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) := by
  intro a b c d h
  have h_main : 1 < a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < d := by linarith
    have h₅ : 0 < a + b + d := by linarith
    have h₆ : 0 < b + c + a := by linarith
    have h₇ : 0 < b + c + d := by linarith
    have h₈ : 0 < a + c + d := by linarith
    have h₉ : 0 < a * b := by positivity
    have h₁₀ : 0 < a * c := by positivity
    have h₁₁ : 0 < a * d := by positivity
    have h₁₂ : 0 < b * c := by positivity
    have h₁₃ : 0 < b * d := by positivity
    have h₁₄ : 0 < c * d := by positivity
    field_simp
    rw [← sub_pos]
    field_simp
    ring_nf
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_9_right : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d → a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < 2 := by
  intro a b c d h
  have h_main : a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < 2 := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < d := by linarith
    have h₅ : 0 < a + b + d := by linarith
    have h₆ : 0 < b + c + a := by linarith
    have h₇ : 0 < b + c + d := by linarith
    have h₈ : 0 < a + c + d := by linarith
    have h₉ : 0 < a * b := by positivity
    have h₁₀ : 0 < a * c := by positivity
    have h₁₁ : 0 < a * d := by positivity
    have h₁₂ : 0 < b * c := by positivity
    have h₁₃ : 0 < b * d := by positivity
    have h₁₄ : 0 < c * d := by positivity
    -- Use the fact that each term is positive and less than 1 to bound the sum
    have h₁₅ : a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < 2 := by
      -- Use the fact that each term is positive and less than 1 to bound the sum
      apply lt_of_sub_pos
      field_simp
      ring_nf
      nlinarith [mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₁ h₄, mul_pos h₂ h₃, mul_pos h₂ h₄, mul_pos h₃ h₄,
        mul_pos (mul_pos h₁ h₂) h₃, mul_pos (mul_pos h₁ h₂) h₄, mul_pos (mul_pos h₁ h₃) h₂,
        mul_pos (mul_pos h₁ h₃) h₄, mul_pos (mul_pos h₁ h₄) h₂, mul_pos (mul_pos h₁ h₄) h₃,
        mul_pos (mul_pos h₂ h₃) h₄, mul_pos (mul_pos h₂ h₄) h₃, mul_pos (mul_pos h₃ h₄) h₂,
        mul_pos (mul_pos h₃ h₄) h₁]
    exact h₁₅
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_13 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → 1 / (a * (1 + b)) + 1 / (b * (1 + c)) + 1 / (c * (1 + a)) ≥ 3 / (1 + a * b * c) := by
  intro a b c h
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
  -- Use the AM-GM inequality to prove the desired inequality
  have h₁₁ : 1 / (a * (1 + b)) + 1 / (b * (1 + c)) + 1 / (c * (1 + a)) ≥ 3 / (1 + a * b * c) := by
    -- Use the fact that the denominator is positive to simplify the inequality
    have h₁₂ : 0 < 1 + a * b * c := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    have h₁₃ : 0 < a * b := by positivity
    have h₁₄ : 0 < a * c := by positivity
    have h₁₅ : 0 < b * c := by positivity
    -- Use the AM-GM inequality to prove the desired inequality
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to prove the inequality
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a * b * c - a), sq_nonneg (a * b * c - b), sq_nonneg (a * b * c - c)]
  -- Use the previously proven inequality to conclude the proof
  exact h₁₁

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_14 : ∀ (a b x y z : ℝ), 0 < a ∧ 0 < b ∧ 0 < x ∧ 0 < y ∧ 0 < z → x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
  intro a b x y z h
  have h₁ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < x := by linarith
    have h₁₄ : 0 < y := by linarith
    have h₁₅ : 0 < z := by linarith
    have h₁₆ : 0 < a * y + b * z := by positivity
    have h₁₇ : 0 < a * z + b * x := by positivity
    have h₁₈ : 0 < a * x + b * y := by positivity
    have h₁₉ : 0 < x * y + y * z + z * x := by positivity
    have h₂₀ : 0 < a + b := by positivity
    have h₂₁ : 0 < (a + b) * (x * y + y * z + z * x) := by positivity
    -- Use Titu's lemma to prove the inequality
    have h₂₂ : x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y) ≥ (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) := by
      have h₂₃ : 0 < a * x * y + b * x * z := by positivity
      have h₂₄ : 0 < a * y * z + b * y * x := by positivity
      have h₂₅ : 0 < a * z * x + b * z * y := by positivity
      have h₂₆ : 0 < (a * x * y + b * x * z) * (a * y * z + b * y * x) := by positivity
      have h₂₇ : 0 < (a * x * y + b * x * z) * (a * z * x + b * z * y) := by positivity
      have h₂₈ : 0 < (a * y * z + b * y * x) * (a * z * x + b * z * y) := by positivity
      -- Use the Cauchy-Schwarz inequality to prove the inequality
      have h₂₉ : (x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y)) ≥ (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) := by
        field_simp
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x * (a * y * z + b * y * x) - y * (a * x * y + b * x * z)),
          sq_nonneg (y * (a * z * x + b * z * y) - z * (a * y * z + b * y * x)),
          sq_nonneg (z * (a * x * y + b * x * z) - x * (a * z * x + b * z * y))]
      exact h₂₉
    have h₃₀ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = x ^ 2 / (a * x * y + b * x * z) + y ^ 2 / (a * y * z + b * y * x) + z ^ 2 / (a * z * x + b * z * y) := by
      have h₃₁ : x / (a * y + b * z) = x ^ 2 / (a * x * y + b * x * z) := by
        have h₃₂ : a * x * y + b * x * z = x * (a * y + b * z) := by ring
        rw [h₃₂]
        have h₃₃ : 0 < x * (a * y + b * z) := by positivity
        field_simp [h₃₃.ne']
        <;> ring
        <;> field_simp [h₁₆.ne']
        <;> ring
      have h₃₄ : y / (a * z + b * x) = y ^ 2 / (a * y * z + b * y * x) := by
        have h₃₅ : a * y * z + b * y * x = y * (a * z + b * x) := by ring
        rw [h₃₅]
        have h₃₆ : 0 < y * (a * z + b * x) := by positivity
        field_simp [h₃₆.ne']
        <;> ring
        <;> field_simp [h₁₇.ne']
        <;> ring
      have h₃₇ : z / (a * x + b * y) = z ^ 2 / (a * z * x + b * z * y) := by
        have h₃₈ : a * z * x + b * z * y = z * (a * x + b * y) := by ring
        rw [h₃₈]
        have h₃₉ : 0 < z * (a * x + b * y) := by positivity
        field_simp [h₃₉.ne']
        <;> ring
        <;> field_simp [h₁₈.ne']
        <;> ring
      rw [h₃₁, h₃₄, h₃₇]
    rw [h₃₀]
    exact h₂₂
  
  have h₂ : (x + y + z)^2 ≥ 3 * (x * y + y * z + z * x) := by
    have h₂₁ : 0 < x := by linarith
    have h₂₂ : 0 < y := by linarith
    have h₂₃ : 0 < z := by linarith
    have h₂₄ : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
      ring
    rw [h₂₄]
    have h₂₅ : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h₃ : (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
    have h₃₁ : 0 < a := by linarith
    have h₃₂ : 0 < b := by linarith
    have h₃₃ : 0 < a + b := by linarith
    have h₃₄ : 0 < x * y + y * z + z * x := by
      nlinarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    have h₃₅ : 0 < (a + b) * (x * y + y * z + z * x) := by positivity
    have h₃₆ : 0 < a + b := by linarith
    have h₃₇ : (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
      rw [ge_iff_le]
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [h₂, h₃₄, h₃₅, h₃₆]
    exact h₃₇
  
  have h₄ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
    have h₄₁ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) := by
      exact h₁
    have h₄₂ : (x + y + z) ^ 2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
      exact h₃
    have h₄₃ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
      linarith
    exact h₄₃
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_24 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b ≥ c ∧ b + c ≥ a ∧ c + a ≥ b → 2 * a ^ 2 * (b + c) + 2 * b ^ 2 * (c + a) + 2 * c ^ 2 * (a + b) ≥ a ^ 3 + b ^ 3 + c ^ 3 + 9 * a * b * c := by
  intro a b c h
  have h_main : 2 * a ^ 2 * (b + c) + 2 * b ^ 2 * (c + a) + 2 * c ^ 2 * (a + b) ≥ a ^ 3 + b ^ 3 + c ^ 3 + 9 * a * b * c := by
    nlinarith [sq_nonneg (a + b - 3 * c), sq_nonneg (b + c - 3 * a), sq_nonneg (c + a - 3 * b),
      mul_nonneg (sub_nonneg.mpr h.2.2.2.1) (sub_nonneg.mpr h.2.2.2.2.1),
      mul_nonneg (sub_nonneg.mpr h.2.2.2.2.1) (sub_nonneg.mpr h.2.2.2.2.2),
      mul_nonneg (sub_nonneg.mpr h.2.2.2.2.2) (sub_nonneg.mpr h.2.2.2.1),
      mul_nonneg (sub_nonneg.mpr h.2.2.2.1) (sub_nonneg.mpr h.2.2.2.2.1),
      mul_nonneg (sub_nonneg.mpr h.2.2.2.2.1) (sub_nonneg.mpr h.2.2.2.2.2),
      mul_nonneg (sub_nonneg.mpr h.2.2.2.2.2) (sub_nonneg.mpr h.2.2.2.1),
      mul_nonneg (sq_nonneg (a - b)) (by nlinarith : (0 : ℝ) ≤ 2),
      mul_nonneg (sq_nonneg (b - c)) (by nlinarith : (0 : ℝ) ≤ 2),
      mul_nonneg (sq_nonneg (c - a)) (by nlinarith : (0 : ℝ) ≤ 2),
      mul_nonneg (sq_nonneg (a + b - c)) (by nlinarith : (0 : ℝ) ≤ 2),
      mul_nonneg (sq_nonneg (b + c - a)) (by nlinarith : (0 : ℝ) ≤ 2),
      mul_nonneg (sq_nonneg (c + a - b)) (by nlinarith : (0 : ℝ) ≤ 2)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_27 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 + 16 * a ^ 3 * b ^ 3 + 16 * b ^ 3 * c ^ 3 + 16 * c ^ 3 * a ^ 3 ≥ 9 * a ^ 4 * (b ^ 2 + c ^ 2) + 9 * b ^ 4 * (c ^ 2 + a ^ 2) + 9 * c ^ 4 * (a ^ 2 + b ^ 2) := by
  have h_main : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 + 16 * a ^ 3 * b ^ 3 + 16 * b ^ 3 * c ^ 3 + 16 * c ^ 3 * a ^ 3 ≥ 9 * a ^ 4 * (b ^ 2 + c ^ 2) + 9 * b ^ 4 * (c ^ 2 + a ^ 2) + 9 * c ^ 4 * (a ^ 2 + b ^ 2) := by
    intro a b c ⟨ha, hb, hc⟩
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      sq_nonneg (a ^ 2 - 2 * a * b + b ^ 2), sq_nonneg (b ^ 2 - 2 * b * c + c ^ 2),
      sq_nonneg (c ^ 2 - 2 * c * a + a ^ 2), mul_nonneg ha (sq_nonneg (a - b)),
      mul_nonneg hb (sq_nonneg (b - c)), mul_nonneg hc (sq_nonneg (c - a)),
      mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hb (sq_nonneg (b - a)),
      mul_nonneg hc (sq_nonneg (c - b)), mul_nonneg (sq_nonneg a) (sq_nonneg b),
      mul_nonneg (sq_nonneg b) (sq_nonneg c), mul_nonneg (sq_nonneg c) (sq_nonneg a),
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

theorem thomas_example_28 : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ≤ 1 / 2 ∧ b ≤ 1 / 2 ∧ c ≤ 1 / 2 ∧ a + b + c = 1 → a ^ 3 + b ^ 3 + c ^ 3 + 4 * a * b * c ≤ 9 / 32 := by
  have h_main : ∀ (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ≤ 1 / 2 ∧ b ≤ 1 / 2 ∧ c ≤ 1 / 2 ∧ a + b + c = 1 → a ^ 3 + b ^ 3 + c ^ 3 + 4 * a * b * c ≤ 9 / 32 := by
    intro a b c h
    rcases h with ⟨ha, hb, hc, ha', hb', hc', hsum⟩
    have h₁ : c = 1 - a - b := by linarith
    rw [h₁] at *
    have h₂ : 0 ≤ a := by linarith
    have h₃ : 0 ≤ b := by linarith
    have h₄ : 0 ≤ 1 - a - b := by linarith
    have h₅ : a ≤ 1 / 2 := by linarith
    have h₆ : b ≤ 1 / 2 := by linarith
    have h₇ : 1 - a - b ≤ 1 / 2 := by linarith
    nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (a - b),
      mul_nonneg h₂ h₃, mul_nonneg h₂ h₄, mul_nonneg h₃ h₄,
      mul_nonneg (sub_nonneg.mpr h₅) (sub_nonneg.mpr h₆),
      mul_nonneg (sub_nonneg.mpr h₅) (sub_nonneg.mpr h₇),
      mul_nonneg (sub_nonneg.mpr h₆) (sub_nonneg.mpr h₇),
      mul_nonneg (sub_nonneg.mpr h₅) (sub_nonneg.mpr h₆),
      mul_nonneg (sub_nonneg.mpr h₅) (sub_nonneg.mpr h₇),
      mul_nonneg (sub_nonneg.mpr h₆) (sub_nonneg.mpr h₇)]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_30 : ∀ (a b c : ℝ), a * b * c = -1 → a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) ≥ a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b := by
  intro a b c h
  have h₁ : a ≠ 0 := by
    by_contra h₁
    rw [h₁] at h
    norm_num at h ⊢
    <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { nlinarith })
    <;>
    (try { nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg (b + c), sq_nonneg (b - c)] })
  
  have h₂ : b ≠ 0 := by
    by_contra h₂
    rw [h₂] at h
    norm_num at h ⊢
    <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { nlinarith })
    <;>
    (try { nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg (a + c), sq_nonneg (a - c)] })
  
  have h₃ : c ≠ 0 := by
    by_contra h₃
    rw [h₃] at h
    norm_num at h ⊢
    <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { nlinarith })
    <;>
    (try { nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a + b), sq_nonneg (a - b)] })
  
  have h₄ : a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b = - (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3) := by
    have h₄₁ : a ^ 2 / b = -a ^ 3 * c := by
      have h₄₂ : b = -1 / (a * c) := by
        have h₄₃ : a * b * c = -1 := h
        have h₄₄ : a ≠ 0 := h₁
        have h₄₅ : c ≠ 0 := h₃
        have h₄₆ : b = -1 / (a * c) := by
          have h₄₇ : a * b * c = -1 := h
          have h₄₈ : a * c ≠ 0 := by
            intro h₄₈
            have h₄₉ : a = 0 ∨ c = 0 := by
              simp [mul_eq_mul_left_iff, h₄₄, h₄₅] at h₄₈ ⊢
              <;> aesop
            cases h₄₉ with
            | inl h₄₉ =>
              contradiction
            | inr h₄₉ =>
              contradiction
          field_simp at h₄₇ ⊢
          nlinarith
        exact h₄₆
      have h₄₉ : a ≠ 0 := h₁
      have h₄₁₀ : c ≠ 0 := h₃
      calc
        a ^ 2 / b = a ^ 2 / (-1 / (a * c)) := by rw [h₄₂]
        _ = -a ^ 3 * c := by
          field_simp [h₄₉, h₄₁₀]
          <;> ring
          <;> field_simp [h₄₉, h₄₁₀]
          <;> nlinarith
    have h₄₂ : a ^ 2 / c = -a ^ 3 * b := by
      have h₄₃ : c = -1 / (a * b) := by
        have h₄₄ : a * b * c = -1 := h
        have h₄₅ : a ≠ 0 := h₁
        have h₄₆ : b ≠ 0 := h₂
        have h₄₇ : c = -1 / (a * b) := by
          have h₄₈ : a * b * c = -1 := h
          have h₄₉ : a * b ≠ 0 := by
            intro h₄₉
            have h₅₀ : a = 0 ∨ b = 0 := by
              simp [mul_eq_mul_left_iff, h₄₅, h₄₆] at h₄₉ ⊢
              <;> aesop
            cases h₅₀ with
            | inl h₅₀ =>
              contradiction
            | inr h₅₀ =>
              contradiction
          field_simp at h₄₈ ⊢
          nlinarith
        exact h₄₇
      have h₄₈ : a ≠ 0 := h₁
      have h₄₉ : b ≠ 0 := h₂
      calc
        a ^ 2 / c = a ^ 2 / (-1 / (a * b)) := by rw [h₄₃]
        _ = -a ^ 3 * b := by
          field_simp [h₄₈, h₄₉]
          <;> ring
          <;> field_simp [h₄₈, h₄₉]
          <;> nlinarith
    have h₄₃ : b ^ 2 / c = -a * b ^ 3 := by
      have h₄₄ : c = -1 / (a * b) := by
        have h₄₅ : a * b * c = -1 := h
        have h₄₆ : a ≠ 0 := h₁
        have h₄₇ : b ≠ 0 := h₂
        have h₄₈ : c = -1 / (a * b) := by
          have h₄₉ : a * b * c = -1 := h
          have h₅₀ : a * b ≠ 0 := by
            intro h₅₀
            have h₅₁ : a = 0 ∨ b = 0 := by
              simp [mul_eq_mul_left_iff, h₄₆, h₄₇] at h₅₀ ⊢
              <;> aesop
            cases h₅₁ with
            | inl h₅₁ =>
              contradiction
            | inr h₅₁ =>
              contradiction
          field_simp at h₄₉ ⊢
          nlinarith
        exact h₄₈
      have h₄₉ : a ≠ 0 := h₁
      have h₅₀ : b ≠ 0 := h₂
      calc
        b ^ 2 / c = b ^ 2 / (-1 / (a * b)) := by rw [h₄₄]
        _ = -a * b ^ 3 := by
          field_simp [h₄₉, h₅₀]
          <;> ring
          <;> field_simp [h₄₉, h₅₀]
          <;> nlinarith
    have h₄₄ : b ^ 2 / a = -b ^ 3 * c := by
      have h₄₅ : a = -1 / (b * c) := by
        have h₄₆ : a * b * c = -1 := h
        have h₄₇ : b ≠ 0 := h₂
        have h₄₈ : c ≠ 0 := h₃
        have h₄₉ : a = -1 / (b * c) := by
          have h₅₀ : a * b * c = -1 := h
          have h₅₁ : b * c ≠ 0 := by
            intro h₅₁
            have h₅₂ : b = 0 ∨ c = 0 := by
              simp [mul_eq_mul_left_iff, h₄₇, h₄₈] at h₅₁ ⊢
              <;> aesop
            cases h₅₂ with
            | inl h₅₂ =>
              contradiction
            | inr h₅₂ =>
              contradiction
          field_simp at h₅₀ ⊢
          nlinarith
        exact h₄₉
      have h₄₆ : b ≠ 0 := h₂
      have h₄₇ : c ≠ 0 := h₃
      calc
        b ^ 2 / a = b ^ 2 / (-1 / (b * c)) := by rw [h₄₅]
        _ = -b ^ 3 * c := by
          field_simp [h₄₆, h₄₇]
          <;> ring
          <;> field_simp [h₄₆, h₄₇]
          <;> nlinarith
    have h₄₅ : c ^ 2 / a = -b * c ^ 3 := by
      have h₄₆ : a = -1 / (b * c) := by
        have h₄₇ : a * b * c = -1 := h
        have h₄₈ : b ≠ 0 := h₂
        have h₄₉ : c ≠ 0 := h₃
        have h₅₀ : a = -1 / (b * c) := by
          have h₅₁ : a * b * c = -1 := h
          have h₅₂ : b * c ≠ 0 := by
            intro h₅₂
            have h₅₃ : b = 0 ∨ c = 0 := by
              simp [mul_eq_mul_left_iff, h₄₈, h₄₉] at h₅₂ ⊢
              <;> aesop
            cases h₅₃ with
            | inl h₅₃ =>
              contradiction
            | inr h₅₃ =>
              contradiction
          field_simp at h₅₁ ⊢
          nlinarith
        exact h₅₀
      have h₄₇ : b ≠ 0 := h₂
      have h₄₈ : c ≠ 0 := h₃
      calc
        c ^ 2 / a = c ^ 2 / (-1 / (b * c)) := by rw [h₄₆]
        _ = -b * c ^ 3 := by
          field_simp [h₄₇, h₄₈]
          <;> ring
          <;> field_simp [h₄₇, h₄₈]
          <;> nlinarith
    have h₄₆ : c ^ 2 / b = -a * c ^ 3 := by
      have h₄₇ : b = -1 / (a * c) := by
        have h₄₈ : a * b * c = -1 := h
        have h₄₉ : a ≠ 0 := h₁
        have h₅₀ : c ≠ 0 := h₃
        have h₅₁ : b = -1 / (a * c) := by
          have h₅₂ : a * b * c = -1 := h
          have h₅₃ : a * c ≠ 0 := by
            intro h₅₃
            have h₅₄ : a = 0 ∨ c = 0 := by
              simp [mul_eq_mul_left_iff, h₄₉, h₅₀] at h₅₃ ⊢
              <;> aesop
            cases h₅₄ with
            | inl h₅₄ =>
              contradiction
            | inr h₅₄ =>
              contradiction
          field_simp at h₅₂ ⊢
          nlinarith
        exact h₅₁
      have h₄₈ : a ≠ 0 := h₁
      have h₄₉ : c ≠ 0 := h₃
      calc
        c ^ 2 / b = c ^ 2 / (-1 / (a * c)) := by rw [h₄₇]
        _ = -a * c ^ 3 := by
          field_simp [h₄₈, h₄₉]
          <;> ring
          <;> field_simp [h₄₈, h₄₉]
          <;> nlinarith
    calc
      a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b = (-a ^ 3 * c) + (-a ^ 3 * b) + (-a * b ^ 3) + (-b ^ 3 * c) + (-b * c ^ 3) + (-a * c ^ 3) := by
        rw [h₄₁, h₄₂, h₄₃, h₄₄, h₄₅, h₄₆]
        <;> ring
      _ = - (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3) := by
        ring
      _ = - (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3) := by rfl
  
  have h₅ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) - (- (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3)) = (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + 3) := by
    ring_nf at *
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try nlinarith) <;>
    (try field_simp at *) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])
    <;>
    (try ring_nf)
    <;>
    (try nlinarith)
    <;>
    (try field_simp at *)
    <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])
  
  have h₆ : a ^ 3 + b ^ 3 + c ^ 3 + 3 = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
    have h₆₁ : a ^ 3 + b ^ 3 + c ^ 3 + 3 = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
      have h₆₂ : a ^ 3 + b ^ 3 + c ^ 3 + 3 = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]
      linarith
    linarith
  
  have h₇ : (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + 3) = (a + b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
    rw [h₆]
    <;> ring
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try nlinarith) <;>
    (try field_simp at *) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])
    <;>
    (try ring_nf)
    <;>
    (try nlinarith)
    <;>
    (try field_simp at *)
    <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])
  
  have h₈ : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ 0 := by
    have h₈₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₉ : (a + b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) ≥ 0 := by
    have h₉₁ : (a + b + c) ^ 2 ≥ 0 := by nlinarith
    have h₉₂ : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ 0 := by nlinarith
    nlinarith
  
  have h₁₀ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) ≥ a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b := by
    have h₁₀₁ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) - (- (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3)) ≥ 0 := by
      linarith
    have h₁₀₂ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) ≥ - (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3) := by linarith
    have h₁₀₃ : a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b = - (a ^ 3 * b + a ^ 3 * c + a * b ^ 3 + b ^ 3 * c + a * c ^ 3 + b * c ^ 3) := by
      rw [h₄]
    linarith
  
  exact h₁₀

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_33 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a * b + b * c + c * a) * (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2) ≥ 9 / 4 := by
  intro a b c h
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
  have h₁₁ : 0 < a * b * c * a * b := by positivity
  have h₁₂ : 0 < a * b * c * b * c := by positivity
  have h₁₃ : 0 < a * b * c * c * a := by positivity
  -- Use the known inequality to prove the statement
  have h₁₄ : (a * b + b * c + c * a) * (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2) ≥ 9 / 4 := by
    have h₁₅ : 0 < a * b + b * c + c * a := by positivity
    have h₁₆ : 0 < a + b := by linarith
    have h₁₇ : 0 < b + c := by linarith
    have h₁₈ : 0 < c + a := by linarith
    -- Use the known inequality to prove the statement
    field_simp [h₁₆.ne', h₁₇.ne', h₁₈.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    -- Use nlinarith to prove the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₄.le (sq_nonneg (a - b)), mul_nonneg h₅.le (sq_nonneg (b - c)),
      mul_nonneg h₆.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (c + a - b))]
  exact h₁₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_34 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) + (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) ≥ 3 / 5 := by
  have h_main : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) + (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) ≥ 3 / 5 := by
    intro a b c ⟨ha, hb, hc⟩
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a^2 * b - b^2 * a), sq_nonneg (b^2 * c - c^2 * b), sq_nonneg (c^2 * a - a^2 * c),
      sq_nonneg (a^2 * b - a^2 * c), sq_nonneg (b^2 * a - b^2 * c), sq_nonneg (c^2 * a - c^2 * b),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)), mul_nonneg h₃.le (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (c - a)),
      mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (a - b)),
      mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc),
      mul_pos (sub_pos.mpr hc) (sub_pos.mpr ha),
      mul_pos (mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)) (mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc)),
      mul_pos (mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc)) (mul_pos (sub_pos.mpr hc) (sub_pos.mpr ha)),
      mul_pos (mul_pos (sub_pos.mpr hc) (sub_pos.mpr ha)) (mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb))]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_35 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (2 * a / (b + c)) ^ (2 / 3) + (2 * b / (c + a)) ^ (2 / 3) + (2 * c / (a + b)) ^ (2 / 3) ≥ 3 := by
  intro a b c h
  have h_main : (2 * a / (b + c)) ^ (2 / 3) + (2 * b / (c + a)) ^ (2 / 3) + (2 * c / (a + b)) ^ (2 / 3) ≥ 3 := by
    norm_num [h.1, h.2.1, h.2.2, pow_two]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith [h.1, h.2.1, h.2.2]
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_37 : ∀ (a b c : ℝ), (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) := by
  intro a b c
  have h_main : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) = (1 / 2 : ℝ) * ((a ^ 2 - 2 * a * b + b * c + c * a - c ^ 2) ^ 2 + (b ^ 2 - 2 * b * c + c * a + a * b - a ^ 2) ^ 2 + (c ^ 2 - 2 * c * a + a * b + b * c - b ^ 2) ^ 2) := by
    ring_nf
    <;>
    (try ring_nf)
    <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)])
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)])
  
  have h_final : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) := by
    have h1 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) = (1 / 2 : ℝ) * ((a ^ 2 - 2 * a * b + b * c + c * a - c ^ 2) ^ 2 + (b ^ 2 - 2 * b * c + c * a + a * b - a ^ 2) ^ 2 + (c ^ 2 - 2 * c * a + a * b + b * c - b ^ 2) ^ 2) := h_main
    have h2 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) ≥ 0 := by
      rw [h1]
      have h3 : (a ^ 2 - 2 * a * b + b * c + c * a - c ^ 2) ^ 2 + (b ^ 2 - 2 * b * c + c * a + a * b - a ^ 2) ^ 2 + (c ^ 2 - 2 * c * a + a * b + b * c - b ^ 2) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (a ^ 2 - 2 * a * b + b * c + c * a - c ^ 2), sq_nonneg (b ^ 2 - 2 * b * c + c * a + a * b - a ^ 2), sq_nonneg (c ^ 2 - 2 * c * a + a * b + b * c - b ^ 2)]
      have h4 : (1 / 2 : ℝ) * ((a ^ 2 - 2 * a * b + b * c + c * a - c ^ 2) ^ 2 + (b ^ 2 - 2 * b * c + c * a + a * b - a ^ 2) ^ 2 + (c ^ 2 - 2 * c * a + a * b + b * c - b ^ 2) ^ 2) ≥ 0 := by
        nlinarith
      nlinarith
    nlinarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_15 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h_main : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < a * c := by positivity
    have h₇ : 0 < a * b * c := by positivity
    -- Prove the key inequality: a^3 + b^3 + abc ≥ ab(a + b + c)
    have h₈ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₁ h₃,
        mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₂), mul_pos (sq_pos_of_pos h₂) (sq_pos_of_pos h₃),
        mul_pos (sq_pos_of_pos h₁) (sq_pos_of_pos h₃)]
    have h₉ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have h₁₀ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      have h₁₀₁ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c), mul_pos h₂ h₃, mul_pos h₁ h₃,
          mul_pos h₁ h₂]
      have h₁₀₂ : 0 < b * c * (a + b + c) := by positivity
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    have h₁₁ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
      have h₁₁₁ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
        nlinarith [sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (b - c), mul_pos h₃ h₁, mul_pos h₂ h₁,
          mul_pos h₂ h₃]
      have h₁₁₂ : 0 < c * a * (a + b + c) := by positivity
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    -- Sum the inequalities
    have h₁₂ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
      field_simp [h₁.ne', h₂.ne', h₃.ne']
      <;> ring
      <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
      <;> ring
    have h₁₃ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
      linarith [h₉, h₁₀, h₁₁]
    have h₁₄ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
      linarith
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_24_left : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 < a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) := by
  intro a b c h
  have h₁ : Real.sqrt (a ^ 2 + b ^ 2) < a + b := by
    have h₁₁ : 0 < a + b := by linarith
    have h₁₂ : 0 < a * b := by nlinarith
    have h₁₃ : 0 < a ^ 2 + b ^ 2 := by nlinarith
    have h₁₄ : Real.sqrt (a ^ 2 + b ^ 2) < a + b := by
      rw [Real.sqrt_lt (by positivity) (by positivity)]
      nlinarith [sq_nonneg (a - b)]
    exact h₁₄
  
  have h₂ : a / Real.sqrt (a ^ 2 + b ^ 2) > a / (a + b) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < a + b := by linarith
    have h₂₄ : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have h₂₅ : 0 < a / Real.sqrt (a ^ 2 + b ^ 2) := div_pos h₂₁ h₂₄
    have h₂₆ : 0 < a / (a + b) := div_pos h₂₁ h₂₃
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₂₇ : Real.sqrt (a ^ 2 + b ^ 2) < a + b := h₁
    have h₂₈ : 0 < a + b := by linarith
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₂₉ : 0 < a + b := by linarith
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₃₀ : a / Real.sqrt (a ^ 2 + b ^ 2) > a / (a + b) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by nlinarith), h₂₇]
    exact h₃₀
  
  have h₃ : Real.sqrt (b ^ 2 + c ^ 2) < b + c := by
    have h₃₁ : 0 < b + c := by linarith
    have h₃₂ : 0 < b * c := by nlinarith
    have h₃₃ : 0 < b ^ 2 + c ^ 2 := by nlinarith
    have h₃₄ : Real.sqrt (b ^ 2 + c ^ 2) < b + c := by
      rw [Real.sqrt_lt (by positivity) (by positivity)]
      nlinarith [sq_nonneg (b - c)]
    exact h₃₄
  
  have h₄ : b / Real.sqrt (b ^ 2 + c ^ 2) > b / (b + c) := by
    have h₄₁ : 0 < b := by linarith
    have h₄₂ : 0 < c := by linarith
    have h₄₃ : 0 < b + c := by linarith
    have h₄₄ : 0 < Real.sqrt (b ^ 2 + c ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have h₄₅ : 0 < b / Real.sqrt (b ^ 2 + c ^ 2) := div_pos h₄₁ h₄₄
    have h₄₆ : 0 < b / (b + c) := div_pos h₄₁ h₄₃
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₄₇ : Real.sqrt (b ^ 2 + c ^ 2) < b + c := h₃
    have h₄₈ : 0 < b + c := by linarith
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₄₉ : 0 < b + c := by linarith
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₅₀ : b / Real.sqrt (b ^ 2 + c ^ 2) > b / (b + c) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [Real.sq_sqrt (show 0 ≤ b ^ 2 + c ^ 2 by nlinarith), h₄₇]
    exact h₅₀
  
  have h₅ : Real.sqrt (c ^ 2 + a ^ 2) < c + a := by
    have h₅₁ : 0 < c + a := by linarith
    have h₅₂ : 0 < c * a := by nlinarith
    have h₅₃ : 0 < c ^ 2 + a ^ 2 := by nlinarith
    have h₅₄ : Real.sqrt (c ^ 2 + a ^ 2) < c + a := by
      rw [Real.sqrt_lt (by positivity) (by positivity)]
      nlinarith [sq_nonneg (c - a)]
    exact h₅₄
  
  have h₆ : c / Real.sqrt (c ^ 2 + a ^ 2) > c / (c + a) := by
    have h₆₁ : 0 < c := by linarith
    have h₆₂ : 0 < a := by linarith
    have h₆₃ : 0 < c + a := by linarith
    have h₆₄ : 0 < Real.sqrt (c ^ 2 + a ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have h₆₅ : 0 < c / Real.sqrt (c ^ 2 + a ^ 2) := div_pos h₆₁ h₆₄
    have h₆₆ : 0 < c / (c + a) := div_pos h₆₁ h₆₃
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₆₇ : Real.sqrt (c ^ 2 + a ^ 2) < c + a := h₅
    have h₆₈ : 0 < c + a := by linarith
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₆₉ : 0 < c + a := by linarith
    -- Use the fact that the reciprocal function is decreasing to compare the two fractions
    have h₇₀ : c / Real.sqrt (c ^ 2 + a ^ 2) > c / (c + a) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith [Real.sq_sqrt (show 0 ≤ c ^ 2 + a ^ 2 by nlinarith), h₆₇]
    exact h₇₀
  
  have h₇ : a / (a + b) + b / (b + c) + c / (c + a) > 1 := by
    have h₇₁ : 0 < a := by linarith
    have h₇₂ : 0 < b := by linarith
    have h₇₃ : 0 < c := by linarith
    have h₇₄ : 0 < a + b := by linarith
    have h₇₅ : 0 < b + c := by linarith
    have h₇₆ : 0 < c + a := by linarith
    have h₇₇ : 0 < a + b + c := by linarith
    have h₇₈ : a / (a + b) > a / (a + b + c) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h₇₉ : b / (b + c) > b / (a + b + c) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h₈₀ : c / (c + a) > c / (a + b + c) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h₈₁ : a / (a + b) + b / (b + c) + c / (c + a) > a / (a + b + c) + b / (a + b + c) + c / (a + b + c) := by
      linarith
    have h₈₂ : a / (a + b + c) + b / (a + b + c) + c / (a + b + c) = 1 := by
      field_simp [h₇₇.ne']
      <;> ring
      <;> field_simp [h₇₇.ne']
      <;> ring
    linarith
  
  have h₈ : a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) > 1 := by
    have h₈₁ : a / Real.sqrt (a ^ 2 + b ^ 2) > a / (a + b) := h₂
    have h₈₂ : b / Real.sqrt (b ^ 2 + c ^ 2) > b / (b + c) := h₄
    have h₈₃ : c / Real.sqrt (c ^ 2 + a ^ 2) > c / (c + a) := h₆
    have h₈₄ : a / (a + b) + b / (b + c) + c / (c + a) > 1 := h₇
    calc
      a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) > a / (a + b) + b / (b + c) + c / (c + a) := by
        linarith
      _ > 1 := by linarith
  
  have h₉ : 1 < a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) := by
    linarith
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_27 : ∀ (a b c x y z : ℝ), a ≥ b ∧ b ≥ c ∧ x + z ≥ y ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) ≥ 0 := by
  intro a b c x y z h
  have h₁ : a - b ≥ 0 := by linarith
  have h₂ : b - c ≥ 0 := by linarith
  have h₃ : a - c ≥ 0 := by linarith
  have h₄ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) = (a - b) ^ 2 * x ^ 2 + (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) + (b - c) ^ 2 * z ^ 2 := by
    have h₄₁ : b - a = -(a - b) := by ring
    have h₄₂ : c - a = -(a - c) := by ring
    have h₄₃ : c - b = -(b - c) := by ring
    have h₄₄ : y ^ 2 * (b - c) * (b - a) = - (a - b) * (b - c) * y ^ 2 := by
      rw [h₄₁]
      <;> ring
      <;> nlinarith
    have h₄₅ : z ^ 2 * (c - a) * (c - b) = (a - c) * (b - c) * z ^ 2 := by
      rw [h₄₂, h₄₃]
      <;> ring
      <;> nlinarith
    have h₄₆ : x ^ 2 * (a - b) * (a - c) = (a - b) * (a - c) * x ^ 2 := by ring
    have h₄₇ : (a - c) = (a - b) + (b - c) := by ring
    calc
      x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) = (a - b) * (a - c) * x ^ 2 + (- (a - b) * (b - c) * y ^ 2) + (a - c) * (b - c) * z ^ 2 := by
        rw [h₄₄, h₄₅, h₄₆]
        <;> ring
        <;> nlinarith
      _ = (a - b) * (a - c) * x ^ 2 - (a - b) * (b - c) * y ^ 2 + (a - c) * (b - c) * z ^ 2 := by ring
      _ = (a - b) * (a - c) * x ^ 2 - (a - b) * (b - c) * y ^ 2 + (a - c) * (b - c) * z ^ 2 := by ring
      _ = (a - b) ^ 2 * x ^ 2 + (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) + (b - c) ^ 2 * z ^ 2 := by
        have h₄₈ : a - c = (a - b) + (b - c) := by ring
        rw [h₄₈]
        ring_nf
        <;> nlinarith
      _ = (a - b) ^ 2 * x ^ 2 + (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) + (b - c) ^ 2 * z ^ 2 := by ring
  have h₅ : x ^ 2 + z ^ 2 - y ^ 2 ≥ -2 * x * z := by
    have h₅₁ : x + z ≥ y := by linarith
    have h₅₂ : y ^ 2 ≤ (x + z) ^ 2 := by
      nlinarith [sq_nonneg (x + z), sq_nonneg (x - z), h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
    have h₅₃ : x ^ 2 + z ^ 2 - y ^ 2 ≥ -2 * x * z := by
      nlinarith [sq_nonneg (x + z), sq_nonneg (x - z), h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
    exact h₅₃
  have h₆ : (a - b) * (b - c) ≥ 0 := by
    nlinarith
  have h₇ : (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) ≥ (a - b) * (b - c) * (-2 * x * z) := by
    have h₇₁ : (a - b) * (b - c) ≥ 0 := by nlinarith
    have h₇₂ : x ^ 2 + z ^ 2 - y ^ 2 ≥ -2 * x * z := by nlinarith
    have h₇₃ : (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) ≥ (a - b) * (b - c) * (-2 * x * z) := by
      have h₇₄ : x ^ 2 + z ^ 2 - y ^ 2 ≥ -2 * x * z := h₅
      have h₇₅ : (a - b) * (b - c) ≥ 0 := h₆
      nlinarith [mul_nonneg h₇₅ (sq_nonneg (x + z))]
    exact h₇₃
  have h₈ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) ≥ (a - b) ^ 2 * x ^ 2 - 2 * (a - b) * (b - c) * x * z + (b - c) ^ 2 * z ^ 2 := by
    have h₈₁ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) = (a - b) ^ 2 * x ^ 2 + (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) + (b - c) ^ 2 * z ^ 2 := by
      rw [h₄]
    rw [h₈₁]
    have h₈₂ : (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) ≥ (a - b) * (b - c) * (-2 * x * z) := h₇
    have h₈₃ : (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) + (b - c) ^ 2 * z ^ 2 ≥ (a - b) * (b - c) * (-2 * x * z) + (b - c) ^ 2 * z ^ 2 := by
      nlinarith
    have h₈₄ : (a - b) ^ 2 * x ^ 2 + (a - b) * (b - c) * (x ^ 2 + z ^ 2 - y ^ 2) + (b - c) ^ 2 * z ^ 2 ≥ (a - b) ^ 2 * x ^ 2 + ((a - b) * (b - c) * (-2 * x * z) + (b - c) ^ 2 * z ^ 2) := by
      nlinarith
    have h₈₅ : (a - b) ^ 2 * x ^ 2 + ((a - b) * (b - c) * (-2 * x * z) + (b - c) ^ 2 * z ^ 2) = (a - b) ^ 2 * x ^ 2 - 2 * (a - b) * (b - c) * x * z + (b - c) ^ 2 * z ^ 2 := by
      ring_nf
      <;> nlinarith
    nlinarith
  have h₉ : (a - b) ^ 2 * x ^ 2 - 2 * (a - b) * (b - c) * x * z + (b - c) ^ 2 * z ^ 2 = ((a - b) * x - (b - c) * z) ^ 2 := by
    have h₉₁ : ((a - b) * x - (b - c) * z) ^ 2 = (a - b) ^ 2 * x ^ 2 - 2 * (a - b) * (b - c) * x * z + (b - c) ^ 2 * z ^ 2 := by
      ring_nf
      <;> nlinarith
    linarith
  have h₁₀ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) ≥ ((a - b) * x - (b - c) * z) ^ 2 := by
    have h₁₀₁ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) ≥ (a - b) ^ 2 * x ^ 2 - 2 * (a - b) * (b - c) * x * z + (b - c) ^ 2 * z ^ 2 := h₈
    have h₁₀₂ : (a - b) ^ 2 * x ^ 2 - 2 * (a - b) * (b - c) * x * z + (b - c) ^ 2 * z ^ 2 = ((a - b) * x - (b - c) * z) ^ 2 := h₉
    linarith
  have h₁₁ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) ≥ 0 := by
    have h₁₁₁ : x ^ 2 * (a - b) * (a - c) + y ^ 2 * (b - c) * (b - a) + z ^ 2 * (c - a) * (c - b) ≥ ((a - b) * x - (b - c) * z) ^ 2 := h₁₀
    have h₁₁₂ : ((a - b) * x - (b - c) * z) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg ((a - b) * x - (b - c) * z)]
    linarith
  exact h₁₁
