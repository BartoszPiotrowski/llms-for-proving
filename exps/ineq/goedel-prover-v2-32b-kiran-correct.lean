
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_example_11 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  intro a b c h
  have h₁ : ∀ (x y : ℝ), x > 0 → y > 0 → x ^ 3 + y ^ 3 ≥ x ^ 2 * y + x * y ^ 2 := by
    intro x y hx hy
    have h₂ : 0 ≤ (x - y) ^ 2 := by nlinarith
    have h₃ : 0 < x + y := by nlinarith
    nlinarith [sq_nonneg (x - y), mul_nonneg hx.le hy.le, mul_nonneg hx.le (sq_nonneg (x - y)),
      mul_nonneg hy.le (sq_nonneg (x - y))]
  
  have h₂ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by
    have h₃ : a > 0 := h.1
    have h₄ : b > 0 := h.2.1
    have h₅ : c > 0 := h.2.2
    have h₆ : a ^ 3 + b ^ 3 ≥ a ^ 2 * b + a * b ^ 2 := h₁ a b h₃ h₄
    have h₇ : a * b * (a + b + c) = a ^ 2 * b + a * b ^ 2 + a * b * c := by
      ring
    nlinarith [h₆]
  
  have h₃ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by
    have h₄ : b > 0 := h.2.1
    have h₅ : c > 0 := h.2.2
    have h₆ : a > 0 := h.1
    have h₇ : b ^ 3 + c ^ 3 ≥ b ^ 2 * c + b * c ^ 2 := h₁ b c h₄ h₅
    have h₈ : b * c * (a + b + c) = b ^ 2 * c + b * c ^ 2 + a * b * c := by
      ring
    nlinarith [h₇]
  
  have h₄ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by
    have h₅ : a > 0 := h.1
    have h₆ : b > 0 := h.2.1
    have h₇ : c > 0 := h.2.2
    have h₈ : c ^ 3 + a ^ 3 ≥ c ^ 2 * a + c * a ^ 2 := h₁ c a h₇ h₅
    have h₉ : c * a * (a + b + c) = c ^ 2 * a + c * a ^ 2 + a * b * c := by
      ring
    nlinarith [h₈]
  
  have h₅ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₅₁ : a > 0 := h.1
    have h₅₂ : b > 0 := h.2.1
    have h₅₃ : c > 0 := h.2.2
    have h₅₄ : a * b > 0 := by positivity
    have h₅₅ : a + b + c > 0 := by positivity
    have h₅₆ : a * b * (a + b + c) > 0 := by positivity
    have h₅₇ : a ^ 3 + b ^ 3 + a * b * c > 0 := by positivity
    have h₅₈ : a * b * (a + b + c) ≤ a ^ 3 + b ^ 3 + a * b * c := by
      linarith [h₂]
    have h₅₉ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₅₉
  
  have h₆ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₆₁ : b > 0 := h.2.1
    have h₆₂ : c > 0 := h.2.2
    have h₆₃ : a > 0 := h.1
    have h₆₄ : b * c > 0 := by positivity
    have h₆₅ : a + b + c > 0 := by positivity
    have h₆₆ : b * c * (a + b + c) > 0 := by positivity
    have h₆₇ : b ^ 3 + c ^ 3 + a * b * c > 0 := by positivity
    have h₆₈ : b * c * (a + b + c) ≤ b ^ 3 + c ^ 3 + a * b * c := by linarith [h₃]
    have h₆₉ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₆₉
  
  have h₇ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    have h₇₁ : a > 0 := h.1
    have h₇₂ : b > 0 := h.2.1
    have h₇₃ : c > 0 := h.2.2
    have h₇₄ : c * a > 0 := by positivity
    have h₇₅ : a + b + c > 0 := by positivity
    have h₇₆ : c * a * (a + b + c) > 0 := by positivity
    have h₇₇ : c ^ 3 + a ^ 3 + a * b * c > 0 := by positivity
    have h₇₈ : c * a * (a + b + c) ≤ c ^ 3 + a ^ 3 + a * b * c := by linarith [h₄]
    have h₇₉ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₇₉
  
  have h₈ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    have h₈₁ : a > 0 := h.1
    have h₈₂ : b > 0 := h.2.1
    have h₈₃ : c > 0 := h.2.2
    have h₈₄ : a * b > 0 := by positivity
    have h₈₅ : a * c > 0 := by positivity
    have h₈₆ : b * c > 0 := by positivity
    have h₈₇ : a * b * c > 0 := by positivity
    have h₈₈ : a + b + c > 0 := by positivity
    have h₈₉ : a * b * (a + b + c) > 0 := by positivity
    have h₉₀ : b * c * (a + b + c) > 0 := by positivity
    have h₉₁ : c * a * (a + b + c) > 0 := by positivity
    -- Simplify the sum of fractions by finding a common denominator
    have h₉₂ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = (1 / (a + b + c)) * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
      calc
        1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = (1 / (a * b * (a + b + c))) + (1 / (b * c * (a + b + c))) + (1 / (c * a * (a + b + c))) := by rfl
        _ = (1 / (a + b + c)) * (1 / (a * b)) + (1 / (a + b + c)) * (1 / (b * c)) + (1 / (a + b + c)) * (1 / (c * a)) := by
          field_simp [h₈₄, h₈₅, h₈₆, h₈₈]
          <;> ring_nf
          <;> field_simp [h₈₄, h₈₅, h₈₆, h₈₈]
          <;> ring_nf
        _ = (1 / (a + b + c)) * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by ring
    rw [h₉₂]
    -- Simplify the expression using the fact that 1/(a+b+c) * (1/(ab) + 1/(bc) + 1/(ca)) = 1/(abc)
    have h₉₃ : 1 / (a + b + c) * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) = 1 / (a * b * c) := by
      have h₉₄ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) = (a + b + c) / (a * b * c) := by
        field_simp [h₈₄, h₈₅, h₈₆, h₈₇]
        <;> ring_nf
        <;> field_simp [h₈₄, h₈₅, h₈₆, h₈₇]
        <;> ring_nf
      rw [h₉₄]
      field_simp [h₈₈, h₈₇]
      <;> ring_nf
      <;> field_simp [h₈₈, h₈₇]
      <;> ring_nf
    rw [h₉₃]
    <;> simp_all
  
  have h₉ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    have h₉₁ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
      linarith [h₅, h₆, h₇]
    have h₉₂ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
      exact h₈
    linarith
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_example_13 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ 3 / 5 := by
  have h_main : ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) ≥ 3 / 5 := by
    intro a b c ha hb hc
    have h₁ : 0 < a * b := mul_pos ha hb
    have h₂ : 0 < b * c := mul_pos hb hc
    have h₃ : 0 < c * a := mul_pos hc ha
    field_simp [add_assoc]
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₁.le (sq_nonneg (a - b)), mul_nonneg h₂.le (sq_nonneg (b - c)),
      mul_nonneg h₃.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (c + a - b)),
      mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb), mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hc),
      mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos ha)]
  intro a b c h
  have h₁ : a > 0 := h.1
  have h₂ : b > 0 := h.2.1
  have h₃ : c > 0 := h.2.2
  exact h_main a b c h₁ h₂ h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_2_1 : ∀ (x y z : ℝ), x ≤ y ∧ y ≤ z ∧ z ≤ x → x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) ≥ 0 := by
  intro x y z h
  have h₁ : x = y := by
    have h₂ : x ≤ y := h.1
    have h₃ : y ≤ z := h.2.1
    have h₄ : z ≤ x := h.2.2
    have h₅ : y ≤ x := by
      linarith
    -- Since x ≤ y and y ≤ x, it follows that x = y.
    linarith
  
  have h₂ : y = z := by
    have h₃ : y ≤ z := h.2.1
    have h₄ : z ≤ x := h.2.2
    have h₅ : x ≤ y := h.1
    have h₆ : x = y := h₁
    have h₇ : z ≤ y := by
      linarith
    -- Since y ≤ z and z ≤ y, it follows that y = z.
    linarith
  
  have h₃ : x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) = 0 := by
    have h₄ : x = y := h₁
    have h₅ : y = z := h₂
    have h₆ : x = z := by linarith
    have h₇ : x - y = 0 := by linarith
    have h₈ : y - z = 0 := by linarith
    have h₉ : z - x = 0 := by linarith
    have h₁₀ : x ^ 1 * (x - y) * (x - z) = 0 := by
      calc
        x ^ 1 * (x - y) * (x - z) = x * (x - y) * (x - z) := by norm_num
        _ = x * 0 * (x - z) := by rw [h₇]
        _ = 0 := by ring
    have h₁₁ : y ^ 1 * (y - z) * (y - x) = 0 := by
      calc
        y ^ 1 * (y - z) * (y - x) = y * (y - z) * (y - x) := by norm_num
        _ = y * 0 * (y - x) := by rw [h₈]
        _ = 0 := by ring
    have h₁₂ : z ^ 1 * (z - x) * (z - y) = 0 := by
      calc
        z ^ 1 * (z - x) * (z - y) = z * (z - x) * (z - y) := by norm_num
        _ = z * 0 * (z - y) := by rw [h₉]
        _ = 0 := by ring
    calc
      x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) = 0 + 0 + 0 := by
        rw [h₁₀, h₁₁, h₁₂]
        <;> norm_num
      _ = 0 := by norm_num
  
  have h₄ : x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) ≥ 0 := by
    have h₅ : x ^ 1 * (x - y) * (x - z) + y ^ 1 * (y - z) * (y - x) + z ^ 1 * (z - x) * (z - y) = 0 := h₃
    rw [h₅]
    <;> norm_num
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_2_5 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 → x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) ≤ 9 / (4 * (x + y + z)) := by
  intro x y z h
  have h₁ : 0 < x := by
    linarith

  have h₂ : 0 < y := by
    linarith

  have h₃ : 0 < z := by
    linarith

  have h₄ : 0 < x * y := by
    positivity

  have h₅ : 0 < x * z := by
    positivity

  have h₆ : 0 < y * z := by
    positivity

  have h₇ : (x + y + z) * (x * y + y * z + z * x) - 9 * x * y * z = x * (y - z)^2 + y * (z - x)^2 + z * (x - y)^2 := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try ring_nf at *) <;>
    (try nlinarith)

  have h₈ : (x + y + z) * (x * y + y * z + z * x) ≥ 9 * x * y * z := by
    have h₈₁ : x * (y - z)^2 + y * (z - x)^2 + z * (x - y)^2 ≥ 0 := by
      nlinarith [sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - y)]
    have h₈₂ : (x + y + z) * (x * y + y * z + z * x) - 9 * x * y * z ≥ 0 := by
      linarith
    linarith

  have h₉ : (x + y) * (y + z) * (z + x) = (x + y + z) * (x * y + y * z + z * x) - x * y * z := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try ring_nf at *) <;>
    (try nlinarith)

  have h₁₀ : (x + y) * (y + z) * (z + x) ≥ (8 : ℝ) / 9 * (x + y + z) * (x * y + y * z + z * x) := by
    have h₁₀₁ : (x + y + z) * (x * y + y * z + z * x) ≥ 9 * x * y * z := h₈
    have h₁₀₂ : (x + y) * (y + z) * (z + x) = (x + y + z) * (x * y + y * z + z * x) - x * y * z := h₉
    have h₁₀₃ : 0 < x * y * z := by positivity
    have h₁₀₄ : 0 < (x + y + z) * (x * y + y * z + z * x) := by positivity
    have h₁₀₅ : (x + y) * (y + z) * (z + x) ≥ (8 : ℝ) / 9 * (x + y + z) * (x * y + y * z + z * x) := by
      nlinarith [h₁₀₁, h₁₀₂, h₁₀₃, h₁₀₄]
    exact h₁₀₅

  have h₁₁ : x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) = 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x)) := by
    have h₁₁₁ : 0 < (x + y) := by linarith
    have h₁₁₂ : 0 < (y + z) := by linarith
    have h₁₁₃ : 0 < (z + x) := by linarith
    have h₁₁₄ : 0 < (x + y) * (y + z) := by positivity
    have h₁₁₅ : 0 < (x + y) * (z + x) := by positivity
    have h₁₁₆ : 0 < (y + z) * (z + x) := by positivity
    have h₁₁₇ : 0 < (x + y) * (y + z) * (z + x) := by positivity
    have h₁₁₈ : x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) = (x * (y + z) + y * (z + x) + z * (x + y)) / ((x + y) * (y + z) * (z + x)) := by
      field_simp [h₁₁₁.ne', h₁₁₂.ne', h₁₁₃.ne', h₁₁₄.ne', h₁₁₅.ne', h₁₁₆.ne', h₁₁₇.ne']
      <;> ring_nf
      <;> field_simp [h₁₁₁.ne', h₁₁₂.ne', h₁₁₃.ne', h₁₁₄.ne', h₁₁₅.ne', h₁₁₆.ne', h₁₁₇.ne']
      <;> ring_nf
      <;> nlinarith
    have h₁₁₉ : (x * (y + z) + y * (z + x) + z * (x + y)) / ((x + y) * (y + z) * (z + x)) = 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x)) := by
      have h₁₂₀ : x * (y + z) + y * (z + x) + z * (x + y) = 2 * (x * y + y * z + z * x) := by
        ring
      rw [h₁₂₀]
    rw [h₁₁₈, h₁₁₉]

  have h₁₂ : 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x)) ≤ 9 / (4 * (x + y + z)) := by
    have h₁₂₁ : 0 < x + y + z := by linarith
    have h₁₂₂ : 0 < x * y + y * z + z * x := by positivity
    have h₁₂₃ : 0 < (x + y) * (y + z) * (z + x) := by positivity
    have h₁₂₄ : 0 < 4 * (x + y + z) := by positivity
    have h₁₂₅ : 0 < (x + y) * (y + z) * (z + x) * (4 * (x + y + z)) := by positivity
    have h₁₂₆ : 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x)) ≤ 9 / (4 * (x + y + z)) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [h₁₀, mul_pos h₁₂₁ h₁₂₂, mul_pos h₁₂₁ h₁₂₃,
        mul_pos (mul_pos h₁₂₁ h₁₂₂) h₁₂₃]
    exact h₁₂₆

  have h₁₃ : x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) ≤ 9 / (4 * (x + y + z)) := by
    have h₁₃₁ : x / ((x + y) * (x + z)) + y / ((y + z) * (y + x)) + z / ((z + x) * (z + y)) = 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x)) := h₁₁
    rw [h₁₃₁]
    have h₁₃₂ : 2 * (x * y + y * z + z * x) / ((x + y) * (y + z) * (z + x)) ≤ 9 / (4 * (x + y + z)) := h₁₂
    linarith

  exact h₁₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_example_14 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) + 1 / (c ^ 3 * (a + b)) ≥ 3 / 2 := by
  have h_main : ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → a * b * c = 1 → 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) + 1 / (c ^ 3 * (a + b)) ≥ 3 / 2 := by
    intro a b c ha hb hc habc
    have h₁ : 0 < a * b := by positivity
    have h₂ : 0 < a * c := by positivity
    have h₃ : 0 < b * c := by positivity
    have h₄ : (a * b) * (b * c) * (c * a) = 1 := by
      calc
        (a * b) * (b * c) * (c * a) = (a * b * c) * (a * b * c) := by ring
        _ = 1 * 1 := by rw [habc]
        _ = 1 := by ring
    have h₅ : a * b + b * c + c * a ≥ 3 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
    have h₆ : (b * c) ^ 2 / (a * b + a * c) + (a * c) ^ 2 / (a * b + b * c) + (a * b) ^ 2 / (a * c + b * c) ≥ (a * b + b * c + c * a) / 2 := by
      have h₆₁ : 0 < a * b + a * c := by positivity
      have h₆₂ : 0 < a * b + b * c := by positivity
      have h₆₃ : 0 < a * c + b * c := by positivity
      have h₆₄ : 0 < (a * b + a * c) * (a * b + b * c) * (a * c + b * c) := by positivity
      field_simp [h₆₁.ne', h₆₂.ne', h₆₃.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((b * c) ^ 2 - (a * c) ^ 2), sq_nonneg ((a * c) ^ 2 - (a * b) ^ 2),
        sq_nonneg ((a * b) ^ 2 - (b * c) ^ 2), mul_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (a * c)),
        mul_nonneg (sq_nonneg (a * c - b * c)) (sq_nonneg (a * b)), mul_nonneg (sq_nonneg (a * b - a * c)) (sq_nonneg (b * c))]
    have h₇ : 1 / (a ^ 3 * (b + c)) = (b * c) ^ 2 / (a * b + a * c) := by
      have h₇₁ : a ^ 3 * (b + c) = a ^ 2 * (a * (b + c)) := by ring
      have h₇₂ : a ^ 3 * (b + c) = a ^ 2 * (a * b + a * c) := by
        calc
          a ^ 3 * (b + c) = a ^ 2 * (a * (b + c)) := by ring
          _ = a ^ 2 * (a * b + a * c) := by ring
      have h₇₃ : (b * c) ^ 2 = 1 / a ^ 2 := by
        have h₇₄ : a * b * c = 1 := habc
        have h₇₅ : b * c = 1 / a := by
          field_simp [ha.ne'] at h₇₄ ⊢
          nlinarith
        calc
          (b * c) ^ 2 = (1 / a) ^ 2 := by rw [h₇₅]
          _ = 1 / a ^ 2 := by field_simp [ha.ne'] <;> ring
          _ = 1 / a ^ 2 := by ring
      calc
        1 / (a ^ 3 * (b + c)) = 1 / (a ^ 2 * (a * b + a * c)) := by
          rw [h₇₂]
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
        _ = (1 / a ^ 2) / (a * b + a * c) := by
          field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
        _ = (b * c) ^ 2 / (a * b + a * c) := by
          rw [h₇₃]
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
    have h₈ : 1 / (b ^ 3 * (c + a)) = (a * c) ^ 2 / (a * b + b * c) := by
      have h₈₁ : b ^ 3 * (c + a) = b ^ 2 * (b * (c + a)) := by ring
      have h₈₂ : b ^ 3 * (c + a) = b ^ 2 * (b * c + a * b) := by
        calc
          b ^ 3 * (c + a) = b ^ 2 * (b * (c + a)) := by ring
          _ = b ^ 2 * (b * c + a * b) := by ring
      have h₈₃ : (a * c) ^ 2 = 1 / b ^ 2 := by
        have h₈₄ : a * b * c = 1 := habc
        have h₈₅ : a * c = 1 / b := by
          field_simp [hb.ne'] at h₈₄ ⊢
          nlinarith
        calc
          (a * c) ^ 2 = (1 / b) ^ 2 := by rw [h₈₅]
          _ = 1 / b ^ 2 := by field_simp [hb.ne'] <;> ring
          _ = 1 / b ^ 2 := by ring
      calc
        1 / (b ^ 3 * (c + a)) = 1 / (b ^ 2 * (b * c + a * b)) := by
          rw [h₈₂]
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
        _ = (1 / b ^ 2) / (a * b + b * c) := by
          field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
        _ = (a * c) ^ 2 / (a * b + b * c) := by
          rw [h₈₃]
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
    have h₉ : 1 / (c ^ 3 * (a + b)) = (a * b) ^ 2 / (a * c + b * c) := by
      have h₉₁ : c ^ 3 * (a + b) = c ^ 2 * (c * (a + b)) := by ring
      have h₉₂ : c ^ 3 * (a + b) = c ^ 2 * (a * c + b * c) := by
        calc
          c ^ 3 * (a + b) = c ^ 2 * (c * (a + b)) := by ring
          _ = c ^ 2 * (a * c + b * c) := by ring
      have h₉₃ : (a * b) ^ 2 = 1 / c ^ 2 := by
        have h₉₄ : a * b * c = 1 := habc
        have h₉₅ : a * b = 1 / c := by
          field_simp [hc.ne'] at h₉₄ ⊢
          nlinarith
        calc
          (a * b) ^ 2 = (1 / c) ^ 2 := by rw [h₉₅]
          _ = 1 / c ^ 2 := by field_simp [hc.ne'] <;> ring
          _ = 1 / c ^ 2 := by ring
      calc
        1 / (c ^ 3 * (a + b)) = 1 / (c ^ 2 * (a * c + b * c)) := by
          rw [h₉₂]
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
        _ = (1 / c ^ 2) / (a * c + b * c) := by
          field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
        _ = (a * b) ^ 2 / (a * c + b * c) := by
          rw [h₉₃]
          <;> field_simp [ha.ne', hb.ne', hc.ne']
          <;> ring
    have h₁₀ : (b * c) ^ 2 / (a * b + a * c) + (a * c) ^ 2 / (a * b + b * c) + (a * b) ^ 2 / (a * c + b * c) ≥ 3 / 2 := by
      calc
        (b * c) ^ 2 / (a * b + a * c) + (a * c) ^ 2 / (a * b + b * c) + (a * b) ^ 2 / (a * c + b * c) ≥ (a * b + b * c + c * a) / 2 := by
          exact h₆
        _ ≥ 3 / 2 := by
          have h₁₀₁ : (a * b + b * c + c * a : ℝ) ≥ 3 := by exact_mod_cast h₅
          linarith
    calc
      1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) + 1 / (c ^ 3 * (a + b)) = (b * c) ^ 2 / (a * b + a * c) + (a * c) ^ 2 / (a * b + b * c) + (a * b) ^ 2 / (a * c + b * c) := by
        rw [h₇, h₈, h₉]
      _ ≥ 3 / 2 := by
        exact h₁₀
  intro a b c h
  have h₁ : a > 0 := h.1
  have h₂ : b > 0 := h.2.1
  have h₃ : c > 0 := h.2.2.1
  have h₄ : a * b * c = 1 := h.2.2.2
  exact h_main a b c h₁ h₂ h₃ h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_1_left : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 → 0 ≤ y * z + z * x + x * y - 2 * x * y * z := by
  intro x y z h
  have h₁ : y ≤ 1 := by
    have h₁₁ : x + y + z = 1 := h.2.2.2
    have h₁₂ : x ≥ 0 := h.1
    have h₁₃ : z ≥ 0 := h.2.2.1
    nlinarith [h.2.1, h.2.2.1]
  
  have h₂ : z ≤ 1 := by
    have h₂₁ : x + y + z = 1 := h.2.2.2
    have h₂₂ : x ≥ 0 := h.1
    have h₂₃ : y ≥ 0 := h.2.1
    nlinarith [h.2.1, h.2.2.1]
  
  have h₃ : y + z - 2 * y * z ≥ 0 := by
    have h₃₁ : 0 ≤ y := by linarith
    have h₃₂ : 0 ≤ z := by linarith
    have h₃₃ : y ≤ 1 := h₁
    have h₃₄ : z ≤ 1 := h₂
    have h₃₅ : 0 ≤ 1 - y := by linarith
    have h₃₆ : 0 ≤ 1 - z := by linarith
    nlinarith [mul_nonneg h₃₁ h₃₆, mul_nonneg h₃₂ h₃₅]
  
  have h₄ : y * z + z * x + x * y - 2 * x * y * z = y * z + x * (y + z - 2 * y * z) := by
    have h₄₁ : y * z + z * x + x * y - 2 * x * y * z = y * z + x * (y + z - 2 * y * z) := by
      ring_nf
      <;>
      (try linarith) <;>
      (try nlinarith) <;>
      (try ring_nf at * <;> linarith)
    linarith
  
  have h₅ : y * z + x * (y + z - 2 * y * z) ≥ y * z := by
    have h₅₁ : 0 ≤ x := by linarith
    have h₅₂ : y + z - 2 * y * z ≥ 0 := h₃
    have h₅₃ : 0 ≤ x * (y + z - 2 * y * z) := by
      nlinarith
    nlinarith
  
  have h₆ : y * z ≥ 0 := by
    have h₆₁ : 0 ≤ y := by linarith
    have h₆₂ : 0 ≤ z := by linarith
    nlinarith
  
  have h₇ : y * z + z * x + x * y - 2 * x * y * z ≥ 0 := by
    have h₇₁ : y * z + z * x + x * y - 2 * x * y * z = y * z + x * (y + z - 2 * y * z) := by
      rw [h₄]
    rw [h₇₁]
    have h₇₂ : y * z + x * (y + z - 2 * y * z) ≥ y * z := h₅
    have h₇₃ : y * z ≥ 0 := h₆
    linarith
  
  linarith

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_1_right : ∀ (x y z : ℝ), x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 → y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
  intro x y z h
  have h_sum : x + y + z = 1 := by
    linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  
  have h_nonneg : x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 := by
    refine' ⟨h.1, h.2.1, _⟩
    linarith [h.2.2.1, h.2.2.2]
  
  have h_schur : 1 + 9 * x * y * z ≥ 4 * (x * y + y * z + z * x) := by
    have h₁ : (x + y + z)^3 + 9 * x * y * z ≥ 4 * (x + y + z) * (x * y + y * z + z * x) := by
      nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
        mul_nonneg h.1 h.2.1, mul_nonneg h.1 h.2.2.1, mul_nonneg h.2.1 h.2.2.1,
        sq_nonneg (x + y - z), sq_nonneg (x + z - y), sq_nonneg (y + z - x)]
    have h₂ : x + y + z = 1 := h_sum
    rw [h₂] at h₁
    linarith
  
  have h_main_ineq : x * y + y * z + z * x ≤ (1 + 9 * x * y * z) / 4 := by
    have h₁ : 1 + 9 * x * y * z ≥ 4 * (x * y + y * z + z * x) := h_schur
    linarith
  
  have h_xyz_bound : x * y * z ≤ 1 / 27 := by
    have h₁ : 0 ≤ x := by linarith
    have h₂ : 0 ≤ y := by linarith
    have h₃ : 0 ≤ z := by linarith
    have h₄ : x + y + z = 1 := h_sum
    have h₅ : x * y * z ≤ 1 / 27 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_nonneg h₁ h₂, mul_nonneg h₂ h₃, mul_nonneg h₃ h₁]
    exact h₅
  
  have h_final : y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
    have h₁ : x * y + y * z + z * x ≤ (1 + 9 * x * y * z) / 4 := h_main_ineq
    have h₂ : x * y * z ≤ 1 / 27 := h_xyz_bound
    have h₃ : 0 ≤ x := by linarith [h_nonneg.1]
    have h₄ : 0 ≤ y := by linarith [h_nonneg.2.1]
    have h₅ : 0 ≤ z := by linarith [h_nonneg.2.2]
    have h₆ : 0 ≤ x * y := by positivity
    have h₇ : 0 ≤ y * z := by positivity
    have h₈ : 0 ≤ z * x := by positivity
    have h₉ : 0 ≤ x * y * z := by positivity
    have h₁₀ : y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    exact h₁₀
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_2 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c ≥ a * b * c → a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b * c := by
  intro a b c h
  have h₁ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₁₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₂ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) ≥ 1 := by
    have ha : 0 < a := by linarith
    have hb : 0 < b := by linarith
    have hc : 0 < c := by linarith
    have h₃ : a + b + c ≥ a * b * c := by linarith
    have h₄ : 0 < a * b * c := by positivity
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < c * a := by positivity
    -- Divide both sides of the given inequality by abc to get the desired form
    have h₈ : (a + b + c) / (a * b * c) ≥ 1 := by
      have h₈₁ : (a + b + c) / (a * b * c) ≥ 1 := by
        rw [ge_iff_le]
        rw [le_div_iff (by positivity)]
        nlinarith
      linarith
    have h₉ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) = (a + b + c) / (a * b * c) := by
      have h₉₁ : 1 / (a * b) + 1 / (b * c) + 1 / (c * a) = (c + a + b) / (a * b * c) := by
        field_simp [h₅.ne', h₆.ne', h₇.ne', h₄.ne']
        <;> ring_nf
        <;> field_simp [ha.ne', hb.ne', hc.ne']
        <;> ring_nf
      have h₉₂ : (c + a + b) / (a * b * c) = (a + b + c) / (a * b * c) := by
        ring_nf
      linarith
    linarith
  
  have h₃ : 1 / a + 1 / b + 1 / c ≥ 1 := by
    have ha : 0 < a := by linarith
    have hb : 0 < b := by linarith
    have hc : 0 < c := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < b * c := by positivity
    have h₆ : 0 < c * a := by positivity
    by_contra! h₇
    have h₈ : (1 / a + 1 / b + 1 / c) ^ 2 ≥ 3 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) := by
      have h₈₁ : 0 < 1 / a := by positivity
      have h₈₂ : 0 < 1 / b := by positivity
      have h₈₃ : 0 < 1 / c := by positivity
      have h₈₄ : (1 / a + 1 / b + 1 / c) ^ 2 ≥ 3 * (1 / a * (1 / b) + 1 / b * (1 / c) + 1 / c * (1 / a)) := by
        nlinarith [sq_nonneg (1 / a - 1 / b), sq_nonneg (1 / b - 1 / c), sq_nonneg (1 / c - 1 / a)]
      have h₈₅ : 1 / a * (1 / b) + 1 / b * (1 / c) + 1 / c * (1 / a) = 1 / (a * b) + 1 / (b * c) + 1 / (c * a) := by
        field_simp [ha.ne', hb.ne', hc.ne']
        <;> ring_nf
        <;> field_simp [ha.ne', hb.ne', hc.ne']
        <;> ring_nf
      linarith
    have h₉ : 3 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≥ 3 := by
      linarith
    have h₁₀ : (1 / a + 1 / b + 1 / c) ^ 2 ≥ 3 := by linarith
    have h₁₁ : 1 / a + 1 / b + 1 / c > 0 := by positivity
    have h₁₂ : 1 / a + 1 / b + 1 / c ≥ Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
    have h₁₃ : Real.sqrt 3 > 1 := by
      norm_num [Real.lt_sqrt, Real.sqrt_lt]
    linarith
  
  have h₄ : a * b + b * c + c * a ≥ a * b * c := by
    have ha : 0 < a := by linarith
    have hb : 0 < b := by linarith
    have hc : 0 < c := by linarith
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < c * a := by positivity
    have h₈ : 0 < a * b * c := by positivity
    have h₉ : 1 / a + 1 / b + 1 / c ≥ 1 := h₃
    have h₁₀ : (1 / a + 1 / b + 1 / c) * (a * b * c) ≥ 1 * (a * b * c) := by
      gcongr
    have h₁₁ : (1 / a + 1 / b + 1 / c) * (a * b * c) = b * c + a * c + a * b := by
      field_simp [ha.ne', hb.ne', hc.ne']
      <;> ring_nf
      <;> field_simp [ha.ne', hb.ne', hc.ne']
      <;> ring_nf
    have h₁₂ : 1 * (a * b * c) = a * b * c := by ring
    linarith
  
  have h₅ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b * c := by
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_2_3_3 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 → 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c) := by
  intro a b c h
  have h_main : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c) := by
    rcases h with ⟨ha, hb, hc, habc⟩
    have h₁ : 0 < a * b := by positivity
    have h₂ : 0 < a * c := by positivity
    have h₃ : 0 < b * c := by positivity
    have h₄ : 0 < a * b * c := by positivity
    -- Use the fact that the difference between LHS and RHS is non-positive
    have h₅ : (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a)) - (1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c)) ≤ 0 := by
      -- Prove that the difference is non-positive by finding a common denominator and simplifying
      field_simp [add_assoc]
      rw [div_le_iff (by positivity)]
      -- Use nlinarith to handle the polynomial inequality
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_nonneg ha.le hb.le, mul_nonneg ha.le hc.le, mul_nonneg hb.le hc.le,
        mul_nonneg (sq_nonneg (a - 1)) hc.le, mul_nonneg (sq_nonneg (b - 1)) ha.le,
        mul_nonneg (sq_nonneg (c - 1)) ha.le, mul_nonneg (sq_nonneg (a - 1)) hb.le,
        mul_nonneg (sq_nonneg (b - 1)) hc.le, mul_nonneg (sq_nonneg (c - 1)) hb.le,
        mul_nonneg (sq_nonneg (a - 1)) (mul_nonneg hb.le hc.le),
        mul_nonneg (sq_nonneg (b - 1)) (mul_nonneg ha.le hc.le),
        mul_nonneg (sq_nonneg (c - 1)) (mul_nonneg ha.le hb.le)]
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_3_1_1 : ∀ (x y : ℝ), x > 0 ∧ y > 0 → x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (x * y) := by
  intro x y hxy
  have h₁ : x ^ 4 + y ^ 2 ≥ 2 * x ^ 2 * y := by
    have h₁₁ : 0 ≤ (x ^ 2 - y) ^ 2 := sq_nonneg (x ^ 2 - y)
    have h₁₂ : (x ^ 2 - y) ^ 2 = x ^ 4 - 2 * x ^ 2 * y + y ^ 2 := by
      ring_nf
      <;>
      nlinarith
    nlinarith
  
  have h₂ : y ^ 4 + x ^ 2 ≥ 2 * x * y ^ 2 := by
    have h₂₁ : 0 ≤ (y ^ 2 - x) ^ 2 := sq_nonneg (y ^ 2 - x)
    have h₂₂ : (y ^ 2 - x) ^ 2 = y ^ 4 - 2 * x * y ^ 2 + x ^ 2 := by
      ring_nf
      <;>
      nlinarith
    nlinarith
  
  have h₃ : x / (x ^ 4 + y ^ 2) ≤ 1 / (2 * x * y) := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have h₃₁ : 0 < x ^ 4 + y ^ 2 := by positivity
    have h₃₂ : 0 < 2 * x * y := by positivity
    have h₃₃ : 0 < x * (2 * x * y) := by positivity
    -- Use the division inequality to transform the goal
    have h₃₄ : x / (x ^ 4 + y ^ 2) ≤ 1 / (2 * x * y) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to verify the inequality
      nlinarith [h₁, mul_pos hx hy, mul_pos (pow_pos hx 2) hy]
    exact h₃₄
  
  have h₄ : y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have h₄₁ : 0 < y ^ 4 + x ^ 2 := by positivity
    have h₄₂ : 0 < 2 * x * y := by positivity
    have h₄₃ : 0 < y * (2 * x * y) := by positivity
    -- Use the division inequality to transform the goal
    have h₄₄ : y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to verify the inequality
      nlinarith [h₂, mul_pos hx hy, mul_pos (pow_pos hy 2) hx]
    exact h₄₄
  
  have h₅ : x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (x * y) := by
    have hx : 0 < x := by linarith
    have hy : 0 < y := by linarith
    have h₅₁ : 0 < x * y := mul_pos hx hy
    have h₅₂ : 0 < 2 * x * y := by positivity
    have h₅₃ : x / (x ^ 4 + y ^ 2) + y / (y ^ 4 + x ^ 2) ≤ 1 / (2 * x * y) + 1 / (2 * x * y) := by
      linarith
    have h₅₄ : 1 / (2 * x * y) + 1 / (2 * x * y) = 1 / (x * y) := by
      field_simp [h₅₁.ne', hx.ne', hy.ne']
      <;> ring_nf <;> field_simp [h₅₁.ne', hx.ne', hy.ne'] <;> ring_nf <;>
        nlinarith
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

lemma lemma1 (a b : ℝ) (ha : a > 0) (hb : b > 0) : 1 / a + 1 / b ≥ 4 / (a + b) := by
  have h₁ : 0 < a * b := mul_pos ha hb
  have h₂ : 0 < a + b := add_pos ha hb
  field_simp [ha.ne', hb.ne', h₂.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

lemma lemma2 (c d : ℝ) (hc : c > 0) (hd : d > 0) : 4 / c + 16 / d ≥ 36 / (c + d) := by
  have h₁ : 0 < c * d := mul_pos hc hd
  have h₂ : 0 < c + d := add_pos hc hd
  field_simp [hc.ne', hd.ne', h₂.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (2 * d - 4 * c), sq_nonneg (c - d), sq_nonneg (c + d)]

lemma lemma3 (x y : ℝ) (hx : x > 0) (hy : y > 0) : 4 / x + 36 / y ≥ 64 / (x + y) := by
  have h₁ : 0 < x * y := mul_pos hx hy
  have h₂ : 0 < x + y := add_pos hx hy
  field_simp [hx.ne', hy.ne', h₂.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (2 * y - 6 * x), sq_nonneg (x - y), sq_nonneg (x + y)]

theorem kiran_problem_3_1_4_correct (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
  have h₁ : 1 / a + 1 / b ≥ 4 / (a + b) := by
    have h₁₀ : 1 / a + 1 / b ≥ 4 / (a + b) := lemma1 a b ha hb
    exact h₁₀
  
  have h₂ : 4 / c + 16 / d ≥ 36 / (c + d) := by
    have h₂₀ : 4 / c + 16 / d ≥ 36 / (c + d) := lemma2 c d hc hd
    exact h₂₀
  
  have h₃ : 1 / a + 1 / b + 4 / c + 16 / d ≥ 4 / (a + b) + 36 / (c + d) := by
    have h₃₁ : 1 / a + 1 / b + 4 / c + 16 / d = (1 / a + 1 / b) + (4 / c + 16 / d) := by ring
    rw [h₃₁]
    linarith [h₁, h₂]
  
  have h₄ : 4 / (a + b) + 36 / (c + d) ≥ 64 / (a + b + c + d) := by
    have h₄₁ : 0 < a + b := by linarith
    have h₄₂ : 0 < c + d := by linarith
    have h₄₃ : 0 < a + b + c + d := by linarith
    have h₄₄ : 4 / (a + b) + 36 / (c + d) ≥ 64 / (a + b + c + d) := by
      have h₄₅ : 4 / (a + b) + 36 / (c + d) ≥ 64 / ((a + b) + (c + d)) := lemma3 (a + b) (c + d) (by linarith) (by linarith)
      have h₄₇ : (a + b) + (c + d) = a + b + c + d := by ring
      rw [h₄₇] at h₄₅
      linarith
    exact h₄₄
  
  have h₅ : 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 / (a + b + c + d) := by
    calc
      1 / a + 1 / b + 4 / c + 16 / d ≥ 4 / (a + b) + 36 / (c + d) := h₃
      _ ≥ 64 / (a + b + c + d) := h₄
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem kiran_problem_5_2_1 : ∀ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1 → x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  intro x y z h
  have h₁ : x + y + z ≥ 3 := by
    have h₁₁ : 0 < x := by linarith
    have h₁₂ : 0 < y := by linarith
    have h₁₃ : 0 < z := by linarith
    have h₁₄ : 0 < x * y := by positivity
    have h₁₅ : 0 < x * z := by positivity
    have h₁₆ : 0 < y * z := by positivity
    -- Use the AM-GM inequality to show that x + y + z ≥ 3
    have h₁₇ : x + y + z ≥ 3 := by
      nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
        mul_pos h₁₁ h₁₂, mul_pos h₁₁ h₁₃, mul_pos h₁₂ h₁₃]
    exact h₁₇
  
  have h₂ : x ^ 2 + y ^ 2 + z ^ 2 ≥ 2 * (x + y + z) - 3 := by
    have h₂₁ : x ^ 2 ≥ 2 * x - 1 := by
      have h₂₁₁ : (x - 1) ^ 2 ≥ 0 := by nlinarith
      nlinarith
    have h₂₂ : y ^ 2 ≥ 2 * y - 1 := by
      have h₂₂₁ : (y - 1) ^ 2 ≥ 0 := by nlinarith
      nlinarith
    have h₂₃ : z ^ 2 ≥ 2 * z - 1 := by
      have h₂₃₁ : (z - 1) ^ 2 ≥ 0 := by nlinarith
      nlinarith
    -- Summing up the inequalities
    linarith
  
  have h₃ : 2 * (x + y + z) - 3 ≥ x + y + z := by
    have h₃₁ : x + y + z ≥ 3 := h₁
    linarith
  
  have h₄ : x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
    linarith
  
  exact h₄
