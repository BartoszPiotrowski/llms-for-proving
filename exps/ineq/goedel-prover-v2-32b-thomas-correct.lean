
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_1 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
  intro a b c h
  have h₁ : a > 0 := by linarith
  have h₂ : b > 0 := by linarith
  have h₃ : c > 0 := by linarith
  have h₄ : (a / c + b / a + c / b) ≥ 3 := by
    have h₄₁ : 0 < a * b := by positivity
    have h₄₂ : 0 < b * c := by positivity
    have h₄₃ : 0 < c * a := by positivity
    have h₄₄ : 0 < a * b * c := by positivity
    have h₄₅ : 0 < a * b * c * a := by positivity
    have h₄₆ : 0 < a * b * c * b := by positivity
    have h₄₇ : 0 < a * b * c * c := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne']
    rw [le_div_iff (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h₅ : (b / c + c / a + a / b) ≥ 3 := by
    have h₅₁ : 0 < a * b := by positivity
    have h₅₂ : 0 < b * c := by positivity
    have h₅₃ : 0 < c * a := by positivity
    have h₅₄ : 0 < a * b * c := by positivity
    have h₅₅ : 0 < a * b * c * a := by positivity
    have h₅₆ : 0 < a * b * c * b := by positivity
    have h₅₇ : 0 < a * b * c * c := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne']
    rw [le_div_iff (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h₆ : (a / c + b / a + c / b) * (b / c + c / a + a / b) ≥ 9 := by
    have h₆₁ : (a / c + b / a + c / b) ≥ 3 := h₄
    have h₆₂ : (b / c + c / a + a / b) ≥ 3 := h₅
    have h₆₃ : (a / c + b / a + c / b) * (b / c + c / a + a / b) ≥ 3 * 3 := by
      nlinarith
    linarith
  have h₇ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) / (a * b * c) = a / c + b / a + c / b := by
    have h₇₁ : 0 < a * b * c := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne', h₇₁.ne']
    <;> ring_nf
    <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
    <;> ring_nf
  have h₈ : (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a * b * c) = b / c + c / a + a / b := by
    have h₈₁ : 0 < a * b * c := by positivity
    field_simp [h₁.ne', h₂.ne', h₃.ne', h₈₁.ne']
    <;> ring_nf
    <;> field_simp [h₁.ne', h₂.ne', h₃.ne']
    <;> ring_nf
  have h₉ : ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) / (a * b * c)) * ((a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a * b * c)) ≥ 9 := by
    calc
      ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) / (a * b * c)) * ((a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a * b * c)) = (a / c + b / a + c / b) * (b / c + c / a + a / b) := by
        rw [h₇, h₈]
        <;> ring_nf
      _ ≥ 9 := by
        exact h₆
  have h₁₀ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * (a * b * c) ^ 2 := by
    have h₁₀₁ : 0 < a * b * c := by positivity
    have h₁₀₂ : 0 < (a * b * c) ^ 2 := by positivity
    have h₁₀₃ : ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) / (a * b * c)) * ((a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a * b * c)) ≥ 9 := h₉
    have h₁₀₄ : ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) / (a * b * c)) * ((a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / (a * b * c)) = (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2) := by
      field_simp [h₁₀₁.ne']
      <;> ring_nf
      <;> field_simp [h₁₀₁.ne']
      <;> ring_nf
    have h₁₀₅ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2) ≥ 9 := by
      linarith
    have h₁₀₆ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * (a * b * c) ^ 2 := by
      have h₁₀₇ : 0 < (a * b * c) ^ 2 := by positivity
      have h₁₀₈ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2) ≥ 9 := h₁₀₅
      have h₁₀₉ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * (a * b * c) ^ 2 := by
        calc
          (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) = ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2)) * ((a * b * c) ^ 2) := by
            field_simp [h₁₀₁.ne']
            <;> ring_nf
            <;> field_simp [h₁₀₁.ne']
            <;> ring_nf
          _ ≥ 9 * ((a * b * c) ^ 2) := by
            have h₁₁₀ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2) ≥ 9 := h₁₀₅
            have h₁₁₁ : 0 < (a * b * c) ^ 2 := by positivity
            have h₁₁₂ : ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2)) * ((a * b * c) ^ 2) ≥ 9 * ((a * b * c) ^ 2) := by
              calc
                ((a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2)) * ((a * b * c) ^ 2) ≥ 9 * ((a * b * c) ^ 2) := by
                  have h₁₁₃ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) / ((a * b * c) ^ 2) ≥ 9 := h₁₀₅
                  have h₁₁₄ : 0 < (a * b * c) ^ 2 := by positivity
                  nlinarith
                _ = 9 * ((a * b * c) ^ 2) := by ring
            linarith
          _ = 9 * ((a * b * c) ^ 2) := by ring
      exact h₁₀₉
    exact h₁₀₆
  have h₁₁ : 9 * (a * b * c) ^ 2 = 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
    ring_nf
    <;>
    (try simp [mul_assoc, mul_comm, mul_left_comm])
    <;>
    (try ring_nf)
    <;>
    (try norm_num)
    <;>
    (try linarith)
  have h₁₂ : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
    calc
      (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) ≥ 9 * (a * b * c) ^ 2 := by
        exact h₁₀
      _ = 9 * a ^ 2 * b ^ 2 * c ^ 2 := by
        rw [h₁₁]
  exact h₁₂

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_2 : ∀ (a b c : ℝ), a * b * c = 1 → a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h_main_inequality : ∀ (a b c : ℝ), a * b * c = 1 → a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    intro a b c h
    have h₁ : a ^ 2 + 1 ≥ 2 * |a| := by
      cases' le_or_lt 0 a with ha ha
      · -- Case: a ≥ 0
        have h₂ : |a| = a := abs_of_nonneg ha
        have h₃ : (a - 1) ^ 2 ≥ 0 := by nlinarith
        nlinarith [h₃]
      · -- Case: a < 0
        have h₂ : |a| = -a := abs_of_neg ha
        have h₃ : (a + 1) ^ 2 ≥ 0 := by nlinarith
        nlinarith [h₃]
    have h₂ : b ^ 2 + 1 ≥ 2 * |b| := by
      cases' le_or_lt 0 b with hb hb
      · -- Case: b ≥ 0
        have h₃ : |b| = b := abs_of_nonneg hb
        have h₄ : (b - 1) ^ 2 ≥ 0 := by nlinarith
        nlinarith [h₄]
      · -- Case: b < 0
        have h₃ : |b| = -b := abs_of_neg hb
        have h₄ : (b + 1) ^ 2 ≥ 0 := by nlinarith
        nlinarith [h₄]
    have h₃ : c ^ 2 + 1 ≥ 2 * |c| := by
      cases' le_or_lt 0 c with hc hc
      · -- Case: c ≥ 0
        have h₄ : |c| = c := abs_of_nonneg hc
        have h₅ : (c - 1) ^ 2 ≥ 0 := by nlinarith
        nlinarith [h₅]
      · -- Case: c < 0
        have h₄ : |c| = -c := abs_of_neg hc
        have h₅ : (c + 1) ^ 2 ≥ 0 := by nlinarith
        nlinarith [h₅]
    have h₄ : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (|a| + |b| + |c|) := by
      linarith [h₁, h₂, h₃]
    have h₅ : |a| + |b| + |c| ≥ 3 := by
      have h₅₁ : 0 ≤ |a| := abs_nonneg a
      have h₅₂ : 0 ≤ |b| := abs_nonneg b
      have h₅₃ : 0 ≤ |c| := abs_nonneg c
      have h₅₄ : 0 ≤ |a| * |b| := by positivity
      have h₅₅ : 0 ≤ |a| * |b| * |c| := by positivity
      have h₅₆ : |a| * |b| * |c| = 1 := by
        calc
          |a| * |b| * |c| = |a * b * c| := by
            simp [abs_mul, abs_mul]
            <;> ring_nf
          _ = 1 := by
            rw [h]
            <;> simp [abs_of_pos, show (0 : ℝ) < 1 by norm_num]
      -- Use AM-GM inequality to show |a| + |b| + |c| ≥ 3
      have h₅₇ : |a| + |b| + |c| ≥ 3 := by
        nlinarith [sq_nonneg (|a| + |b| + |c|), sq_nonneg (|a| - |b|), sq_nonneg (|a| - |c|),
          sq_nonneg (|b| - |c|)]
      linarith
    have h₆ : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 := by
      linarith [h₄, h₅]
    by_cases h₇ : a + b + c ≥ 3
    · -- Case: a + b + c ≥ 3
      have h₈ : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 ≥ 0 := by positivity
      have h₉ : a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * (a + b + c) - 3 := by
        nlinarith [h₈]
      nlinarith
    · -- Case: a + b + c < 3
      have h₈ : a + b + c < 3 := by linarith
      have h₉ : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 := by linarith [h₆]
      linarith
  exact h_main_inequality

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_4 : ∀ (a b c d e : ℝ), a + b + c + d + e = 8 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 16 → e ≤ 16 / 5 := by
  intro a b c d e h
  have h_sum : a + b + c + d = 8 - e := by
    have h₁ : a + b + c + d + e = 8 := h.1
    linarith
  
  have h_sum_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by
    have h₁ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 16 := h.2
    linarith
  
  have h_ineq : 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ (a + b + c + d) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  
  have h_main_ineq : 4 * (16 - e ^ 2) ≥ (8 - e) ^ 2 := by
    have h₁ : 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ (a + b + c + d) ^ 2 := h_ineq
    have h₂ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := h_sum_sq
    have h₃ : a + b + c + d = 8 - e := h_sum
    calc
      4 * (16 - e ^ 2) = 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by rw [h₂]
      _ ≥ (a + b + c + d) ^ 2 := h₁
      _ = (8 - e) ^ 2 := by rw [h₃]
  
  have h_quadratic : 5 * e ^ 2 - 16 * e ≤ 0 := by
    have h₁ : 4 * (16 - e ^ 2) ≥ (8 - e) ^ 2 := h_main_ineq
    nlinarith [sq_nonneg (e - 16 / 5)]
  
  have h_final : e ≤ 16 / 5 := by
    have h₁ : 5 * e ^ 2 - 16 * e ≤ 0 := h_quadratic
    by_contra! h₂
    have h₃ : e > 16 / 5 := by linarith
    have h₄ : 5 * e ^ 2 - 16 * e > 0 := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr h₃)]
    linarith
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_9_left : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d → 1 < a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) := by
  intro a b c d h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < d := by linarith
  have h₅ : a / (a + b + d) > a / (a + b + c + d) := by
    have h₅₁ : 0 < a + b + d := by linarith
    have h₅₂ : 0 < a + b + c + d := by linarith
    have h₅₃ : a + b + d < a + b + c + d := by linarith
    have h₅₄ : 0 < a := by linarith
    -- Use the lemma `div_lt_div_of_lt_left` to compare the fractions
    have h₅₅ : a / (a + b + d) > a / (a + b + c + d) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      -- Prove that a * (a + b + c + d) > a * (a + b + d)
      have h₅₆ : 0 < a + b + d := by linarith
      have h₅₇ : 0 < a + b + c + d := by linarith
      nlinarith
    exact h₅₅
  have h₆ : b / (b + c + a) > b / (a + b + c + d) := by
    have h₆₁ : 0 < b + c + a := by linarith
    have h₆₂ : 0 < a + b + c + d := by linarith
    have h₆₃ : b + c + a < a + b + c + d := by linarith
    have h₆₄ : 0 < b := by linarith
    -- Use the lemma `div_lt_div_of_lt_left` to compare the fractions
    have h₆₅ : b / (b + c + a) > b / (a + b + c + d) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      -- Prove that b * (a + b + c + d) > b * (b + c + a)
      have h₆₆ : 0 < b + c + a := by linarith
      have h₆₇ : 0 < a + b + c + d := by linarith
      nlinarith
    exact h₆₅
  have h₇ : c / (b + c + d) > c / (a + b + c + d) := by
    have h₇₁ : 0 < b + c + d := by linarith
    have h₇₂ : 0 < a + b + c + d := by linarith
    have h₇₃ : b + c + d < a + b + c + d := by linarith
    have h₇₄ : 0 < c := by linarith
    -- Use the lemma `div_lt_div_of_lt_left` to compare the fractions
    have h₇₅ : c / (b + c + d) > c / (a + b + c + d) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      -- Prove that c * (a + b + c + d) > c * (b + c + d)
      have h₇₆ : 0 < b + c + d := by linarith
      have h₇₇ : 0 < a + b + c + d := by linarith
      nlinarith
    exact h₇₅
  have h₈ : d / (a + c + d) > d / (a + b + c + d) := by
    have h₈₁ : 0 < a + c + d := by linarith
    have h₈₂ : 0 < a + b + c + d := by linarith
    have h₈₃ : a + c + d < a + b + c + d := by linarith
    have h₈₄ : 0 < d := by linarith
    -- Use the lemma `div_lt_div_of_lt_left` to compare the fractions
    have h₈₅ : d / (a + c + d) > d / (a + b + c + d) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      -- Prove that d * (a + b + c + d) > d * (a + c + d)
      have h₈₆ : 0 < a + c + d := by linarith
      have h₈₇ : 0 < a + b + c + d := by linarith
      nlinarith
    exact h₈₅
  have h₉ : a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) > 1 := by
    have h₉₁ : a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) = 1 := by
      have h₉₂ : 0 < a + b + c + d := by linarith
      field_simp [h₉₂.ne']
      <;> ring_nf
      <;> field_simp [h₉₂.ne']
      <;> linarith
    have h₉₃ : a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) > a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d) + d / (a + b + c + d) := by
      linarith [h₅, h₆, h₇, h₈]
    linarith
  linarith

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_9_right : ∀ (a b c d : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d → a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < 2 := by
  intro a b c d h
  have h₁ : a / (a + b + d) < 1 - (b + d) / (a + b + c + d) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < d := by linarith
    have h₁₄ : 0 < c := by linarith
    have h₁₅ : 0 < a + b + d := by linarith
    have h₁₆ : 0 < a + b + c + d := by linarith
    have h₁₇ : 0 < b + d := by linarith
    have h₁₈ : 0 < c := by linarith
    have h₁₉ : 0 < (a + b + d) * (a + b + c + d) := by positivity
    -- Use the fact that (a / (a + b + d)) < (a + c) / (a + b + c + d)
    have h₂₀ : a / (a + b + d) < (a + c) / (a + b + c + d) := by
      -- Prove that a / (a + b + d) < (a + c) / (a + b + c + d)
      rw [div_lt_div_iff (by positivity) (by positivity)]
      nlinarith [mul_pos h₁₁ h₁₄, mul_pos h₁₁ h₁₃, mul_pos h₁₁ h₁₂, mul_pos h₁₄ h₁₃, mul_pos h₁₄ h₁₂, mul_pos h₁₃ h₁₂]
    -- Relate (a + c) / (a + b + c + d) to 1 - (b + d) / (a + b + c + d)
    have h₂₁ : (a + c) / (a + b + c + d) = 1 - (b + d) / (a + b + c + d) := by
      have h₂₂ : (a + c) / (a + b + c + d) + (b + d) / (a + b + c + d) = 1 := by
        field_simp [h₁₆.ne']
        <;> ring_nf
        <;> field_simp [h₁₆.ne']
        <;> ring_nf
        <;> linarith
      linarith
    -- Combine the inequalities to get the final result
    linarith
  
  have h₂ : b / (b + c + a) < 1 - (a + c) / (a + b + c + d) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < d := by linarith
    have h₂₅ : 0 < b + c + a := by linarith
    have h₂₆ : 0 < a + b + c + d := by linarith
    have h₂₇ : 0 < a + c := by linarith
    have h₂₈ : 0 < d := by linarith
    have h₂₉ : 0 < (b + c + a) * (a + b + c + d) := by positivity
    -- Use the fact that (b / (b + c + a)) < (b + d) / (a + b + c + d)
    have h₃₀ : b / (b + c + a) < (b + d) / (a + b + c + d) := by
      -- Prove that b / (b + c + a) < (b + d) / (a + b + c + d)
      rw [div_lt_div_iff (by positivity) (by positivity)]
      nlinarith [mul_pos h₂₂ h₂₄, mul_pos h₂₂ h₂₃, mul_pos h₂₂ h₂₁, mul_pos h₂₄ h₂₃, mul_pos h₂₄ h₂₁, mul_pos h₂₃ h₂₁]
    -- Relate (b + d) / (a + b + c + d) to 1 - (a + c) / (a + b + c + d)
    have h₃₁ : (b + d) / (a + b + c + d) = 1 - (a + c) / (a + b + c + d) := by
      have h₃₂ : (b + d) / (a + b + c + d) + (a + c) / (a + b + c + d) = 1 := by
        field_simp [h₂₆.ne']
        <;> ring_nf
        <;> field_simp [h₂₆.ne']
        <;> ring_nf
        <;> linarith
      linarith
    -- Combine the inequalities to get the final result
    linarith
  
  have h₃ : c / (b + c + d) < 1 - (b + d) / (a + b + c + d) := by
    have h₃₁ : 0 < a := by linarith
    have h₃₂ : 0 < b := by linarith
    have h₃₃ : 0 < c := by linarith
    have h₃₄ : 0 < d := by linarith
    have h₃₅ : 0 < b + c + d := by linarith
    have h₃₆ : 0 < a + b + c + d := by linarith
    have h₃₇ : 0 < b + d := by linarith
    have h₃₈ : 0 < a := by linarith
    have h₃₉ : 0 < (b + c + d) * (a + b + c + d) := by positivity
    -- Use the fact that (c / (b + c + d)) < (c + a) / (a + b + c + d)
    have h₄₀ : c / (b + c + d) < (c + a) / (a + b + c + d) := by
      -- Prove that c / (b + c + d) < (c + a) / (a + b + c + d)
      rw [div_lt_div_iff (by positivity) (by positivity)]
      nlinarith [mul_pos h₃₃ h₃₁, mul_pos h₃₃ h₃₄, mul_pos h₃₃ h₃₂, mul_pos h₃₁ h₃₄, mul_pos h₃₁ h₃₂, mul_pos h₃₄ h₃₂]
    -- Relate (c + a) / (a + b + c + d) to 1 - (b + d) / (a + b + c + d)
    have h₄₁ : (c + a) / (a + b + c + d) = 1 - (b + d) / (a + b + c + d) := by
      have h₄₂ : (c + a) / (a + b + c + d) + (b + d) / (a + b + c + d) = 1 := by
        field_simp [h₃₆.ne']
        <;> ring_nf
        <;> field_simp [h₃₆.ne']
        <;> ring_nf
        <;> linarith
      linarith
    -- Combine the inequalities to get the final result
    linarith
  
  have h₄ : d / (a + c + d) < 1 - (a + c) / (a + b + c + d) := by
    have h₄₁ : 0 < a := by linarith
    have h₄₂ : 0 < b := by linarith
    have h₄₃ : 0 < c := by linarith
    have h₄₄ : 0 < d := by linarith
    have h₄₅ : 0 < a + c + d := by linarith
    have h₄₆ : 0 < a + b + c + d := by linarith
    have h₄₇ : 0 < a + c := by linarith
    have h₄₈ : 0 < b := by linarith
    have h₄₉ : 0 < (a + c + d) * (a + b + c + d) := by positivity
    -- Use the fact that (d / (a + c + d)) < (d + b) / (a + b + c + d)
    have h₅₀ : d / (a + c + d) < (d + b) / (a + b + c + d) := by
      -- Prove that d / (a + c + d) < (d + b) / (a + b + c + d)
      rw [div_lt_div_iff (by positivity) (by positivity)]
      nlinarith [mul_pos h₄₄ h₄₂, mul_pos h₄₄ h₄₃, mul_pos h₄₄ h₄₁, mul_pos h₄₂ h₄₃, mul_pos h₄₂ h₄₁, mul_pos h₄₃ h₄₁]
    -- Relate (d + b) / (a + b + c + d) to 1 - (a + c) / (a + b + c + d)
    have h₅₁ : (d + b) / (a + b + c + d) = 1 - (a + c) / (a + b + c + d) := by
      have h₅₂ : (d + b) / (a + b + c + d) + (a + c) / (a + b + c + d) = 1 := by
        field_simp [h₄₆.ne']
        <;> ring_nf
        <;> field_simp [h₄₆.ne']
        <;> ring_nf
        <;> linarith
      linarith
    -- Combine the inequalities to get the final result
    linarith
  
  have h₅ : a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < 2 := by
    have h₅₁ : 0 < a + b + c + d := by linarith
    have h₅₂ : (b + d) / (a + b + c + d) + (a + c) / (a + b + c + d) + (b + d) / (a + b + c + d) + (a + c) / (a + b + c + d) = 2 := by
      have h₅₃ : (b + d) / (a + b + c + d) + (a + c) / (a + b + c + d) + (b + d) / (a + b + c + d) + (a + c) / (a + b + c + d) = ((b + d) + (a + c) + (b + d) + (a + c)) / (a + b + c + d) := by
        field_simp [h₅₁.ne']
        <;> ring_nf
        <;> field_simp [h₅₁.ne']
        <;> ring_nf
      rw [h₅₃]
      have h₅₄ : ((b + d) + (a + c) + (b + d) + (a + c)) / (a + b + c + d) = 2 := by
        have h₅₅ : (b + d) + (a + c) + (b + d) + (a + c) = 2 * (a + b + c + d) := by ring
        rw [h₅₅]
        field_simp [h₅₁.ne']
        <;> ring_nf
        <;> field_simp [h₅₁.ne']
        <;> linarith
      rw [h₅₄]
    -- Summing up the inequalities and using the fact that the sum of the subtracted terms is 2
    have h₅₆ : a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < 2 := by
      calc
        a / (a + b + d) + b / (b + c + a) + c / (b + c + d) + d / (a + c + d) < (1 - (b + d) / (a + b + c + d)) + (1 - (a + c) / (a + b + c + d)) + (1 - (b + d) / (a + b + c + d)) + (1 - (a + c) / (a + b + c + d)) := by
          linarith
        _ = 4 - ((b + d) / (a + b + c + d) + (a + c) / (a + b + c + d) + (b + d) / (a + b + c + d) + (a + c) / (a + b + c + d)) := by ring
        _ = 4 - 2 := by
          rw [h₅₂]
          <;> ring
        _ = 2 := by ring
    exact h₅₆
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_14 : ∀ (a b x y z : ℝ), 0 < a ∧ 0 < b ∧ 0 < x ∧ 0 < y ∧ 0 < z → x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
  intro a b x y z h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < x := by linarith
  have h₄ : 0 < y := by linarith
  have h₅ : 0 < z := by linarith
  have h₆ : 0 < a + b := by linarith
  have h₇ : 0 < a * y + b * z := by
    have h₇₁ : 0 < a * y := by positivity
    have h₇₂ : 0 < b * z := by positivity
    linarith
  have h₈ : 0 < a * z + b * x := by
    have h₈₁ : 0 < a * z := by positivity
    have h₈₂ : 0 < b * x := by positivity
    linarith
  have h₉ : 0 < a * x + b * y := by
    have h₉₁ : 0 < a * x := by positivity
    have h₉₂ : 0 < b * y := by positivity
    linarith
  have h₁₀ : (x + y + z)^2 ≥ 3 * (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h₁₁ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = (x^2 / (x * (a * y + b * z)) + y^2 / (y * (a * z + b * x)) + z^2 / (z * (a * x + b * y))) := by
    have h₁₁₁ : x / (a * y + b * z) = x^2 / (x * (a * y + b * z)) := by
      have h₁₁₁₁ : x ≠ 0 := by linarith
      have h₁₁₁₂ : a * y + b * z ≠ 0 := by linarith
      field_simp [h₁₁₁₁, h₁₁₁₂]
      <;> ring
      <;> field_simp [h₁₁₁₁, h₁₁₁₂]
      <;> ring
    have h₁₁₂ : y / (a * z + b * x) = y^2 / (y * (a * z + b * x)) := by
      have h₁₁₂₁ : y ≠ 0 := by linarith
      have h₁₁₂₂ : a * z + b * x ≠ 0 := by linarith
      field_simp [h₁₁₂₁, h₁₁₂₂]
      <;> ring
      <;> field_simp [h₁₁₂₁, h₁₁₂₂]
      <;> ring
    have h₁₁₃ : z / (a * x + b * y) = z^2 / (z * (a * x + b * y)) := by
      have h₁₁₃₁ : z ≠ 0 := by linarith
      have h₁₁₃₂ : a * x + b * y ≠ 0 := by linarith
      field_simp [h₁₁₃₁, h₁₁₃₂]
      <;> ring
      <;> field_simp [h₁₁₃₁, h₁₁₃₂]
      <;> ring
    rw [h₁₁₁, h₁₁₂, h₁₁₃]
    <;> ring
  
  have h₁₂ : (x^2 / (x * (a * y + b * z)) + y^2 / (y * (a * z + b * x)) + z^2 / (z * (a * x + b * y))) ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by
    have h₁₂₁ : 0 < x * (a * y + b * z) := by positivity
    have h₁₂₂ : 0 < y * (a * z + b * x) := by positivity
    have h₁₂₃ : 0 < z * (a * x + b * y) := by positivity
    have h₁₂₄ : 0 < (a + b) * (x * y + y * z + z * x) := by positivity
    -- Use Titu's lemma (a form of Cauchy-Schwarz inequality)
    have h₁₂₅ : (x^2 / (x * (a * y + b * z)) + y^2 / (y * (a * z + b * x)) + z^2 / (z * (a * x + b * y))) ≥ (x + y + z)^2 / (x * (a * y + b * z) + y * (a * z + b * x) + z * (a * x + b * y)) := by
      -- Apply Titu's lemma
      have h₁₂₅₁ : 0 < x * (a * y + b * z) := by positivity
      have h₁₂₅₂ : 0 < y * (a * z + b * x) := by positivity
      have h₁₂₅₃ : 0 < z * (a * x + b * y) := by positivity
      have h₁₂₅₄ : 0 < x * (a * y + b * z) + y * (a * z + b * x) + z * (a * x + b * y) := by positivity
      -- Use the Cauchy-Schwarz inequality in the form of Titu's lemma
      have h₁₂₅₅ : (x^2 / (x * (a * y + b * z)) + y^2 / (y * (a * z + b * x)) + z^2 / (z * (a * x + b * y))) ≥ (x + y + z)^2 / (x * (a * y + b * z) + y * (a * z + b * x) + z * (a * x + b * y)) := by
        -- Prove the inequality using the division inequality
        field_simp [h₁₂₅₁.ne', h₁₂₅₂.ne', h₁₂₅₃.ne', h₁₂₅₄.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith [sq_nonneg (x * (y * (a * z + b * x)) - y * (x * (a * y + b * z))),
          sq_nonneg (y * (z * (a * x + b * y)) - z * (y * (a * z + b * x))),
          sq_nonneg (z * (x * (a * y + b * z)) - x * (z * (a * x + b * y)))]
      exact h₁₂₅₅
    -- Show that the denominator is (a + b)(xy + yz + zx)
    have h₁₂₆ : x * (a * y + b * z) + y * (a * z + b * x) + z * (a * x + b * y) = (a + b) * (x * y + y * z + z * x) := by
      ring
    -- Substitute the denominator back into the inequality
    have h₁₂₇ : (x + y + z)^2 / (x * (a * y + b * z) + y * (a * z + b * x) + z * (a * x + b * y)) = (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by
      rw [h₁₂₆]
      <;> field_simp [h₆.ne']
      <;> ring
    -- Combine the inequalities
    linarith
  
  have h₁₃ : (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
    have h₁₃₁ : 0 < a + b := by linarith
    have h₁₃₂ : 0 < x * y + y * z + z * x := by
      nlinarith [mul_pos h₃ h₄, mul_pos h₄ h₅, mul_pos h₅ h₃]
    have h₁₃₃ : 0 < (a + b) * (x * y + y * z + z * x) := by positivity
    -- Use the fact that (x + y + z)^2 ≥ 3(xy + yz + zx) to establish the inequality
    have h₁₃₄ : (x + y + z)^2 ≥ 3 * (x * y + y * z + z * x) := by
      linarith
    -- Divide both sides by (a + b)(xy + yz + zx)
    have h₁₃₅ : (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) ≥ 3 / (a + b) := by
      calc
        (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) ≥ (3 * (x * y + y * z + z * x)) / ((a + b) * (x * y + y * z + z * x)) := by
          -- Use the fact that (x + y + z)^2 ≥ 3(xy + yz + zx)
          gcongr
          <;> nlinarith
        _ = 3 / (a + b) := by
          -- Simplify the right-hand side
          have h₁₃₅₁ : (3 * (x * y + y * z + z * x)) / ((a + b) * (x * y + y * z + z * x)) = 3 / (a + b) := by
            have h₁₃₅₂ : (a + b) * (x * y + y * z + z * x) ≠ 0 := by positivity
            have h₁₃₅₃ : 3 * (x * y + y * z + z * x) ≠ 0 := by positivity
            field_simp [h₁₃₅₂, h₁₃₅₃]
            <;> ring
            <;> field_simp [h₁₃₁.ne']
            <;> ring
          rw [h₁₃₅₁]
    exact h₁₃₅
  
  have h₁₄ : x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) ≥ 3 / (a + b) := by
    calc
      x / (a * y + b * z) + y / (a * z + b * x) + z / (a * x + b * y) = (x^2 / (x * (a * y + b * z)) + y^2 / (y * (a * z + b * x)) + z^2 / (z * (a * x + b * y))) := by rw [h₁₁]
      _ ≥ (x + y + z)^2 / ((a + b) * (x * y + y * z + z * x)) := by linarith
      _ ≥ 3 / (a + b) := by linarith
  
  exact h₁₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_30 : ∀ (a b c : ℝ), a * b * c = -1 → a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) ≥ a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b := by
  intro a b c h_abc
  have h_a_ne_zero : a ≠ 0 := by
    by_contra h
    rw [h] at h_abc
    norm_num at h_abc ⊢
    <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { nlinarith })
  
  have h_b_ne_zero : b ≠ 0 := by
    by_contra h
    rw [h] at h_abc
    norm_num at h_abc ⊢
    <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { nlinarith })
  
  have h_c_ne_zero : c ≠ 0 := by
    by_contra h
    rw [h] at h_abc
    norm_num at h_abc ⊢
    <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { nlinarith })
  
  have h_sum_denominator_terms : (a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b) = - (a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)) := by
    have h1 : a ^ 2 / b = -a ^ 3 * c := by
      have h1 : a * b * c = -1 := h_abc
      have h2 : b ≠ 0 := h_b_ne_zero
      have h3 : a ≠ 0 := h_a_ne_zero
      have h4 : c ≠ 0 := h_c_ne_zero
      have h5 : 1 / b = -a * c := by
        have h6 : a * b * c = -1 := h_abc
        have h7 : a * c = -1 / b := by
          field_simp [h2] at h6 ⊢
          <;> nlinarith
        have h8 : 1 / b = -a * c := by
          have h9 : a * c = -1 / b := h7
          field_simp [h2] at h9 ⊢
          <;> nlinarith
        exact h8
      calc
        a ^ 2 / b = a ^ 2 * (1 / b) := by field_simp [h2]
        _ = a ^ 2 * (-a * c) := by rw [h5]
        _ = -a ^ 3 * c := by ring
    have h2 : a ^ 2 / c = -a ^ 3 * b := by
      have h1 : a * b * c = -1 := h_abc
      have h2 : c ≠ 0 := h_c_ne_zero
      have h3 : a ≠ 0 := h_a_ne_zero
      have h4 : b ≠ 0 := h_b_ne_zero
      have h5 : 1 / c = -a * b := by
        have h6 : a * b * c = -1 := h_abc
        have h7 : a * b = -1 / c := by
          field_simp [h2] at h6 ⊢
          <;> nlinarith
        have h8 : 1 / c = -a * b := by
          have h9 : a * b = -1 / c := h7
          field_simp [h2] at h9 ⊢
          <;> nlinarith
        exact h8
      calc
        a ^ 2 / c = a ^ 2 * (1 / c) := by field_simp [h2]
        _ = a ^ 2 * (-a * b) := by rw [h5]
        _ = -a ^ 3 * b := by ring
    have h3 : b ^ 2 / c = -b ^ 3 * a := by
      have h1 : a * b * c = -1 := h_abc
      have h2 : c ≠ 0 := h_c_ne_zero
      have h3 : b ≠ 0 := h_b_ne_zero
      have h4 : a ≠ 0 := h_a_ne_zero
      have h5 : 1 / c = -a * b := by
        have h6 : a * b * c = -1 := h_abc
        have h7 : a * b = -1 / c := by
          field_simp [h2] at h6 ⊢
          <;> nlinarith
        have h8 : 1 / c = -a * b := by
          have h9 : a * b = -1 / c := h7
          field_simp [h2] at h9 ⊢
          <;> nlinarith
        exact h8
      calc
        b ^ 2 / c = b ^ 2 * (1 / c) := by field_simp [h2]
        _ = b ^ 2 * (-a * b) := by rw [h5]
        _ = -b ^ 3 * a := by ring
    have h4 : b ^ 2 / a = -b ^ 3 * c := by
      have h1 : a * b * c = -1 := h_abc
      have h2 : a ≠ 0 := h_a_ne_zero
      have h3 : b ≠ 0 := h_b_ne_zero
      have h4 : c ≠ 0 := h_c_ne_zero
      have h5 : 1 / a = -b * c := by
        have h6 : a * b * c = -1 := h_abc
        have h7 : b * c = -1 / a := by
          field_simp [h2] at h6 ⊢
          <;> nlinarith
        have h8 : 1 / a = -b * c := by
          have h9 : b * c = -1 / a := h7
          field_simp [h2] at h9 ⊢
          <;> nlinarith
        exact h8
      calc
        b ^ 2 / a = b ^ 2 * (1 / a) := by field_simp [h2]
        _ = b ^ 2 * (-b * c) := by rw [h5]
        _ = -b ^ 3 * c := by ring
    have h5 : c ^ 2 / a = -c ^ 3 * b := by
      have h1 : a * b * c = -1 := h_abc
      have h2 : a ≠ 0 := h_a_ne_zero
      have h3 : c ≠ 0 := h_c_ne_zero
      have h4 : b ≠ 0 := h_b_ne_zero
      have h5 : 1 / a = -b * c := by
        have h6 : a * b * c = -1 := h_abc
        have h7 : b * c = -1 / a := by
          field_simp [h2] at h6 ⊢
          <;> nlinarith
        have h8 : 1 / a = -b * c := by
          have h9 : b * c = -1 / a := h7
          field_simp [h2] at h9 ⊢
          <;> nlinarith
        exact h8
      calc
        c ^ 2 / a = c ^ 2 * (1 / a) := by field_simp [h2]
        _ = c ^ 2 * (-b * c) := by rw [h5]
        _ = -c ^ 3 * b := by ring
    have h6 : c ^ 2 / b = -c ^ 3 * a := by
      have h1 : a * b * c = -1 := h_abc
      have h2 : b ≠ 0 := h_b_ne_zero
      have h3 : c ≠ 0 := h_c_ne_zero
      have h4 : a ≠ 0 := h_a_ne_zero
      have h5 : 1 / b = -a * c := by
        have h6 : a * b * c = -1 := h_abc
        have h7 : a * c = -1 / b := by
          field_simp [h2] at h6 ⊢
          <;> nlinarith
        have h8 : 1 / b = -a * c := by
          have h9 : a * c = -1 / b := h7
          field_simp [h2] at h9 ⊢
          <;> nlinarith
        exact h8
      calc
        c ^ 2 / b = c ^ 2 * (1 / b) := by field_simp [h2]
        _ = c ^ 2 * (-a * c) := by rw [h5]
        _ = -c ^ 3 * a := by ring
    calc
      (a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b) =
          (-a ^ 3 * c + -a ^ 3 * b + -b ^ 3 * a + -b ^ 3 * c + -c ^ 3 * b + -c ^ 3 * a) := by
        rw [h1, h2, h3, h4, h5, h6]
        <;> ring
      _ = - (a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)) := by
        ring
        <;>
        linarith
  
  have h_main_ineq : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) + (a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)) ≥ 0 := by
    have h₁ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) + (a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)) = (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + 3) := by
      ring_nf
      <;>
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    rw [h₁]
    have h₂ : a ^ 3 + b ^ 3 + c ^ 3 + 3 = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
      have h₃ : a * b * c = -1 := h_abc
      have h₄ : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
        ring_nf
      have h₅ : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = a ^ 3 + b ^ 3 + c ^ 3 + 3 := by
        rw [h₃]
        <;> ring_nf
        <;> linarith
      linarith
    rw [h₂]
    have h₃ : (a + b + c) * ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a)) ≥ 0 := by
      have h₄ : 0 ≤ (a + b + c) ^ 2 := sq_nonneg (a + b + c)
      have h₅ : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      nlinarith [sq_nonneg (a + b + c), mul_nonneg h₄ h₅]
    nlinarith
  
  have h_final : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) ≥ a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b := by
    have h₁ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) + (a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)) ≥ 0 := h_main_ineq
    have h₂ : (a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b) = - (a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)) := h_sum_denominator_terms
    have h₃ : a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a + b + c) ≥ a ^ 2 / b + a ^ 2 / c + b ^ 2 / c + b ^ 2 / a + c ^ 2 / a + c ^ 2 / b := by
      linarith
    exact h₃
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_example_35 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (2 * a / (b + c)) ^ (2 / 3) + (2 * b / (c + a)) ^ (2 / 3) + (2 * c / (a + b)) ^ (2 / 3) ≥ 3 := by
  have h_main : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (2 * a / (b + c)) ^ (2 / 3) + (2 * b / (c + a)) ^ (2 / 3) + (2 * c / (a + b)) ^ (2 / 3) ≥ 3 := by
    intro a b c h
    have h₁ : (2 * a / (b + c)) ^ (2 / 3) = 1 := by
      norm_num [pow_zero]
    have h₂ : (2 * b / (c + a)) ^ (2 / 3) = 1 := by
      norm_num [pow_zero]
    have h₃ : (2 * c / (a + b)) ^ (2 / 3) = 1 := by
      norm_num [pow_zero]
    have h₄ : (2 * a / (b + c)) ^ (2 / 3) + (2 * b / (c + a)) ^ (2 / 3) + (2 * c / (a + b)) ^ (2 / 3) = 3 := by
      rw [h₁, h₂, h₃]
      <;> norm_num
    linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_1 : ∀ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c → ((a + 2 * b) / (a + 2 * c)) ^ 3 + ((b + 2 * c) / (b + 2 * a)) ^ 3 + ((c + 2 * a) / (c + 2 * b)) ^ 3 ≥ 3 := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : ((a + 2 * b) / (a + 2 * c)) ^ 3 + ((b + 2 * c) / (b + 2 * a)) ^ 3 + ((c + 2 * a) / (c + 2 * b)) ^ 3 ≥ 3 := by
    -- Use the fact that t³ ≥ 3t - 2 for t > 0
    have h₅ : ∀ (t : ℝ), t > 0 → t ^ 3 ≥ 3 * t - 2 := by
      intro t ht
      nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 2), sq_nonneg (t - 2 / 3)]
    -- Apply the inequality to each term
    have h₆ : ((a + 2 * b) / (a + 2 * c)) ^ 3 ≥ 3 * ((a + 2 * b) / (a + 2 * c)) - 2 := by
      apply h₅
      apply div_pos
      · linarith
      · linarith
    have h₇ : ((b + 2 * c) / (b + 2 * a)) ^ 3 ≥ 3 * ((b + 2 * c) / (b + 2 * a)) - 2 := by
      apply h₅
      apply div_pos
      · linarith
      · linarith
    have h₈ : ((c + 2 * a) / (c + 2 * b)) ^ 3 ≥ 3 * ((c + 2 * a) / (c + 2 * b)) - 2 := by
      apply h₅
      apply div_pos
      · linarith
      · linarith
    -- Sum the inequalities
    have h₉ : ((a + 2 * b) / (a + 2 * c)) ^ 3 + ((b + 2 * c) / (b + 2 * a)) ^ 3 + ((c + 2 * a) / (c + 2 * b)) ^ 3 ≥ 3 * (((a + 2 * b) / (a + 2 * c)) + ((b + 2 * c) / (b + 2 * a)) + ((c + 2 * a) / (c + 2 * b))) - 6 := by
      linarith
    -- Prove that the sum of fractions is at least 3
    have h₁₀ : ((a + 2 * b) / (a + 2 * c)) + ((b + 2 * c) / (b + 2 * a)) + ((c + 2 * a) / (c + 2 * b)) ≥ 3 := by
      -- Use the fact that the sum of the fractions is at least 3
      field_simp [h₁.ne', h₂.ne', h₃.ne']
      rw [le_div_iff (by positivity), ← sub_nonneg]
      ring_nf
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
        mul_nonneg (sq_nonneg (a - b)) h₃.le, mul_nonneg (sq_nonneg (b - c)) h₁.le,
        mul_nonneg (sq_nonneg (c - a)) h₂.le]
    -- Combine the results to get the final inequality
    linarith
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_10 : ∀ (a b c : ℝ), ¬ (a = 0) ∧ ¬ (b = 0) ∧ ¬ (c = 0) → a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ a / c + c / b + b / a := by
  intro a b c h
  have h₁ : (a / b - b / c) ^ 2 = a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 - 2 * (a / c) := by
    have hb : b ≠ 0 := by tauto
    have hc : c ≠ 0 := by tauto
    have h₁ : (a / b - b / c) ^ 2 = (a / b) ^ 2 + (b / c) ^ 2 - 2 * (a / b) * (b / c) := by
      ring_nf
      <;> field_simp [hb, hc]
      <;> ring_nf
    rw [h₁]
    have h₂ : (a / b) ^ 2 = a ^ 2 / b ^ 2 := by
      field_simp [hb]
      <;> ring_nf
    have h₃ : (b / c) ^ 2 = b ^ 2 / c ^ 2 := by
      field_simp [hc]
      <;> ring_nf
    have h₄ : (a / b) * (b / c) = a / c := by
      field_simp [hb, hc]
      <;> ring_nf
    rw [h₂, h₃]
    have h₅ : 2 * (a / b) * (b / c) = 2 * (a / c) := by
      calc
        2 * (a / b) * (b / c) = 2 * ((a / b) * (b / c)) := by ring
        _ = 2 * (a / c) := by rw [h₄]
        _ = 2 * (a / c) := by ring
    linarith
  
  have h₂ : (b / c - c / a) ^ 2 = b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 - 2 * (b / a) := by
    have hb : b ≠ 0 := by tauto
    have hc : c ≠ 0 := by tauto
    have ha : a ≠ 0 := by tauto
    have h₂ : (b / c - c / a) ^ 2 = (b / c) ^ 2 + (c / a) ^ 2 - 2 * (b / c) * (c / a) := by
      ring_nf
      <;> field_simp [hb, hc, ha]
      <;> ring_nf
    rw [h₂]
    have h₃ : (b / c) ^ 2 = b ^ 2 / c ^ 2 := by
      field_simp [hc]
      <;> ring_nf
    have h₄ : (c / a) ^ 2 = c ^ 2 / a ^ 2 := by
      field_simp [ha]
      <;> ring_nf
    have h₅ : (b / c) * (c / a) = b / a := by
      field_simp [hb, hc, ha]
      <;> ring_nf
    rw [h₃, h₄]
    have h₆ : 2 * (b / c) * (c / a) = 2 * (b / a) := by
      calc
        2 * (b / c) * (c / a) = 2 * ((b / c) * (c / a)) := by ring
        _ = 2 * (b / a) := by rw [h₅]
        _ = 2 * (b / a) := by ring
    linarith
  
  have h₃ : (c / a - a / b) ^ 2 = c ^ 2 / a ^ 2 + a ^ 2 / b ^ 2 - 2 * (c / b) := by
    have hb : b ≠ 0 := by tauto
    have hc : c ≠ 0 := by tauto
    have ha : a ≠ 0 := by tauto
    have h₃ : (c / a - a / b) ^ 2 = (c / a) ^ 2 + (a / b) ^ 2 - 2 * (c / a) * (a / b) := by
      ring_nf
      <;> field_simp [ha, hb, hc]
      <;> ring_nf
    rw [h₃]
    have h₄ : (c / a) ^ 2 = c ^ 2 / a ^ 2 := by
      field_simp [ha]
      <;> ring_nf
    have h₅ : (a / b) ^ 2 = a ^ 2 / b ^ 2 := by
      field_simp [hb]
      <;> ring_nf
    have h₆ : (c / a) * (a / b) = c / b := by
      field_simp [ha, hb]
      <;> ring_nf
      <;> simp_all
      <;> field_simp [ha, hb]
      <;> ring_nf
    rw [h₄, h₅]
    have h₇ : 2 * (c / a) * (a / b) = 2 * (c / b) := by
      calc
        2 * (c / a) * (a / b) = 2 * ((c / a) * (a / b)) := by ring
        _ = 2 * (c / b) := by rw [h₆]
        _ = 2 * (c / b) := by ring
    linarith
  
  have h₄ : 2 * (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2) - 2 * (a / c + b / a + c / b) ≥ 0 := by
    have h₅ : 0 ≤ (a / b - b / c) ^ 2 := sq_nonneg _
    have h₆ : 0 ≤ (b / c - c / a) ^ 2 := sq_nonneg _
    have h₇ : 0 ≤ (c / a - a / b) ^ 2 := sq_nonneg _
    have h₈ : (a / b - b / c) ^ 2 + (b / c - c / a) ^ 2 + (c / a - a / b) ^ 2 ≥ 0 := by linarith
    have h₉ : (a / b - b / c) ^ 2 + (b / c - c / a) ^ 2 + (c / a - a / b) ^ 2 = 2 * (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2) - 2 * (a / c + b / a + c / b) := by
      calc
        (a / b - b / c) ^ 2 + (b / c - c / a) ^ 2 + (c / a - a / b) ^ 2 = (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 - 2 * (a / c)) + (b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 - 2 * (b / a)) + (c ^ 2 / a ^ 2 + a ^ 2 / b ^ 2 - 2 * (c / b)) := by
          rw [h₁, h₂, h₃]
          <;> ring_nf
        _ = 2 * (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2) - 2 * (a / c + b / a + c / b) := by
          ring_nf
          <;> field_simp [h.1, h.2.1, h.2.2]
          <;> ring_nf
          <;> linarith
    linarith
  
  have h₅ : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ a / c + c / b + b / a := by
    have h₅₁ : a / c + c / b + b / a = a / c + b / a + c / b := by
      ring
    rw [h₅₁]
    have h₅₂ : 2 * (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2) - 2 * (a / c + b / a + c / b) ≥ 0 := h₄
    have h₅₃ : 2 * (a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2) ≥ 2 * (a / c + b / a + c / b) := by linarith
    have h₅₄ : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ a / c + b / a + c / b := by
      linarith
    linarith
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_15 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
  have h_main_ineq : ∀ (a b : ℝ), a > 0 → b > 0 → a ^ 3 + b ^ 3 ≥ a * b * (a + b) := by
    intro a b ha hb
    have h₁ : 0 ≤ (a - b) ^ 2 := by nlinarith
    have h₂ : 0 < a + b := by nlinarith
    have h₃ : 0 ≤ (a - b) ^ 2 * (a + b) := by positivity
    have h₄ : (a - b) ^ 2 * (a + b) = a ^ 3 + b ^ 3 - a * b * (a + b) := by
      ring_nf
      <;>
      nlinarith [sq_nonneg (a - b)]
    have h₅ : a ^ 3 + b ^ 3 - a * b * (a + b) ≥ 0 := by
      linarith
    linarith
  
  intro a b c h
  have ha : a > 0 := by linarith
  have hb : b > 0 := by linarith
  have hc : c > 0 := by linarith
  have h₁ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
    have h₂ : a ^ 3 + b ^ 3 ≥ a * b * (a + b) := h_main_ineq a b ha hb
    have h₃ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b) + a * b * c := by linarith
    have h₄ : a * b * (a + b) + a * b * c = a * b * (a + b + c) := by ring
    have h₅ : a ^ 3 + b ^ 3 + a * b * c ≥ a * b * (a + b + c) := by linarith
    have h₆ : 0 < a ^ 3 + b ^ 3 + a * b * c := by
      have h₇ : 0 < a := ha
      have h₈ : 0 < b := hb
      have h₉ : 0 < c := hc
      positivity
    have h₇ : 0 < a * b * (a + b + c) := by positivity
    have h₈ : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₈
  have h₂ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
    have h₃ : b ^ 3 + c ^ 3 ≥ b * c * (b + c) := h_main_ineq b c hb hc
    have h₄ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (b + c) + a * b * c := by linarith
    have h₅ : b * c * (b + c) + a * b * c = b * c * (a + b + c) := by ring
    have h₆ : b ^ 3 + c ^ 3 + a * b * c ≥ b * c * (a + b + c) := by linarith
    have h₇ : 0 < b ^ 3 + c ^ 3 + a * b * c := by positivity
    have h₈ : 0 < b * c * (a + b + c) := by positivity
    have h₉ : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ 1 / (b * c * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₉
  have h₃ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
    have h₄ : c ^ 3 + a ^ 3 ≥ c * a * (c + a) := h_main_ineq c a hc ha
    have h₅ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (c + a) + a * b * c := by linarith
    have h₆ : c * a * (c + a) + a * b * c = c * a * (a + b + c) := by ring
    have h₇ : c ^ 3 + a ^ 3 + a * b * c ≥ c * a * (a + b + c) := by linarith
    have h₈ : 0 < c ^ 3 + a ^ 3 + a * b * c := by positivity
    have h₉ : 0 < c * a * (a + b + c) := by positivity
    have h₁₀ : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (c * a * (a + b + c)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    exact h₁₀
  have h₄ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    have h₅ : 0 < a * b := by positivity
    have h₆ : 0 < b * c := by positivity
    have h₇ : 0 < c * a := by positivity
    have h₈ : 0 < a * b * c := by positivity
    have h₉ : 0 < a + b + c := by positivity
    have h₁₀ : 0 < a * b * (a + b + c) := by positivity
    have h₁₁ : 0 < b * c * (a + b + c) := by positivity
    have h₁₂ : 0 < c * a * (a + b + c) := by positivity
    calc
      1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = (c + a + b) / (a * b * c * (a + b + c)) := by
        field_simp [h₅, h₆, h₇, h₈, h₉]
        <;> ring
        <;> field_simp [h₅, h₆, h₇, h₈, h₉]
        <;> ring
      _ = 1 / (a * b * c) := by
        have h₁₃ : (c + a + b : ℝ) = (a + b + c : ℝ) := by ring
        rw [h₁₃]
        field_simp [h₈, h₉]
        <;> ring
        <;> field_simp [h₈, h₉]
        <;> ring
  have h₅ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) := by
    linarith [h₁, h₂, h₃]
  have h₆ : 1 / (a * b * (a + b + c)) + 1 / (b * c * (a + b + c)) + 1 / (c * a * (a + b + c)) = 1 / (a * b * c) := by
    exact h₄
  have h₇ : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) + 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by
    linarith
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_19 : ∀ (a b c : ℝ), a + b + c = 1 ∧ a ≥ -3 / 4 ∧ b ≥ -3 / 4 ∧ c ≥ -3 / 4 → a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 9 / 10 := by
  intro a b c h
  have h₁ : ∀ (x : ℝ), x ≥ -3 / 4 → x / (x ^ 2 + 1) ≤ (18 / 25 : ℝ) * x + 3 / 50 := by
    intro x hx
    have h₂ : (36 : ℝ) * x ^ 3 + 3 * x ^ 2 - 14 * x + 3 ≥ 0 := by
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x + 7 / 18),
        sq_nonneg (x + 3 / 4), mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (x - 1 / 3)),
        mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (x + 7 / 18))]
    have h₃ : 0 < (x ^ 2 + 1 : ℝ) := by nlinarith
    have h₄ : (18 / 25 : ℝ) * x + 3 / 50 - x / (x ^ 2 + 1) ≥ 0 := by
      field_simp [h₃.ne']
      rw [le_div_iff (by positivity)]
      nlinarith [h₂]
    linarith
  have h₂ : a / (a ^ 2 + 1) ≤ (18 / 25 : ℝ) * a + 3 / 50 := by
    have h₃ : a ≥ -3 / 4 := by linarith
    have h₄ : a / (a ^ 2 + 1) ≤ (18 / 25 : ℝ) * a + 3 / 50 := h₁ a h₃
    exact h₄
  have h₃ : b / (b ^ 2 + 1) ≤ (18 / 25 : ℝ) * b + 3 / 50 := by
    have h₄ : b ≥ -3 / 4 := by linarith
    have h₅ : b / (b ^ 2 + 1) ≤ (18 / 25 : ℝ) * b + 3 / 50 := h₁ b h₄
    exact h₅
  have h₄ : c / (c ^ 2 + 1) ≤ (18 / 25 : ℝ) * c + 3 / 50 := by
    have h₅ : c ≥ -3 / 4 := by linarith
    have h₆ : c / (c ^ 2 + 1) ≤ (18 / 25 : ℝ) * c + 3 / 50 := h₁ c h₅
    exact h₆
  have h₅ : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ (18 / 25 : ℝ) * (a + b + c) + 9 / 50 := by
    have h₆ : a / (a ^ 2 + 1) ≤ (18 / 25 : ℝ) * a + 3 / 50 := h₂
    have h₇ : b / (b ^ 2 + 1) ≤ (18 / 25 : ℝ) * b + 3 / 50 := h₃
    have h₈ : c / (c ^ 2 + 1) ≤ (18 / 25 : ℝ) * c + 3 / 50 := h₄
    linarith
  have h₆ : (18 / 25 : ℝ) * (a + b + c) + 9 / 50 = 9 / 10 := by
    have h₇ : a + b + c = 1 := by linarith
    rw [h₇]
    <;> norm_num
  have h₇ : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 9 / 10 := by
    linarith
  exact h₇

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem thomas_problem_24_left : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 < a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) := by
  have h_main : ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → 1 < a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) := by
    intro a b c ha hb hc
    have h₁ : a / Real.sqrt (a ^ 2 + b ^ 2) > a / (a + b) := by
      have h₁₀ : 0 < a := ha
      have h₁₁ : 0 < b := hb
      have h₁₂ : 0 < a + b := by linarith
      have h₁₃ : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h₁₄ : Real.sqrt (a ^ 2 + b ^ 2) < a + b := by
        have h₁₄₁ : 0 < a + b := by linarith
        have h₁₄₂ : 0 < a * b := by positivity
        have h₁₄₃ : (a + b) ^ 2 > a ^ 2 + b ^ 2 := by
          nlinarith [sq_nonneg (a - b)]
        have h₁₄₄ : Real.sqrt (a ^ 2 + b ^ 2) < a + b := by
          apply Real.sqrt_lt' (by positivity) |>.mpr
          nlinarith
        exact h₁₄₄
      have h₁₅ : 0 < a + b := by linarith
      have h₁₆ : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr (by positivity)
      -- Use the fact that the denominator on the LHS is smaller to show the fraction is larger
      have h₁₇ : a / Real.sqrt (a ^ 2 + b ^ 2) > a / (a + b) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h₁₄]
      exact h₁₇
    have h₂ : b / Real.sqrt (b ^ 2 + c ^ 2) > b / (b + c) := by
      have h₂₀ : 0 < b := hb
      have h₂₁ : 0 < c := hc
      have h₂₂ : 0 < b + c := by linarith
      have h₂₃ : 0 < Real.sqrt (b ^ 2 + c ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h₂₄ : Real.sqrt (b ^ 2 + c ^ 2) < b + c := by
        have h₂₄₁ : 0 < b + c := by linarith
        have h₂₄₂ : 0 < b * c := by positivity
        have h₂₄₃ : (b + c) ^ 2 > b ^ 2 + c ^ 2 := by
          nlinarith [sq_nonneg (b - c)]
        have h₂₄₄ : Real.sqrt (b ^ 2 + c ^ 2) < b + c := by
          apply Real.sqrt_lt' (by positivity) |>.mpr
          nlinarith
        exact h₂₄₄
      have h₂₅ : 0 < b + c := by linarith
      have h₂₆ : 0 < Real.sqrt (b ^ 2 + c ^ 2) := Real.sqrt_pos.mpr (by positivity)
      -- Use the fact that the denominator on the LHS is smaller to show the fraction is larger
      have h₂₇ : b / Real.sqrt (b ^ 2 + c ^ 2) > b / (b + c) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h₂₄]
      exact h₂₇
    have h₃ : c / Real.sqrt (c ^ 2 + a ^ 2) > c / (c + a) := by
      have h₃₀ : 0 < c := hc
      have h₃₁ : 0 < a := ha
      have h₃₂ : 0 < c + a := by linarith
      have h₃₃ : 0 < Real.sqrt (c ^ 2 + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h₃₄ : Real.sqrt (c ^ 2 + a ^ 2) < c + a := by
        have h₃₄₁ : 0 < c + a := by linarith
        have h₃₄₂ : 0 < c * a := by positivity
        have h₃₄₃ : (c + a) ^ 2 > c ^ 2 + a ^ 2 := by
          nlinarith [sq_nonneg (c - a)]
        have h₃₄₄ : Real.sqrt (c ^ 2 + a ^ 2) < c + a := by
          apply Real.sqrt_lt' (by positivity) |>.mpr
          nlinarith
        exact h₃₄₄
      have h₃₅ : 0 < c + a := by linarith
      have h₃₆ : 0 < Real.sqrt (c ^ 2 + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
      -- Use the fact that the denominator on the LHS is smaller to show the fraction is larger
      have h₃₇ : c / Real.sqrt (c ^ 2 + a ^ 2) > c / (c + a) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h₃₄]
      exact h₃₇
    have h₄ : a / (a + b) + b / (b + c) + c / (c + a) > 1 := by
      have h₄₁ : 0 < a := ha
      have h₄₂ : 0 < b := hb
      have h₄₃ : 0 < c := hc
      have h₄₄ : 0 < a + b + c := by positivity
      have h₄₅ : a / (a + b) > a / (a + b + c) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h₄₆ : b / (b + c) > b / (a + b + c) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h₄₇ : c / (c + a) > c / (a + b + c) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h₄₈ : a / (a + b) + b / (b + c) + c / (c + a) > a / (a + b + c) + b / (a + b + c) + c / (a + b + c) := by
        linarith
      have h₄₉ : a / (a + b + c) + b / (a + b + c) + c / (a + b + c) = 1 := by
        field_simp [h₄₄.ne']
        <;> ring
        <;> field_simp [h₄₄.ne']
        <;> linarith
      linarith
    have h₅ : a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) > 1 := by
      calc
        a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) > a / (a + b) + b / (b + c) + c / (c + a) := by
          linarith [h₁, h₂, h₃]
        _ > 1 := by linarith [h₄]
    linarith [h₅]
  
  intro a b c h
  have h₁ : a > 0 := h.1
  have h₂ : b > 0 := h.2.1
  have h₃ : c > 0 := h.2.2
  have h₄ : 1 < a / Real.sqrt (a ^ 2 + b ^ 2) + b / Real.sqrt (b ^ 2 + c ^ 2) + c / Real.sqrt (c ^ 2 + a ^ 2) := h_main a b c h₁ h₂ h₃
  exact h₄
