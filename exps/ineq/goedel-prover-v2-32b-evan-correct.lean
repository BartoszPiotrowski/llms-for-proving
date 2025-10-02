
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_1_2_left : ∀ (a b c : ℝ), a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  intro a b c
  have h_main : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h_expand : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try nlinarith)
    <;>
    (try ring_nf at *) <;>
    (try nlinarith)
  
  have h_nonneg : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
    have h₁ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := h_main
    have h₂ : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := h_expand
    have h₃ : 0 ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by linarith
    -- Divide both sides by 2 to get the desired inequality
    have h₄ : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
      linarith
    exact h₄
  
  have h_final : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₁ : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := h_nonneg
    -- Rearrange the inequality to the desired form
    have h₂ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
      linarith
    exact h₂
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_1_2_right : ∀ (a b c : ℝ), a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
  intro a b c
  have h₁ : a ^ 4 + b ^ 4 ≥ 2 * (a ^ 2 * b ^ 2) := by
    have h₁₀ : 0 ≤ (a ^ 2 - b ^ 2) ^ 2 := sq_nonneg _
    have h₁₁ : (a ^ 2 - b ^ 2) ^ 2 = a ^ 4 - 2 * (a ^ 2 * b ^ 2) + b ^ 4 := by
      ring
    nlinarith
  
  have h₂ : b ^ 4 + c ^ 4 ≥ 2 * (b ^ 2 * c ^ 2) := by
    have h₂₀ : 0 ≤ (b ^ 2 - c ^ 2) ^ 2 := sq_nonneg _
    have h₂₁ : (b ^ 2 - c ^ 2) ^ 2 = b ^ 4 - 2 * (b ^ 2 * c ^ 2) + c ^ 4 := by
      ring
    nlinarith
  
  have h₃ : c ^ 4 + a ^ 4 ≥ 2 * (c ^ 2 * a ^ 2) := by
    have h₃₀ : 0 ≤ (c ^ 2 - a ^ 2) ^ 2 := sq_nonneg _
    have h₃₁ : (c ^ 2 - a ^ 2) ^ 2 = c ^ 4 - 2 * (c ^ 2 * a ^ 2) + a ^ 4 := by
      ring
    nlinarith
  
  have h₄ : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
    have h₄₁ : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := by
      nlinarith [h₁, h₂, h₃]
    exact h₄₁
  
  have h₅ : (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  
  have h₆ : 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b)) ≥ 0 := by
    have h₆₁ : (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 = 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b)) := by
      ring
    have h₆₂ : (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 ≥ 0 := h₅
    linarith
  
  have h₇ : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
    have h₇₁ : 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b)) ≥ 0 := h₆
    have h₇₂ : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) ≥ 0 := by
      linarith
    linarith
  
  have h₈ : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
    have h₈₁ : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 := h₄
    have h₈₂ : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := h₇
    linarith
  
  exact h₈

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_exercise_1_3 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
  intro a b c h
  have h₁ : 2 * a ^ 3 + b ^ 3 ≥ 3 * a ^ 2 * b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg h.1 h.2.1, mul_nonneg (sq_nonneg (a - b)) h.1,
      mul_nonneg (sq_nonneg (a - b)) h.2.1]
  
  have h₂ : 2 * b ^ 3 + c ^ 3 ≥ 3 * b ^ 2 * c := by
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), mul_nonneg h.2.1 h.2.2, mul_nonneg (sq_nonneg (b - c)) h.2.1,
      mul_nonneg (sq_nonneg (b - c)) h.2.2]
  
  have h₃ : 2 * c ^ 3 + a ^ 3 ≥ 3 * c ^ 2 * a := by
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), mul_nonneg h.2.2 h.1, mul_nonneg (sq_nonneg (c - a)) h.2.2,
      mul_nonneg (sq_nonneg (c - a)) h.1]
  
  have h_sum : 3 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
    have h₄ : 3 * (a ^ 3 + b ^ 3 + c ^ 3) = (2 * a ^ 3 + b ^ 3) + (2 * b ^ 3 + c ^ 3) + (2 * c ^ 3 + a ^ 3) := by ring
    have h₅ : 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) = (3 * a ^ 2 * b) + (3 * b ^ 2 * c) + (3 * c ^ 2 * a) := by ring
    have h₆ : (2 * a ^ 3 + b ^ 3) + (2 * b ^ 3 + c ^ 3) + (2 * c ^ 3 + a ^ 3) ≥ (3 * a ^ 2 * b) + (3 * b ^ 2 * c) + (3 * c ^ 2 * a) := by
      linarith
    linarith
  
  have h_final : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
    have h₄ : 3 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := h_sum
    have h₅ : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a := by
      linarith
    exact h₅
  
  exact h_final

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_exercise_1_4_left : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
  have h_main : ∀ (a b c : ℝ), a ≥ 0 → b ≥ 0 → c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
    intro a b c ha hb hc
    have h₁ : 0 ≤ a * b := mul_nonneg ha hb
    have h₂ : 0 ≤ a * c := mul_nonneg ha hc
    have h₃ : 0 ≤ b * c := mul_nonneg hb hc
    have h₄ : 0 ≤ a ^ 3 := pow_nonneg ha 3
    have h₅ : 0 ≤ b ^ 3 := pow_nonneg hb 3
    have h₆ : 0 ≤ c ^ 3 := pow_nonneg hc 3
    have h₇ : 0 ≤ a ^ 2 := pow_nonneg ha 2
    have h₈ : 0 ≤ b ^ 2 := pow_nonneg hb 2
    have h₉ : 0 ≤ c ^ 2 := pow_nonneg hc 2
    -- Step 1: Prove that a⁵ + b⁵ ≥ a³b² + a²b³
    have h₁₀ : a ^ 5 + b ^ 5 ≥ a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha (sq_nonneg (a - b)), mul_nonneg hb (sq_nonneg (a - b)),
        mul_nonneg (sq_nonneg a) (sq_nonneg b), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b)),
        mul_nonneg (sq_nonneg (a + b)) (sq_nonneg (a - b))]
    have h₁₁ : a ^ 5 + c ^ 5 ≥ a ^ 3 * c ^ 2 + a ^ 2 * c ^ 3 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), mul_nonneg ha (sq_nonneg (a - c)), mul_nonneg hc (sq_nonneg (a - c)),
        mul_nonneg (sq_nonneg a) (sq_nonneg c), mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (a + c)),
        mul_nonneg (sq_nonneg (a + c)) (sq_nonneg (a - c))]
    have h₁₂ : b ^ 5 + c ^ 5 ≥ b ^ 3 * c ^ 2 + b ^ 2 * c ^ 3 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), mul_nonneg hb (sq_nonneg (b - c)), mul_nonneg hc (sq_nonneg (b - c)),
        mul_nonneg (sq_nonneg b) (sq_nonneg c), mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c)),
        mul_nonneg (sq_nonneg (b + c)) (sq_nonneg (b - c))]
    -- Step 2: Sum over pairs to get 2(a⁵ + b⁵ + c⁵) ≥ Σ(a³b² + a²b³)
    have h₁₃ : 2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a ^ 3 * c ^ 2 + a ^ 2 * c ^ 3 + b ^ 3 * c ^ 2 + b ^ 2 * c ^ 3 := by
      linarith [h₁₀, h₁₁, h₁₂]
    -- Step 3: Prove that a³b² + a³c² ≥ 2a³bc
    have h₁₄ : a ^ 3 * b ^ 2 + a ^ 3 * c ^ 2 ≥ 2 * a ^ 3 * b * c := by
      have h₁₄₁ : 0 ≤ a ^ 3 := pow_nonneg ha 3
      have h₁₄₂ : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
      nlinarith [sq_nonneg (b - c), mul_nonneg h₁₄₁ h₁₄₂]
    have h₁₅ : b ^ 3 * a ^ 2 + b ^ 3 * c ^ 2 ≥ 2 * b ^ 3 * a * c := by
      have h₁₅₁ : 0 ≤ b ^ 3 := pow_nonneg hb 3
      have h₁₅₂ : 0 ≤ (a - c) ^ 2 := sq_nonneg (a - c)
      nlinarith [sq_nonneg (a - c), mul_nonneg h₁₅₁ h₁₅₂]
    have h₁₆ : c ^ 3 * a ^ 2 + c ^ 3 * b ^ 2 ≥ 2 * c ^ 3 * a * b := by
      have h₁₆₁ : 0 ≤ c ^ 3 := pow_nonneg hc 3
      have h₁₆₂ : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
      nlinarith [sq_nonneg (a - b), mul_nonneg h₁₆₁ h₁₆₂]
    -- Step 4: Summing the inequalities over all pairs to get Σ(a³b² + a³c²) ≥ 2Σ(a³bc)
    have h₁₇ : a ^ 3 * b ^ 2 + a ^ 3 * c ^ 2 + b ^ 3 * a ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2 + c ^ 3 * b ^ 2 ≥ 2 * (a ^ 3 * b * c + b ^ 3 * a * c + c ^ 3 * a * b) := by
      have h₁₇₁ : a ^ 3 * b ^ 2 + a ^ 3 * c ^ 2 ≥ 2 * a ^ 3 * b * c := h₁₄
      have h₁₇₂ : b ^ 3 * a ^ 2 + b ^ 3 * c ^ 2 ≥ 2 * b ^ 3 * a * c := h₁₅
      have h₁₇₃ : c ^ 3 * a ^ 2 + c ^ 3 * b ^ 2 ≥ 2 * c ^ 3 * a * b := h₁₆
      nlinarith [h₁₇₁, h₁₇₂, h₁₇₃]
    -- Step 5: Combine the two inequalities to get the result
    have h₁₈ : a ^ 3 * b ^ 2 + a ^ 3 * c ^ 2 + b ^ 3 * a ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2 + c ^ 3 * b ^ 2 = a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a ^ 3 * c ^ 2 + a ^ 2 * c ^ 3 + b ^ 3 * c ^ 2 + b ^ 2 * c ^ 3 := by
      ring
    have h₁₉ : 2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ 2 * (a ^ 3 * b * c + b ^ 3 * a * c + c ^ 3 * a * b) := by
      calc
        2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a ^ 3 * c ^ 2 + a ^ 2 * c ^ 3 + b ^ 3 * c ^ 2 + b ^ 2 * c ^ 3 := by linarith [h₁₃]
        _ = a ^ 3 * b ^ 2 + a ^ 3 * c ^ 2 + b ^ 3 * a ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2 + c ^ 3 * b ^ 2 := by linarith [h₁₈]
        _ ≥ 2 * (a ^ 3 * b * c + b ^ 3 * a * c + c ^ 3 * a * b) := by linarith [h₁₇]
    have h₂₀ : a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b := by
      have h₂₀₁ : 2 * (a ^ 5 + b ^ 5 + c ^ 5) ≥ 2 * (a ^ 3 * b * c + b ^ 3 * a * c + c ^ 3 * a * b) := h₁₉
      have h₂₀₂ : a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 * b * c + b ^ 3 * a * c + c ^ 3 * a * b := by linarith
      have h₂₀₃ : b ^ 3 * a * c = b ^ 3 * c * a := by ring
      have h₂₀₄ : c ^ 3 * a * b = c ^ 3 * b * a := by ring
      have h₂₀₅ : a ^ 3 * b * c + b ^ 3 * c * a + c ^ 3 * a * b = a ^ 3 * b * c + b ^ 3 * a * c + c ^ 3 * a * b := by
        ring_nf
        <;>
        (try simp_all [mul_assoc, mul_comm, mul_left_comm])
        <;>
        (try nlinarith)
      linarith
    exact h₂₀
  intro a b c h
  have h₁ : a ≥ 0 := h.1
  have h₂ : b ≥ 0 := h.2.1
  have h₃ : c ≥ 0 := h.2.2
  exact h_main a b c h₁ h₂ h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_exercise_1_4_right : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≥ a * b * c * (a * b + b * c + c * a) := by
  intro a b c h
  have h₁ : a ^ 5 + b ^ 5 + c ^ 5 ≥ a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h.1 h.2.1, mul_nonneg h.2.1 h.2.2, mul_nonneg h.2.2 h.1,
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      mul_nonneg (sq_nonneg (a - b)) h.1, mul_nonneg (sq_nonneg (b - c)) h.2.1,
      mul_nonneg (sq_nonneg (c - a)) h.2.2, mul_nonneg (sq_nonneg (a - b)) h.2.1,
      mul_nonneg (sq_nonneg (b - c)) h.2.2, mul_nonneg (sq_nonneg (c - a)) h.1,
      mul_nonneg (sq_nonneg (a + b)) h.2.2, mul_nonneg (sq_nonneg (b + c)) h.1,
      mul_nonneg (sq_nonneg (c + a)) h.2.1]
  
  have h₂ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h₃ : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₃ : a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a * b * c * (a * b + b * c + c * a) := by
    have h₄ : 0 ≤ a * b * c := by
      have h₅ : 0 ≤ a := by linarith
      have h₆ : 0 ≤ b := by linarith
      have h₇ : 0 ≤ c := by linarith
      positivity
    have h₅ : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := h₂
    have h₆ : a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a * b * c * (a * b + b * c + c * a) := by
      have h₇ : a * b * c ≥ 0 := by
        have h₈ : 0 ≤ a := by linarith
        have h₉ : 0 ≤ b := by linarith
        have h₁₀ : 0 ≤ c := by linarith
        positivity
      nlinarith
    exact h₆
  
  have h₄ : a ^ 5 + b ^ 5 + c ^ 5 ≥ a * b * c * (a * b + b * c + c * a) := by
    linarith
  
  exact h₄

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_practice_problem_1 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → a ^ 7 + b ^ 7 + c ^ 7 ≥ a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3 := by
  intro a b c h
  have h₁ : 4 * a ^ 7 + 3 * b ^ 7 ≥ 7 * a ^ 4 * b ^ 3 := by
    have h₁₁ : 0 ≤ a := by linarith
    have h₁₂ : 0 ≤ b := by linarith
    have h₁₃ : 0 ≤ a ^ 4 := by positivity
    have h₁₄ : 0 ≤ b ^ 3 := by positivity
    have h₁₅ : 0 ≤ a ^ 7 := by positivity
    have h₁₆ : 0 ≤ b ^ 7 := by positivity
    have h₁₇ : 0 ≤ a ^ 4 * b ^ 3 := by positivity
    -- Use nlinarith to prove the inequality using AM-GM
    nlinarith [sq_nonneg (a ^ 3 - b ^ 3), sq_nonneg (a ^ 2 - a * b), sq_nonneg (a * b - b ^ 2),
      sq_nonneg (a ^ 3 - a ^ 2 * b), sq_nonneg (a ^ 2 * b - a * b ^ 2),
      sq_nonneg (a * b ^ 2 - b ^ 3), mul_nonneg h₁₁ h₁₂,
      mul_nonneg (sq_nonneg (a ^ 2 - b ^ 2)) (pow_nonneg h₁₁ 2),
      mul_nonneg (sq_nonneg (a ^ 2 - a * b)) (pow_nonneg h₁₂ 2),
      mul_nonneg (sq_nonneg (a * b - b ^ 2)) (pow_nonneg h₁₁ 2)]
  
  have h₂ : 4 * b ^ 7 + 3 * c ^ 7 ≥ 7 * b ^ 4 * c ^ 3 := by
    have h₂₁ : 0 ≤ b := by linarith
    have h₂₂ : 0 ≤ c := by linarith
    have h₂₃ : 0 ≤ b ^ 4 := by positivity
    have h₂₄ : 0 ≤ c ^ 3 := by positivity
    have h₂₅ : 0 ≤ b ^ 7 := by positivity
    have h₂₆ : 0 ≤ c ^ 7 := by positivity
    have h₂₇ : 0 ≤ b ^ 4 * c ^ 3 := by positivity
    -- Use nlinarith to prove the inequality using AM-GM
    nlinarith [sq_nonneg (b ^ 3 - c ^ 3), sq_nonneg (b ^ 2 - b * c), sq_nonneg (b * c - c ^ 2),
      sq_nonneg (b ^ 3 - b ^ 2 * c), sq_nonneg (b ^ 2 * c - b * c ^ 2),
      sq_nonneg (b * c ^ 2 - c ^ 3), mul_nonneg h₂₁ h₂₂,
      mul_nonneg (sq_nonneg (b ^ 2 - c ^ 2)) (pow_nonneg h₂₁ 2),
      mul_nonneg (sq_nonneg (b ^ 2 - b * c)) (pow_nonneg h₂₂ 2),
      mul_nonneg (sq_nonneg (b * c - c ^ 2)) (pow_nonneg h₂₁ 2)]
  
  have h₃ : 4 * c ^ 7 + 3 * a ^ 7 ≥ 7 * c ^ 4 * a ^ 3 := by
    have h₃₁ : 0 ≤ c := by linarith
    have h₃₂ : 0 ≤ a := by linarith
    have h₃₃ : 0 ≤ c ^ 4 := by positivity
    have h₃₄ : 0 ≤ a ^ 3 := by positivity
    have h₃₅ : 0 ≤ c ^ 7 := by positivity
    have h₃₆ : 0 ≤ a ^ 7 := by positivity
    have h₃₇ : 0 ≤ c ^ 4 * a ^ 3 := by positivity
    -- Use nlinarith to prove the inequality using AM-GM
    nlinarith [sq_nonneg (c ^ 3 - a ^ 3), sq_nonneg (c ^ 2 - c * a), sq_nonneg (c * a - a ^ 2),
      sq_nonneg (c ^ 3 - c ^ 2 * a), sq_nonneg (c ^ 2 * a - c * a ^ 2),
      sq_nonneg (c * a ^ 2 - a ^ 3), mul_nonneg h₃₁ h₃₂,
      mul_nonneg (sq_nonneg (c ^ 2 - a ^ 2)) (pow_nonneg h₃₁ 2),
      mul_nonneg (sq_nonneg (c ^ 2 - c * a)) (pow_nonneg h₃₂ 2),
      mul_nonneg (sq_nonneg (c * a - a ^ 2)) (pow_nonneg h₃₁ 2)]
  
  have h₄ : 7 * (a ^ 7 + b ^ 7 + c ^ 7) ≥ 7 * (a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3) := by
    have h₄₁ : 4 * a ^ 7 + 3 * b ^ 7 + (4 * b ^ 7 + 3 * c ^ 7) + (4 * c ^ 7 + 3 * a ^ 7) ≥ 7 * a ^ 4 * b ^ 3 + 7 * b ^ 4 * c ^ 3 + 7 * c ^ 4 * a ^ 3 := by
      linarith
    have h₄₂ : 7 * (a ^ 7 + b ^ 7 + c ^ 7) = 4 * a ^ 7 + 3 * b ^ 7 + (4 * b ^ 7 + 3 * c ^ 7) + (4 * c ^ 7 + 3 * a ^ 7) := by
      ring
    have h₄₃ : 7 * (a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3) = 7 * a ^ 4 * b ^ 3 + 7 * b ^ 4 * c ^ 3 + 7 * c ^ 4 * a ^ 3 := by
      ring
    linarith
  
  have h₅ : a ^ 7 + b ^ 7 + c ^ 7 ≥ a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3 := by
    have h₅₁ : 7 * (a ^ 7 + b ^ 7 + c ^ 7) ≥ 7 * (a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3) := h₄
    -- Divide both sides by 7 to get the desired inequality
    have h₅₂ : a ^ 7 + b ^ 7 + c ^ 7 ≥ a ^ 4 * b ^ 3 + b ^ 4 * c ^ 3 + c ^ 4 * a ^ 3 := by
      linarith
    exact h₅₂
  
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_2_4_left : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / a + 1 / b + 1 / c ≥ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  intro a b c h
  have h₁ : 1 / a + 1 / b ≥ 4 / (a + b) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < a + b := by linarith
    have h₁₄ : 0 < a * b := by positivity
    have h₁₅ : 0 < a * b * (a + b) := by positivity
    field_simp [h₁₁.ne', h₁₂.ne', h₁₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b)]

  have h₂ : 1 / b + 1 / c ≥ 4 / (b + c) := by
    have h₂₁ : 0 < b := by linarith
    have h₂₂ : 0 < c := by linarith
    have h₂₃ : 0 < b + c := by linarith
    have h₂₄ : 0 < b * c := by positivity
    have h₂₅ : 0 < b * c * (b + c) := by positivity
    field_simp [h₂₁.ne', h₂₂.ne', h₂₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (b - c)]

  have h₃ : 1 / c + 1 / a ≥ 4 / (c + a) := by
    have h₃₁ : 0 < c := by linarith
    have h₃₂ : 0 < a := by linarith
    have h₃₃ : 0 < c + a := by linarith
    have h₃₄ : 0 < c * a := by positivity
    have h₃₅ : 0 < c * a * (c + a) := by positivity
    field_simp [h₃₁.ne', h₃₂.ne', h₃₃.ne']
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (c - a)]

  have h₄ : 2 * (1 / a + 1 / b + 1 / c) ≥ 4 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
    have h₄₁ : 1 / a + 1 / b ≥ 4 / (a + b) := h₁
    have h₄₂ : 1 / b + 1 / c ≥ 4 / (b + c) := h₂
    have h₄₃ : 1 / c + 1 / a ≥ 4 / (c + a) := h₃
    have h₄₄ : (1 / a + 1 / b) + (1 / b + 1 / c) + (1 / c + 1 / a) ≥ 4 / (a + b) + 4 / (b + c) + 4 / (c + a) := by
      linarith
    have h₄₅ : 2 * (1 / a + 1 / b + 1 / c) ≥ 4 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
      have h₄₅₁ : (1 / a + 1 / b) + (1 / b + 1 / c) + (1 / c + 1 / a) = 2 * (1 / a + 1 / b + 1 / c) := by ring
      have h₄₅₂ : 4 / (a + b) + 4 / (b + c) + 4 / (c + a) = 4 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
        ring
      linarith
    exact h₄₅

  have h₅ : 1 / a + 1 / b + 1 / c ≥ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
    linarith

  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_2_4_right : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c) := by
  intro a b c h
  have h₁ : 0 < a := by linarith
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < c := by linarith
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 < a * c := by positivity
  have h₆ : 0 < b * c := by positivity
  have h₇ : 0 < a * b * c := by positivity
  field_simp [h₁.ne', h₂.ne', h₃.ne']
  rw [div_le_div_iff (by positivity) (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    mul_nonneg (sq_nonneg (a - b)) h₃.le, mul_nonneg (sq_nonneg (a - c)) h₂.le,
    mul_nonneg (sq_nonneg (b - c)) h₁.le]

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_2_6 : ∀ (a b c : ℝ), a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 3 → 18 * (1 / (3 - c) * (4 - c) + 1 / (3 - a) * (4 - a) + 1 / (3 - b) * (4 - b)) + 2 * (a * b + b * c + c * a) ≥ 15 := by
  intro a b c h
  have h_sum : a + b + c = 3 := by
    linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  
  have h_a_nonneg : a ≥ 0 := by
    linarith [h.1]
  
  have h_b_nonneg : b ≥ 0 := by
    linarith [h.2.1]
  
  have h_c_nonneg : c ≥ 0 := by
    linarith [h.2.2.1]
  
  have h_main : 18 * (1 / (3 - c) * (4 - c) + 1 / (3 - a) * (4 - a) + 1 / (3 - b) * (4 - b)) + 2 * (a * b + b * c + c * a) ≥ 15 := by
    -- Case when one of the variables is 3
    by_cases h₁ : a = 3
    · -- Subcase: a = 3
      have h₂ : b = 0 := by
        have h₃ : a + b + c = 3 := h_sum
        have h₄ : a = 3 := h₁
        have h₅ : b ≥ 0 := h_b_nonneg
        have h₆ : c ≥ 0 := h_c_nonneg
        linarith
      have h₃ : c = 0 := by
        have h₄ : a + b + c = 3 := h_sum
        have h₅ : a = 3 := h₁
        have h₆ : b = 0 := h₂
        have h₇ : b ≥ 0 := h_b_nonneg
        have h₈ : c ≥ 0 := h_c_nonneg
        linarith
      have h₄ : 18 * (1 / (3 - c) * (4 - c) + 1 / (3 - a) * (4 - a) + 1 / (3 - b) * (4 - b)) + 2 * (a * b + b * c + c * a) = 48 := by
        have h₅ : a = 3 := h₁
        have h₆ : b = 0 := h₂
        have h₇ : c = 0 := h₃
        rw [h₅, h₆, h₇]
        norm_num
      linarith
    · -- Subcase: a ≠ 3
      by_cases h₂ : b = 3
      · -- Subcase: b = 3
        have h₃ : a = 0 := by
          have h₄ : a + b + c = 3 := h_sum
          have h₅ : b = 3 := h₂
          have h₆ : a ≥ 0 := h_a_nonneg
          have h₇ : c ≥ 0 := h_c_nonneg
          linarith
        have h₄ : c = 0 := by
          have h₅ : a + b + c = 3 := h_sum
          have h₆ : b = 3 := h₂
          have h₇ : a = 0 := h₃
          have h₈ : a ≥ 0 := h_a_nonneg
          have h₉ : c ≥ 0 := h_c_nonneg
          linarith
        have h₅ : 18 * (1 / (3 - c) * (4 - c) + 1 / (3 - a) * (4 - a) + 1 / (3 - b) * (4 - b)) + 2 * (a * b + b * c + c * a) = 48 := by
          have h₆ : b = 3 := h₂
          have h₇ : a = 0 := h₃
          have h₈ : c = 0 := h₄
          rw [h₇, h₆, h₈]
          norm_num
        linarith
      · -- Subcase: b ≠ 3
        by_cases h₃ : c = 3
        · -- Subcase: c = 3
          have h₄ : a = 0 := by
            have h₅ : a + b + c = 3 := h_sum
            have h₆ : c = 3 := h₃
            have h₇ : a ≥ 0 := h_a_nonneg
            have h₈ : b ≥ 0 := h_b_nonneg
            linarith
          have h₅ : b = 0 := by
            have h₆ : a + b + c = 3 := h_sum
            have h₇ : c = 3 := h₃
            have h₈ : a = 0 := h₄
            have h₉ : a ≥ 0 := h_a_nonneg
            have h₁₀ : b ≥ 0 := h_b_nonneg
            linarith
          have h₆ : 18 * (1 / (3 - c) * (4 - c) + 1 / (3 - a) * (4 - a) + 1 / (3 - b) * (4 - b)) + 2 * (a * b + b * c + c * a) = 48 := by
            have h₇ : c = 3 := h₃
            have h₈ : a = 0 := h₄
            have h₉ : b = 0 := h₅
            rw [h₈, h₉, h₇]
            norm_num
          linarith
        · -- Subcase: none of a, b, c is 3
          -- Use the fact that each term is ≥ 1 when 0 ≤ x < 3
          have h₄ : a < 3 := by
            by_contra h₄
            have h₅ : a ≥ 3 := by linarith
            have h₆ : a = 3 := by
              have h₇ : a + b + c = 3 := h_sum
              have h₈ : a ≥ 3 := h₅
              have h₉ : b ≥ 0 := h_b_nonneg
              have h₁₀ : c ≥ 0 := h_c_nonneg
              linarith
            contradiction
          have h₅ : b < 3 := by
            by_contra h₅
            have h₆ : b ≥ 3 := by linarith
            have h₇ : b = 3 := by
              have h₈ : a + b + c = 3 := h_sum
              have h₉ : b ≥ 3 := h₆
              have h₁₀ : a ≥ 0 := h_a_nonneg
              have h₁₁ : c ≥ 0 := h_c_nonneg
              linarith
            contradiction
          have h₆ : c < 3 := by
            by_contra h₆
            have h₇ : c ≥ 3 := by linarith
            have h₈ : c = 3 := by
              have h₉ : a + b + c = 3 := h_sum
              have h₁₀ : c ≥ 3 := h₇
              have h₁₁ : a ≥ 0 := h_a_nonneg
              have h₁₂ : b ≥ 0 := h_b_nonneg
              linarith
            contradiction
          have h₇ : 1 / (3 - a) * (4 - a) ≥ 1 := by
            have h₈ : 0 < 3 - a := by linarith
            have h₉ : (4 - a : ℝ) / (3 - a) ≥ 1 := by
              -- Prove that (4 - a) / (3 - a) ≥ 1 for 0 ≤ a < 3
              have h₁₀ : (4 - a : ℝ) / (3 - a) - 1 = 1 / (3 - a : ℝ) := by
                have h₁₁ : (3 - a : ℝ) ≠ 0 := by linarith
                field_simp [h₁₁]
                <;> ring_nf
                <;> field_simp [h₁₁]
                <;> linarith
              have h₁₁ : 1 / (3 - a : ℝ) > 0 := by
                apply one_div_pos.mpr
                linarith
              have h₁₂ : (4 - a : ℝ) / (3 - a) - 1 > 0 := by linarith
              linarith
            have h₁₀ : (1 : ℝ) / (3 - a) * (4 - a) = (4 - a : ℝ) / (3 - a) := by
              field_simp [sub_ne_zero.mpr (show (3 : ℝ) ≠ a by linarith)]
              <;> ring_nf
            rw [h₁₀]
            linarith
          have h₈ : 1 / (3 - b) * (4 - b) ≥ 1 := by
            have h₉ : 0 < 3 - b := by linarith
            have h₁₀ : (4 - b : ℝ) / (3 - b) ≥ 1 := by
              -- Prove that (4 - b) / (3 - b) ≥ 1 for 0 ≤ b < 3
              have h₁₁ : (4 - b : ℝ) / (3 - b) - 1 = 1 / (3 - b : ℝ) := by
                have h₁₂ : (3 - b : ℝ) ≠ 0 := by linarith
                field_simp [h₁₂]
                <;> ring_nf
                <;> field_simp [h₁₂]
                <;> linarith
              have h₁₂ : 1 / (3 - b : ℝ) > 0 := by
                apply one_div_pos.mpr
                linarith
              have h₁₃ : (4 - b : ℝ) / (3 - b) - 1 > 0 := by linarith
              linarith
            have h₁₁ : (1 : ℝ) / (3 - b) * (4 - b) = (4 - b : ℝ) / (3 - b) := by
              field_simp [sub_ne_zero.mpr (show (3 : ℝ) ≠ b by linarith)]
              <;> ring_nf
            rw [h₁₁]
            linarith
          have h₉ : 1 / (3 - c) * (4 - c) ≥ 1 := by
            have h₁₀ : 0 < 3 - c := by linarith
            have h₁₁ : (4 - c : ℝ) / (3 - c) ≥ 1 := by
              -- Prove that (4 - c) / (3 - c) ≥ 1 for 0 ≤ c < 3
              have h₁₂ : (4 - c : ℝ) / (3 - c) - 1 = 1 / (3 - c : ℝ) := by
                have h₁₃ : (3 - c : ℝ) ≠ 0 := by linarith
                field_simp [h₁₃]
                <;> ring_nf
                <;> field_simp [h₁₃]
                <;> linarith
              have h₁₃ : 1 / (3 - c : ℝ) > 0 := by
                apply one_div_pos.mpr
                linarith
              have h₁₄ : (4 - c : ℝ) / (3 - c) - 1 > 0 := by linarith
              linarith
            have h₁₂ : (1 : ℝ) / (3 - c) * (4 - c) = (4 - c : ℝ) / (3 - c) := by
              field_simp [sub_ne_zero.mpr (show (3 : ℝ) ≠ c by linarith)]
              <;> ring_nf
            rw [h₁₂]
            linarith
          have h₁₀ : 18 * (1 / (3 - c) * (4 - c) + 1 / (3 - a) * (4 - a) + 1 / (3 - b) * (4 - b)) ≥ 54 := by
            linarith [h₇, h₈, h₉]
          have h₁₁ : 2 * (a * b + b * c + c * a) ≥ 0 := by
            have h₁₂ : 0 ≤ a * b := by positivity
            have h₁₃ : 0 ≤ b * c := by positivity
            have h₁₄ : 0 ≤ c * a := by positivity
            linarith
          linarith
  exact h_main

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_2_7 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → (b + c - a) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (c + a - b) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (a + b - c) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5 := by
  have h₁ : ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 → (b + c - a) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (c + a - b) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (a + b - c) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5 := by
    intro a b c ha hb hc
    have h₂ : 0 < a * b := mul_pos ha hb
    have h₃ : 0 < b * c := mul_pos hb hc
    have h₄ : 0 < c * a := mul_pos hc ha
    field_simp [add_assoc]
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg h₂.le (sq_nonneg (a - b)), mul_nonneg h₃.le (sq_nonneg (b - c)),
      mul_nonneg h₄.le (sq_nonneg (c - a)), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b - c)),
      mul_nonneg (sq_nonneg (b - c)) (sq_nonneg (b + c - a)), mul_nonneg (sq_nonneg (c - a)) (sq_nonneg (c + a - b)),
      mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb), mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hc),
      mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos ha)]
  intro a b c h
  have h₂ : a > 0 := h.1
  have h₃ : b > 0 := h.2.1
  have h₄ : c > 0 := h.2.2
  have h₅ : (b + c - a) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (c + a - b) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (a + b - c) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5 := h₁ a b c h₂ h₃ h₄
  exact h₅

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_example_3_5 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 27 / (2 * (a + b + c) ^ 2) := by
  intro a b c h
  have h₁ : 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 9 / (2 * (a * b + b * c + c * a)) := by
    have h₁₁ : 0 < a := by linarith
    have h₁₂ : 0 < b := by linarith
    have h₁₃ : 0 < c := by linarith
    have h₁₄ : 0 < a * b := by positivity
    have h₁₅ : 0 < b * c := by positivity
    have h₁₆ : 0 < c * a := by positivity
    have h₁₇ : 0 < a * (b + c) := by positivity
    have h₁₈ : 0 < b * (c + a) := by positivity
    have h₁₉ : 0 < c * (a + b) := by positivity
    have h₂₀ : 0 < a * b + b * c + c * a := by positivity
    -- Use Titu's lemma (a form of Cauchy-Schwarz) to prove the inequality
    have h₂₁ : (1 : ℝ) / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 9 / (2 * (a * b + b * c + c * a)) := by
      have h₂₂ : 0 < a * (b + c) := by positivity
      have h₂₃ : 0 < b * (c + a) := by positivity
      have h₂₄ : 0 < c * (a + b) := by positivity
      -- Use the Cauchy-Schwarz inequality in the form of Titu's lemma
      have h₂₅ : (1 : ℝ) / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) = (1 : ℝ) / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) := rfl
      have h₂₆ : (1 : ℝ) ^ 2 / (a * (b + c)) + (1 : ℝ) ^ 2 / (b * (c + a)) + (1 : ℝ) ^ 2 / (c * (a + b)) ≥ (1 + 1 + 1 : ℝ) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := by
        -- Apply the Cauchy-Schwarz inequality
        have h₂₇ : 0 < a * (b + c) + b * (c + a) + c * (a + b) := by positivity
        have h₂₈ : 0 < a * (b + c) := by positivity
        have h₂₉ : 0 < b * (c + a) := by positivity
        have h₃₀ : 0 < c * (a + b) := by positivity
        -- Use the Titu's lemma form of Cauchy-Schwarz
        have h₃₁ : (1 : ℝ) ^ 2 / (a * (b + c)) + (1 : ℝ) ^ 2 / (b * (c + a)) + (1 : ℝ) ^ 2 / (c * (a + b)) ≥ (1 + 1 + 1 : ℝ) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) := by
          -- Prove the inequality using the Titu's lemma
          field_simp [h₂₈.ne', h₂₉.ne', h₃₀.ne', h₂₇.ne']
          rw [div_le_div_iff (by positivity) (by positivity)]
          nlinarith [sq_nonneg (a * (b + c) - b * (c + a)), sq_nonneg (b * (c + a) - c * (a + b)), sq_nonneg (c * (a + b) - a * (b + c))]
        exact h₃₁
      -- Simplify the right-hand side of the inequality
      have h₃₂ : (1 + 1 + 1 : ℝ) ^ 2 / (a * (b + c) + b * (c + a) + c * (a + b)) = 9 / (2 * (a * b + b * c + c * a)) := by
        have h₃₃ : a * (b + c) + b * (c + a) + c * (a + b) = 2 * (a * b + b * c + c * a) := by
          ring
        rw [h₃₃]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
      -- Combine the results to get the final inequality
      have h₃₄ : (1 : ℝ) ^ 2 / (a * (b + c)) + (1 : ℝ) ^ 2 / (b * (c + a)) + (1 : ℝ) ^ 2 / (c * (a + b)) = (1 : ℝ) / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) := by
        norm_num
      rw [h₃₄] at h₂₆
      linarith
    exact h₂₁
  
  have h₂ : 9 / (2 * (a * b + b * c + c * a)) ≥ 27 / (2 * (a + b + c) ^ 2) := by
    have h₂₁ : 0 < a := by linarith
    have h₂₂ : 0 < b := by linarith
    have h₂₃ : 0 < c := by linarith
    have h₂₄ : 0 < a * b := by positivity
    have h₂₅ : 0 < b * c := by positivity
    have h₂₆ : 0 < c * a := by positivity
    have h₂₇ : 0 < a * b + b * c + c * a := by positivity
    have h₂₈ : 0 < a + b + c := by positivity
    have h₂₉ : 0 < (a + b + c) ^ 2 := by positivity
    -- Prove that (a + b + c)^2 ≥ 3(ab + bc + ca)
    have h₃₀ : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    -- Use the above inequality to prove the desired inequality
    have h₃₁ : 9 / (2 * (a * b + b * c + c * a)) ≥ 27 / (2 * (a + b + c) ^ 2) := by
      -- Use the fact that (a + b + c)^2 ≥ 3(ab + bc + ca)
      have h₃₂ : 0 < 2 * (a * b + b * c + c * a) := by positivity
      have h₃₃ : 0 < 2 * (a + b + c) ^ 2 := by positivity
      -- Use the division inequality to compare the two sides
      rw [ge_iff_le]
      rw [div_le_div_iff (by positivity) (by positivity)]
      -- Use nlinarith to verify the inequality
      nlinarith [h₃₀]
    exact h₃₁
  
  have h₃ : 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 27 / (2 * (a + b + c) ^ 2) := by
    linarith
  
  exact h₃

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_problem_4_1 : ∀ (a b c : ℝ), a + b + c = 3 → Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ Real.sqrt 3 := by
  intro a b c h
  have h₁ : a ^ 2 + a * b + b ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b * Real.sqrt 3 / 2)]
  
  have h₂ : b ^ 2 + b * c + c ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (b + c / 2), sq_nonneg (c * Real.sqrt 3 / 2)]
  
  have h₃ : c ^ 2 + c * a + a ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (c + a / 2), sq_nonneg (a * Real.sqrt 3 / 2)]
  
  have h₄ : 2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a * b + b * c + c * a) ≥ 9 := by
    have h₄₁ : (a + b + c) ^ 2 = 9 := by
      rw [h]
      <;> norm_num
    have h₄₂ : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have h₄₃ : 2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a * b + b * c + c * a) = (3 * (a ^ 2 + b ^ 2 + c ^ 2) + 9) / 2 := by
      have h₄₄ : a * b + b * c + c * a = (9 - (a ^ 2 + b ^ 2 + c ^ 2)) / 2 := by
        nlinarith
      rw [h₄₄]
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> nlinarith
    rw [h₄₃]
    nlinarith [h₄₂]
  
  have h₅ : (Real.sqrt (a ^ 2 + a * b + b ^ 2)) ^ 2 + (Real.sqrt (b ^ 2 + b * c + c ^ 2)) ^ 2 + (Real.sqrt (c ^ 2 + c * a + a ^ 2)) ^ 2 ≥ 9 := by
    have h₅₁ : (Real.sqrt (a ^ 2 + a * b + b ^ 2)) ^ 2 = a ^ 2 + a * b + b ^ 2 := by
      rw [Real.sq_sqrt] <;> nlinarith
    have h₅₂ : (Real.sqrt (b ^ 2 + b * c + c ^ 2)) ^ 2 = b ^ 2 + b * c + c ^ 2 := by
      rw [Real.sq_sqrt] <;> nlinarith
    have h₅₃ : (Real.sqrt (c ^ 2 + c * a + a ^ 2)) ^ 2 = c ^ 2 + c * a + a ^ 2 := by
      rw [Real.sq_sqrt] <;> nlinarith
    have h₅₄ : (Real.sqrt (a ^ 2 + a * b + b ^ 2)) ^ 2 + (Real.sqrt (b ^ 2 + b * c + c ^ 2)) ^ 2 + (Real.sqrt (c ^ 2 + c * a + a ^ 2)) ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a * b + b * c + c * a) := by
      rw [h₅₁, h₅₂, h₅₃]
      <;> ring_nf
      <;> nlinarith
    linarith
  
  have h₆ : (Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2)) ^ 2 ≥ 9 := by
    have h₆₁ : 0 ≤ Real.sqrt (a ^ 2 + a * b + b ^ 2) := Real.sqrt_nonneg _
    have h₆₂ : 0 ≤ Real.sqrt (b ^ 2 + b * c + c ^ 2) := Real.sqrt_nonneg _
    have h₆₃ : 0 ≤ Real.sqrt (c ^ 2 + c * a + a ^ 2) := Real.sqrt_nonneg _
    have h₆₄ : 0 ≤ Real.sqrt (a ^ 2 + a * b + b ^ 2) * Real.sqrt (b ^ 2 + b * c + c ^ 2) := by positivity
    have h₆₅ : 0 ≤ Real.sqrt (b ^ 2 + b * c + c ^ 2) * Real.sqrt (c ^ 2 + c * a + a ^ 2) := by positivity
    have h₆₆ : 0 ≤ Real.sqrt (c ^ 2 + c * a + a ^ 2) * Real.sqrt (a ^ 2 + a * b + b ^ 2) := by positivity
    nlinarith [sq_nonneg (Real.sqrt (a ^ 2 + a * b + b ^ 2) - Real.sqrt (b ^ 2 + b * c + c ^ 2)),
      sq_nonneg (Real.sqrt (b ^ 2 + b * c + c ^ 2) - Real.sqrt (c ^ 2 + c * a + a ^ 2)),
      sq_nonneg (Real.sqrt (c ^ 2 + c * a + a ^ 2) - Real.sqrt (a ^ 2 + a * b + b ^ 2))]
  
  have h₇ : Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ 3 := by
    have h₇₁ : 0 ≤ Real.sqrt (a ^ 2 + a * b + b ^ 2) := Real.sqrt_nonneg _
    have h₇₂ : 0 ≤ Real.sqrt (b ^ 2 + b * c + c ^ 2) := Real.sqrt_nonneg _
    have h₇₃ : 0 ≤ Real.sqrt (c ^ 2 + c * a + a ^ 2) := Real.sqrt_nonneg _
    have h₇₄ : 0 ≤ Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) := by positivity
    nlinarith [sq_nonneg (Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) - 3)]
  
  have h₈ : (3 : ℝ) ≥ Real.sqrt 3 := by
    have h₈₁ : Real.sqrt 3 ≤ 3 := by
      have h₈₂ : Real.sqrt 3 ≤ 3 := by
        rw [Real.sqrt_le_iff]
        norm_num
      linarith
    linarith
  
  have h₉ : Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) + Real.sqrt (c ^ 2 + c * a + a ^ 2) ≥ Real.sqrt 3 := by
    linarith [h₇, h₈]
  
  exact h₉

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem evan_problem_4_6 : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = a ^ (1 / 7) + b ^ (1 / 7) + c ^ (1 / 7) → a ^ a * b ^ b * c ^ c ≥ 1 := by
  have h_main_ineq : ∀ (x : ℝ), x > 0 → x * Real.log x ≥ x - 1 := by
    intro x hx
    have h₁ : Real.log x ≥ 1 - 1 / x := by
      -- Prove that log x ≥ 1 - 1/x for x > 0
      have h₂ : Real.log x ≥ 1 - 1 / x := by
        -- Use the fact that the logarithm function is concave and the tangent line at x=1 is y = x - 1
        have h₃ : Real.log (1 / x) ≤ (1 / x) - 1 := by
          -- Use the inequality log x ≤ x - 1 for x > 0
          have h₄ : Real.log (1 / x) ≤ (1 / x) - 1 := by
            have h₅ : 1 / x > 0 := by positivity
            have h₆ : Real.log (1 / x) ≤ (1 / x) - 1 := by
              -- Apply the inequality log x ≤ x - 1 to 1/x
              linarith [Real.log_le_sub_one_of_pos h₅]
            linarith
          linarith
        -- Manipulate the inequality to get the desired form
        have h₇ : Real.log (1 / x) = -Real.log x := by
          rw [Real.log_div (by norm_num) (by positivity)]
          <;> simp [Real.log_one]
          <;> ring
        rw [h₇] at h₃
        have h₈ : -Real.log x ≤ (1 / x) - 1 := by linarith
        have h₉ : Real.log x ≥ 1 - 1 / x := by linarith
        linarith
      linarith
    -- Use the inequality to prove x * log x ≥ x - 1
    have h₂ : x * Real.log x ≥ x - 1 := by
      have h₃ : Real.log x ≥ 1 - 1 / x := h₁
      have h₄ : x * Real.log x ≥ x * (1 - 1 / x) := by
        -- Multiply both sides by x (which is positive)
        have h₅ : x > 0 := hx
        nlinarith
      have h₅ : x * (1 - 1 / x) = x - 1 := by
        -- Simplify the right-hand side
        field_simp [hx.ne']
        <;> ring
        <;> field_simp [hx.ne']
        <;> linarith
      linarith
    exact h₂
  
  have h_final : ∀ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 → a ^ a * b ^ b * c ^ c ≥ 1 := by
    intro a b c h
    have h₁ : a > 0 := h.1
    have h₂ : b > 0 := h.2.1
    have h₃ : c > 0 := h.2.2.1
    have h₄ : a + b + c = 3 := h.2.2.2
    have h₅ : a * Real.log a + b * Real.log b + c * Real.log c ≥ 0 := by
      have h₅₁ : a * Real.log a ≥ a - 1 := h_main_ineq a h₁
      have h₅₂ : b * Real.log b ≥ b - 1 := h_main_ineq b h₂
      have h₅₃ : c * Real.log c ≥ c - 1 := h_main_ineq c h₃
      -- Sum the inequalities and use the condition a + b + c = 3
      linarith
    have h₆ : Real.log (a ^ a * b ^ b * c ^ c) = a * Real.log a + b * Real.log b + c * Real.log c := by
      have h₆₁ : Real.log (a ^ a * b ^ b * c ^ c) = Real.log (a ^ a) + Real.log (b ^ b) + Real.log (c ^ c) := by
        have h₆₂ : Real.log (a ^ a * b ^ b * c ^ c) = Real.log (a ^ a * b ^ b) + Real.log (c ^ c) := by
          rw [Real.log_mul (by
            -- Prove that a^a * b^b > 0
            have h₆₃ : a > 0 := h₁
            have h₆₄ : b > 0 := h₂
            positivity
          ) (by
            -- Prove that c^c > 0
            have h₆₃ : c > 0 := h₃
            positivity
          )]
        rw [h₆₂]
        have h₆₃ : Real.log (a ^ a * b ^ b) = Real.log (a ^ a) + Real.log (b ^ b) := by
          rw [Real.log_mul (by
            -- Prove that a^a > 0
            have h₆₄ : a > 0 := h₁
            positivity
          ) (by
            -- Prove that b^b > 0
            have h₆₄ : b > 0 := h₂
            positivity
          )]
        rw [h₆₃]
        <;> ring_nf
      have h₆₂ : Real.log (a ^ a) = a * Real.log a := by
        rw [Real.log_rpow (by positivity)]
      have h₆₃ : Real.log (b ^ b) = b * Real.log b := by
        rw [Real.log_rpow (by positivity)]
      have h₆₄ : Real.log (c ^ c) = c * Real.log c := by
        rw [Real.log_rpow (by positivity)]
      rw [h₆₁, h₆₂, h₆₃, h₆₄]
      <;> ring_nf
    have h₇ : Real.log (a ^ a * b ^ b * c ^ c) ≥ 0 := by
      rw [h₆]
      linarith
    have h₈ : a ^ a * b ^ b * c ^ c ≥ 1 := by
      by_contra h₈₁
      -- If a^a * b^b * c^c < 1, then log(a^a * b^b * c^c) < 0, which contradicts h₇
      have h₈₂ : a ^ a * b ^ b * c ^ c < 1 := by linarith
      have h₈₃ : Real.log (a ^ a * b ^ b * c ^ c) < 0 := by
        have h₈₄ : a ^ a * b ^ b * c ^ c > 0 := by
          -- Prove that a^a * b^b * c^c > 0
          have h₈₅ : a > 0 := h₁
          have h₈₆ : b > 0 := h₂
          have h₈₇ : c > 0 := h₃
          positivity
        have h₈₅ : Real.log (a ^ a * b ^ b * c ^ c) < Real.log 1 := by
          apply Real.log_lt_log h₈₄
          linarith
        have h₈₆ : Real.log 1 = 0 := by norm_num
        linarith
      linarith
    exact h₈
  
  intro a b c h
  have h₁ : a > 0 := h.1
  have h₂ : b > 0 := h.2.1
  have h₃ : c > 0 := h.2.2.1
  have h₄ : a + b + c = a ^ (1 / 7) + b ^ (1 / 7) + c ^ (1 / 7) := h.2.2.2
  have h₅ : a + b + c = 3 := by
    norm_num [pow_one] at h₄ ⊢
    <;>
    (try norm_num at h₄ ⊢) <;>
    (try linarith) <;>
    (try ring_nf at h₄ ⊢) <;>
    (try simp_all) <;>
    (try nlinarith)
  have h₆ : a ^ a * b ^ b * c ^ c ≥ 1 := h_final a b c ⟨h₁, h₂, h₃, h₅⟩
  exact h₆
