-- This file proves that the Matthews Correlation Coefficient (MCC)
-- converges to the F-Measure (FM) as the number of true negatives (TN) approaches infinity.
-- Theorem: MCC atTop = FM

import Mathlib

open Filter Topology

noncomputable def MCC (TP FP FN TN : ℝ) : ℝ :=
  (TP * TN - FP * FN) / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))

noncomputable def FM (TP FP FN : ℝ) : ℝ :=
  TP / Real.sqrt ((TP + FP) * (TP + FN))

theorem MCC_atTop_eq_FM (TP FP FN : ℝ) (hTPFPpos : 0 < TP + FP) (hTPFNpos : 0 < TP + FN) :
    Tendsto (fun TN : ℝ => MCC TP FP FN TN) atTop (𝓝 (FM TP FP FN)) := by
  have hpos : 0 < (TP + FP) * (TP + FN) := mul_pos hTPFPpos hTPFNpos
  have hsqrt_pos : 0 < Real.sqrt ((TP + FP) * (TP + FN)) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne_zero : Real.sqrt ((TP + FP) * (TP + FN)) ≠ 0 := hsqrt_pos.ne'

  -- Show that TN⁻¹ → 0 as TN → ∞
  have h1 : Tendsto (fun TN : ℝ => TN⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero

  -- Show that FP * FN * TN⁻¹ → 0
  have h2 : Tendsto (fun TN : ℝ => FP * FN * TN⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun TN : ℝ => (FP * FN : ℝ) * TN⁻¹) atTop (𝓝 ((FP * FN : ℝ) * 0)) := by
      apply Tendsto.mul
      · exact tendsto_const_nhds
      · exact h1
    convert this using 1 <;> ring_nf

  -- Show that TP - FP * FN * TN⁻¹ → TP
  have h3 : Tendsto (fun TN : ℝ => TP - FP * FN * TN⁻¹) atTop (𝓝 TP) := by
    have : Tendsto (fun TN : ℝ => (TP : ℝ) - FP * FN * TN⁻¹) atTop (𝓝 (TP - 0)) := by
      apply Tendsto.sub
      · exact tendsto_const_nhds
      · exact h2
    convert this using 1 <;> simp

  -- Show that FP * TN⁻¹ → 0
  have h4 : Tendsto (fun TN : ℝ => FP * TN⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun TN : ℝ => (FP : ℝ) * TN⁻¹) atTop (𝓝 ((FP : ℝ) * 0)) := by
      apply Tendsto.mul
      · exact tendsto_const_nhds
      · exact h1
    convert this using 1 <;> ring_nf

  -- Show that 1 + FP * TN⁻¹ → 1
  have h5 : Tendsto (fun TN : ℝ => 1 + FP * TN⁻¹) atTop (𝓝 1) := by
    have : Tendsto (fun TN : ℝ => (1 : ℝ) + FP * TN⁻¹) atTop (𝓝 (1 + 0)) := by
      apply Tendsto.add
      · exact tendsto_const_nhds
      · exact h4
    convert this using 1 <;> simp

  -- Show that FN * TN⁻¹ → 0
  have h6 : Tendsto (fun TN : ℝ => FN * TN⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun TN : ℝ => (FN : ℝ) * TN⁻¹) atTop (𝓝 ((FN : ℝ) * 0)) := by
      apply Tendsto.mul
      · exact tendsto_const_nhds
      · exact h1
    convert this using 1 <;> ring_nf

  -- Show that 1 + FN * TN⁻¹ → 1
  have h7 : Tendsto (fun TN : ℝ => 1 + FN * TN⁻¹) atTop (𝓝 1) := by
    have : Tendsto (fun TN : ℝ => (1 : ℝ) + FN * TN⁻¹) atTop (𝓝 (1 + 0)) := by
      apply Tendsto.add
      · exact tendsto_const_nhds
      · exact h6
    convert this using 1 <;> simp

  -- Show that (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹) → 1
  have h8 : Tendsto (fun TN : ℝ => (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) atTop (𝓝 1) := by
    have : Tendsto (fun TN : ℝ => (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) atTop (𝓝 (1 * 1)) := by
      apply Tendsto.mul
      · exact h5
      · exact h7
    convert this using 1 <;> simp

  -- Show that (TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹) → (TP + FP) * (TP + FN)
  have h9 : Tendsto (fun TN : ℝ => (TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹))
      atTop (𝓝 ((TP + FP) * (TP + FN))) := by
    have : Tendsto (fun TN : ℝ => ((TP + FP) * (TP + FN) : ℝ) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹))
        atTop (𝓝 (((TP + FP) * (TP + FN) : ℝ) * 1)) := by
      apply Tendsto.mul
      · exact tendsto_const_nhds
      · apply Tendsto.mul
        · exact tendsto_const_nhds
        · exact h8
    convert this using 1 <;> simp

  -- Show that sqrt((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) → sqrt((TP + FP) * (TP + FN))
  have h10 : Tendsto (fun TN : ℝ => Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)))
      atTop (𝓝 (Real.sqrt ((TP + FP) * (TP + FN)))) := by
    exact (Real.continuous_sqrt).continuousAt.tendsto.comp h9

  -- Show that the simplified expression converges to FM
  have h12 : Tendsto (fun TN : ℝ => (TP - FP * FN * TN⁻¹) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)))
      atTop (𝓝 (TP / Real.sqrt ((TP + FP) * (TP + FN)))) := by
    have hfmeq : FM TP FP FN = TP / Real.sqrt ((TP + FP) * (TP + FN)) := rfl
    rw [hfmeq]
    exact Tendsto.div h3 h10 hsqrt_ne_zero

  -- Show that MCC TP FP FN TN equals the simplified expression for large TN
  have h13 : ∀ᶠ (TN : ℝ) in atTop, MCC TP FP FN TN =
      (TP - FP * FN * TN⁻¹) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) := by
    filter_upwards [atTop] with TN hTN
    have hTN : 0 < TN := by linarith
    have hsqrt : Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) * TN⁻¹ =
        Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) := by
      have hposTN : 0 < TN := hTN
      have hposProd : 0 < (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN) := by positivity
      calc
        Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) * TN⁻¹
          = Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) * (1 / TN) := by rw [inv_eq_one_div]
        _ = Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN) / TN ^ 2) := by
          rw [← Real.sqrt_mul_self hposTN, div_eq_mul_inv, mul_div_assoc]
          <;> field_simp [hTN.ne']
          <;> ring_nf
        _ = Real.sqrt ((TP + FP) * (TP + FN) * ((TN + FP) / TN) * ((TN + FN) / TN)) := by
          field_simp [hTN.ne']
          <;> ring_nf
        _ = Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) := by
          field_simp [hTN.ne']
          <;> ring_nf
    calc
      MCC TP FP FN TN
        = (TP * TN - FP * FN) / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) := rfl
      _ = (TP - FP * FN * TN⁻¹) / (Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) * TN⁻¹) := by
          field_simp [hTN.ne', inv_eq_one_div]
          <;> ring_nf
      _ = (TP - FP * FN * TN⁻¹) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) := by
          rw [hsqrt]
      _ = (TP - FP * FN * TN⁻¹) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)) := rfl

  -- Combine the results using Tendsto.congr
  have h14 : Tendsto (fun TN : ℝ => MCC TP FP FN TN) atTop (𝓝 (FM TP FP FN)) := by
    have : Tendsto (fun TN : ℝ => (TP - FP * FN * TN⁻¹) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP * TN⁻¹) * (1 + FN * TN⁻¹)))
        atTop (𝓝 (FM TP FP FN)) := h12
    exact this.congr h13

  exact h14
