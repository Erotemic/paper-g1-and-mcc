import Mathlib.Tactic
open Filter

noncomputable section

/-- Precision -/
def PPV (TP FP : Real) : Real :=
  TP / (TP + FP)

/-- Recall -/
def TPR (TP FN : Real) : Real :=
  TP / (TP + FN)

/-- Fowlkes-Mallows index -/
def FM (TP FP FN : Real) : Real :=
  Real.sqrt (PPV TP FP * TPR TP FN)

/-- Matthews Correlation Coefficient (MCC) -/
def MCC (TP TN FP FN : Real) : Real :=
  let num := TP * TN - FP * FN
  let den := Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))
  num / den
end

/-- Main target theorem -/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : Real}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_nonneg : 0 <= TP)
    (hFP_nonneg : 0 <= FP)
    (hFN_nonneg : 0 <= FN) :
    Tendsto (fun TN : Real => MCC TP TN FP FN) atTop (nhds (FM TP FP FN)) := by
  -- Simplify the expression for the MCC as TN approaches infinity
  have h_simplify : Filter.Tendsto (
    fun TN : Real =>
      (TP * TN - FP * FN) / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)))
        Filter.atTop (nhds (TP / Real.sqrt ((TP + FP) * (TP + FN)))) := by
    -- We divide numerator and denominator by TN:
    suffices h_suff'' : Filter.Tendsto (
      fun TN : Real =>
      (TP - FP * FN / TN) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN)))
      Filter.atTop (
        nhds (TP / Real.sqrt ((TP + FP) * (TP + FN)))) by
      -- By simplifying, we can see that the two expressions are equivalent for large TN
      have h_eq : forall TN : Real, TN > 0 ->
          (TP * TN - FP * FN) / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) =
          (TP - FP * FN / TN) / Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN))
          := by
        intro TN hTNpos
        field_simp [hTNpos];
        rw [ Real.sqrt_div ( by positivity ), Real.sqrt_sq hTNpos.le ] ; ring_nf;
        -- By simplifying, we can see that the two expressions are equal
        field_simp [hTNpos]
        ring;
      exact h_suff''.congr' (by
        filter_upwards [Filter.eventually_gt_atTop 0] with TN hTN; simp [h_eq TN hTN]);
    exact le_trans (
      Filter.Tendsto.div
      ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) )
      ( Filter.Tendsto.sqrt <| Filter.Tendsto.mul ( Filter.Tendsto.mul
      ( tendsto_const_nhds.mul <| tendsto_const_nhds )
      <| tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop Filter.tendsto_id )
      <| tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop Filter.tendsto_id )
      <| ne_of_gt <| Real.sqrt_pos.mpr <| by positivity ) <| by norm_num;
  convert h_simplify using 1;
  unfold FM PPV TPR; ring_nf;
  field_simp;
  rw [ Real.sqrt_div ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring_nf
