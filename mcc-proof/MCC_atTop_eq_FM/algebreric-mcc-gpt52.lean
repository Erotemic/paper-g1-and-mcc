import Mathlib.Tactic
open Filter Topology

noncomputable section

/-- Precision -/
def PPV (TP FP : Real) : Real := TP / (TP + FP)

/-- Recall -/
def TPR (TP FN : Real) : Real := TP / (TP + FN)

/-- Fowlkes–Mallows index -/
def FM (TP FP FN : Real) : Real :=
  Real.sqrt (PPV TP FP * TPR TP FN)

/-- Matthews Correlation Coefficient (MCC) -/
def MCC (TP TN FP FN : Real) : Real :=
  let num := TP * TN - FP * FN
  let den := Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))
  num / den

/-- `TN + X = TN * (1 + X/TN)` when `TN ≠ 0`. -/
lemma add_eq_mul_one_add_div (TN X : Real) (hTN : TN ≠ 0) :
    TN + X = TN * (1 + X / TN) := by
  field_simp [hTN]

/-- Cancel a common nonzero left factor in a ratio. -/
lemma mul_div_mul_cancel_left (a b c : Real) (hc : c ≠ 0) :
    (c * a) / (c * b) = a / b := by
  field_simp [hc]

/-
Lee step (1)-(3), arranged to mirror the paper:

1. Numerator: TP*TN - FP*FN = TN*(TP - FP*FN/TN)
2. Denominator: factor TN out of (TN+FP)(TN+FN) using TN*(1+FP/TN), TN*(1+FN/TN)
3. Pull sqrt(TN*TN)=TN (since TN>0)
4. Cancel the common TN
-/
lemma mcc_Lee_rewrite
    {TP FP FN TN : Real}
    (hTN : 0 < TN)
    (hFP : 0 ≤ FP) (hFN : 0 ≤ FN)
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN) :
    (TP * TN - FP * FN)
        / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))
      =
    (TP - FP * FN / TN)
        / (Real.sqrt ((TP + FP) * (TP + FN))
           * Real.sqrt ((1 + FP / TN) * (1 + FN / TN))) := by
  have hTN0 : TN ≠ 0 := ne_of_gt hTN

  -- (1) Numerator rewrite
  have h_num :
      TP * TN - FP * FN = TN * (TP - FP * FN / TN) := by
    field_simp [hTN0]

  -- (2) Factor TN out of (TN+FP)(TN+FN)
  have h_tnfp : TN + FP = TN * (1 + FP / TN) := add_eq_mul_one_add_div TN FP hTN0
  have h_tnfn : TN + FN = TN * (1 + FN / TN) := add_eq_mul_one_add_div TN FN hTN0

  have h_prod :
      (TN + FP) * (TN + FN) = (TN * TN) * ((1 + FP / TN) * (1 + FN / TN)) := by
    simp [h_tnfp, h_tnfn]
    ring_nf

  set A : Real := (TP + FP) * (TP + FN)
  set C : Real := (1 + FP / TN) * (1 + FN / TN)

  have hApos : 0 < A := by simpa [A] using mul_pos hTPFPpos hTPFNpos
  have hAnonneg : 0 ≤ A := hApos.le
  have hTN2nonneg : 0 ≤ TN * TN := by nlinarith [hTN.le]

  -- positivity for C (enough for later `positivity` uses / simp)
  have hCnonneg : 0 ≤ C := by
    positivity

  -- sqrt((TN+FP)(TN+FN)) = TN * sqrt(C)
  have h_sqrtB :
      Real.sqrt ((TN + FP) * (TN + FN)) = TN * Real.sqrt C := by
    calc
      Real.sqrt ((TN + FP) * (TN + FN))
          = Real.sqrt ((TN * TN) * C) := by
              simp [h_prod, C]
      _   = Real.sqrt (TN * TN) * Real.sqrt C := by
              -- `Real.sqrt_mul` needs nonneg proof for the first factor only (in your snapshot)
              simpa using (Real.sqrt_mul (x := TN * TN) hTN2nonneg C)
      _   = TN * Real.sqrt C := by
              have hs : Real.sqrt (TN * TN) = TN :=
                Real.sqrt_mul_self (show 0 ≤ TN from hTN.le)
              simp [hs, mul_assoc]

  -- split the big sqrt into sqrt(A) * sqrt(B), then substitute h_sqrtB
  have h_big_sqrt :
      Real.sqrt (A * ((TN + FP) * (TN + FN)))
        = Real.sqrt A * (TN * Real.sqrt C) := by
    calc
      Real.sqrt (A * ((TN + FP) * (TN + FN)))
          = Real.sqrt A * Real.sqrt ((TN + FP) * (TN + FN)) := by
              simpa using (Real.sqrt_mul (x := A) hAnonneg ((TN + FP) * (TN + FN)))
      _   = Real.sqrt A * (TN * Real.sqrt C) := by
              simp [h_sqrtB]

  -- reassociate the original product into A * ((TN+FP)(TN+FN))
  have h_den_reassoc :
      (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN) = A * ((TN + FP) * (TN + FN)) := by
    simp [A, mul_assoc, mul_left_comm, mul_comm]

  -- (3)(4) Put it together and cancel TN
  calc
    (TP * TN - FP * FN)
        / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))
        =
      (TP * TN - FP * FN) / Real.sqrt (A * ((TN + FP) * (TN + FN))) := by
        simp [h_den_reassoc]
    _ =
      (TN * (TP - FP * FN / TN)) / (Real.sqrt A * (TN * Real.sqrt C)) := by
        simp [h_num, h_big_sqrt]
    _ =
      (TN * (TP - FP * FN / TN)) / (TN * (Real.sqrt A * Real.sqrt C)) := by
        have hdenTN : Real.sqrt A * (TN * Real.sqrt C) = TN * (Real.sqrt A * Real.sqrt C) := by
          ring
        simp [hdenTN, mul_assoc]
    _ =
      (TP - FP * FN / TN) / (Real.sqrt A * Real.sqrt C) := by
        simpa [mul_assoc] using
          (mul_div_mul_cancel_left (a := (TP - FP * FN / TN)) (b := (Real.sqrt A * Real.sqrt C)) (c := TN) hTN0)
    _ =
      (TP - FP * FN / TN)
        / (Real.sqrt ((TP + FP) * (TP + FN))
           * Real.sqrt ((1 + FP / TN) * (1 + FN / TN))) := by
        simp [A, C, mul_assoc]

/-- FM in closed form. -/
lemma FM_eq_closed
    {TP FP FN : Real}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_nonneg : 0 ≤ TP) :
    FM TP FP FN = TP / Real.sqrt ((TP + FP) * (TP + FN)) := by
  unfold FM PPV TPR
  set D : Real := (TP + FP) * (TP + FN)

  have hDpos : 0 < D := by simpa [D] using mul_pos hTPFPpos hTPFNpos
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  have h0 : TP + FP ≠ 0 := ne_of_gt hTPFPpos
  have h1 : TP + FN ≠ 0 := ne_of_gt hTPFNpos

  -- rewrite the inside product as TP^2 / D
  have hinside :
      TP / (TP + FP) * (TP / (TP + FN)) = (TP ^ 2) / D := by
    field_simp [h0, h1, D]
    ring

  -- apply that rewrite
  simp [hinside]

  -- now goal: √(TP^2 / D) = TP / √D
  have hsqrtD0 : Real.sqrt D ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hDpos)
  apply (eq_div_iff hsqrtD0).2

  -- show: √(TP^2 / D) * √D = TP
  have hx : 0 ≤ (TP ^ 2) / D := by
    have : 0 ≤ TP ^ 2 := by positivity
    exact div_nonneg this hDpos.le

  have hmul : ((TP ^ 2) / D) * D = TP ^ 2 := by
    field_simp [hD0]

  calc
    Real.sqrt ((TP ^ 2) / D) * Real.sqrt D
        = Real.sqrt (((TP ^ 2) / D) * D) := by
            -- use sqrt_mul, then take symmetry
            symm
            simpa using (Real.sqrt_mul (x := (TP ^ 2) / D) hx D)
    _   = Real.sqrt (TP ^ 2) := by
            simp [hmul]
    _   = TP := by
            -- sqrt(TP^2)=|TP|=TP (since TP≥0)
            simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hTP_nonneg] using (Real.sqrt_sq_eq_abs TP)

/-- Main target theorem: `MCC(TN) → FM` as `TN → ∞`. -/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : Real}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_nonneg : 0 ≤ TP)
    (hFP_nonneg : 0 ≤ FP)
    (hFN_nonneg : 0 ≤ FN) :
    Tendsto (fun TN : Real => MCC TP TN FP FN) atTop (nhds (FM TP FP FN)) := by
  -- unfold MCC to the raw expression
  simp [MCC]

  -- Lee-step rewrite holds eventually (TN>0) along atTop
  have h_eventually :
      (∀ᶠ TN in (atTop : Filter Real),
        (TP * TN - FP * FN)
          / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))
        =
        (TP - FP * FN / TN)
          / (Real.sqrt ((TP + FP) * (TP + FN))
             * Real.sqrt ((1 + FP / TN) * (1 + FN / TN)))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with TN hTN
    simpa using
      mcc_Lee_rewrite (TP := TP) (FP := FP) (FN := FN) (TN := TN)
        hTN hFP_nonneg hFN_nonneg hTPFPpos hTPFNpos

  -- small terms -> 0
  have h_fp_over : Tendsto (fun TN : Real => FP / TN) atTop (nhds (0 : Real)) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h_fn_over : Tendsto (fun TN : Real => FN / TN) atTop (nhds (0 : Real)) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h_fpfnover : Tendsto (fun TN : Real => (FP * FN) / TN) atTop (nhds (0 : Real)) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id

  -- 1 + const/TN -> 1  (simp away 1+0)
  have h_one_plus_fp : Tendsto (fun TN : Real => 1 + FP / TN) atTop (nhds (1 : Real)) := by
    have h1 : Tendsto (fun _ : Real => (1 : Real)) atTop (nhds (1 : Real)) := tendsto_const_nhds
    simpa [add_zero] using (h1.add h_fp_over)
  have h_one_plus_fn : Tendsto (fun TN : Real => 1 + FN / TN) atTop (nhds (1 : Real)) := by
    have h1 : Tendsto (fun _ : Real => (1 : Real)) atTop (nhds (1 : Real)) := tendsto_const_nhds
    simpa [add_zero] using (h1.add h_fn_over)

  -- numerator -> TP  (simp away TP-0)
  have h_num : Tendsto (fun TN : Real => TP - (FP * FN) / TN) atTop (nhds TP) := by
    have hTPc : Tendsto (fun _ : Real => TP) atTop (nhds TP) := tendsto_const_nhds
    simpa [sub_zero] using (hTPc.sub h_fpfnover)

  -- sqrt((1+FP/TN)(1+FN/TN)) -> 1
  have h_prod :
      Tendsto (fun TN : Real => (1 + FP / TN) * (1 + FN / TN)) atTop (nhds ((1 : Real) * (1 : Real))) :=
    h_one_plus_fp.mul h_one_plus_fn

  have h_sqrt_prod :
      Tendsto (fun TN : Real => Real.sqrt ((1 + FP / TN) * (1 + FN / TN)))
        atTop (nhds (Real.sqrt ((1 : Real) * (1 : Real)))) :=
    (Real.continuous_sqrt.tendsto _).comp h_prod

  -- denominator -> sqrtA * 1
  have h_den :
      Tendsto
        (fun TN : Real =>
          Real.sqrt ((TP + FP) * (TP + FN))
            * Real.sqrt ((1 + FP / TN) * (1 + FN / TN)))
        atTop
        (nhds (Real.sqrt ((TP + FP) * (TP + FN)) * Real.sqrt ((1 : Real) * (1 : Real)))) :=
    (tendsto_const_nhds.mul h_sqrt_prod)

  have hsqrt11 : Real.sqrt ((1 : Real) * (1 : Real)) = 1 := by simp
  have hApos : 0 < (TP + FP) * (TP + FN) := mul_pos hTPFPpos hTPFNpos
  have hsqrtA0 : Real.sqrt ((TP + FP) * (TP + FN)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hApos)

  -- simplify denominator limit to just sqrtA
  have h_den' :
      Tendsto
        (fun TN : Real =>
          Real.sqrt ((TP + FP) * (TP + FN))
            * Real.sqrt ((1 + FP / TN) * (1 + FN / TN)))
        atTop
        (nhds (Real.sqrt ((TP + FP) * (TP + FN)))) := by
    simpa [hsqrt11] using h_den

  have h_frac :
      Tendsto
        (fun TN : Real =>
          (TP - (FP * FN) / TN)
            / (Real.sqrt ((TP + FP) * (TP + FN))
               * Real.sqrt ((1 + FP / TN) * (1 + FN / TN))))
        atTop
        (nhds (TP / Real.sqrt ((TP + FP) * (TP + FN)))) :=
    h_num.div h_den' hsqrtA0

  -- flip the eventual equality (rewritten = original)
  have h_eventually_flip :
      (∀ᶠ TN in (atTop : Filter Real),
        (TP - FP * FN / TN)
          / (Real.sqrt ((TP + FP) * (TP + FN))
             * Real.sqrt ((1 + FP / TN) * (1 + FN / TN))) =
        (TP * TN - FP * FN)
          / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))) := by
    filter_upwards [h_eventually] with TN h
    simpa using h.symm

  -- transfer back to the original MCC body
  have h_mcc_limit :
      Tendsto
        (fun TN : Real =>
          (TP * TN - FP * FN)
            / Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)))
        atTop
        (nhds (TP / Real.sqrt ((TP + FP) * (TP + FN)))) :=
    h_frac.congr' h_eventually_flip

  -- identify the limit with FM
  have hFM : FM TP FP FN = TP / Real.sqrt ((TP + FP) * (TP + FN)) :=
    FM_eq_closed (TP := TP) (FP := FP) (FN := FN) hTPFPpos hTPFNpos hTP_nonneg

  simpa [hFM] using h_mcc_limit
