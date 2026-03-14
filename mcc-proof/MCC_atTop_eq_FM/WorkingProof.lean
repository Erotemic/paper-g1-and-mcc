import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib
import Aesop

open Filter
open Real
open NNReal
open Order
open Topology

noncomputable section

namespace ConfusionMatrix

/-- Precision / PPV = TP / (TP + FP) -/
def PPV (TP FP : ℝ) : ℝ :=
  TP / (TP + FP)

/-- Recall / TPR = TP / (TP + FN) -/
def TPR (TP FN : ℝ) : ℝ :=
  TP / (TP + FN)

/-- Fowlkes–Mallows index: geometric mean of precision and recall. -/
def FM (TP FP FN : ℝ) : ℝ :=
  Real.sqrt (PPV TP FP * TPR TP FN)

/-- Matthews Correlation Coefficient (MCC). We treat all entries as reals. -/
def MCC (TP TN FP FN : ℝ) : ℝ :=
  let num := TP * TN - FP * FN
  let den := Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))
  num / den

/-
  Algebraic identity:

    FM = TP / sqrt ((TP + FP) * (TP + FN))

  under some positivity / non-vanishing assumptions.

  I assume `0 ≤ TP` so we can simplify `sqrt(TP^2)` to `TP` instead of `|TP|`.
-/
lemma fm_simplified_abs
    {TP FP FN : ℝ}
    (hPPVden : TP + FP ≠ 0)
    (hTPRden : TP + FN ≠ 0)
    (hNonneg1 : 0 ≤ TP + FP)
    (hNonneg2 : 0 ≤ TP + FN) :
    FM TP FP FN = |TP| / Real.sqrt ((TP + FP) * (TP + FN)) := by
  unfold FM PPV TPR
  -- Show inside sqrt is (TP^2)/((TP+FP)*(TP+FN))
  have hFrac :
      TP / (TP + FP) * (TP / (TP + FN))
        = (TP * TP) / ((TP + FP) * (TP + FN)) := by
    field_simp [mul_comm, mul_left_comm, mul_assoc, hPPVden, hTPRden]
  have h1 :
      Real.sqrt (TP / (TP + FP) * (TP / (TP + FN)))
        = Real.sqrt ((TP * TP) / ((TP + FP) * (TP + FN))) := by
    simp [hFrac]

  -- Denominator product B and its positivity
  set B : ℝ := (TP + FP) * (TP + FN) with hBdef
  have hTPFPpos : 0 < TP + FP :=
    lt_of_le_of_ne hNonneg1 (by simpa [ne_comm] using hPPVden)
  have hTPFNpos : 0 < TP + FN :=
    lt_of_le_of_ne hNonneg2 (by simpa [ne_comm] using hTPRden)
  have hBpos : 0 < B := by
    have := mul_pos hTPFPpos hTPFNpos
    simpa [hBdef] using this
  have hBnonneg : 0 ≤ B := le_of_lt hBpos

  -- TP^2 ≥ 0
  have hNumNonneg : 0 ≤ TP ^ (2 : ℕ) := by
    exact sq_nonneg TP

  -- Now invoke the mathlib lemma `Real.sqrt_div_mul_self`-style:
  -- morally: sqrt (TP^2 / B) = |TP| / sqrt B for B>0.
  -- In mathlib there is a lemma on that shape (the name may differ slightly).
  -- FIXME: you will need to replace `?lemma` with the actual lemma name:
  -- Now show sqrt((TP^2)/B) = |TP| / sqrt B
  have h2 :
      Real.sqrt ((TP * TP) / ((TP + FP) * (TP + FN)))
        = |TP| / Real.sqrt ((TP + FP) * (TP + FN)) := by
    -- Rewrite in terms of B
    have h2' :
        Real.sqrt ((TP * TP) / B)
          = |TP| / Real.sqrt B := by
      -- LHS and RHS are both ≥ 0
      have hL_nonneg :
          0 ≤ Real.sqrt (TP * TP / B) :=
        Real.sqrt_nonneg _
      have hR_nonneg :
          0 ≤ |TP| / Real.sqrt B := by
        have hsqrt_pos : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
        exact div_nonneg (abs_nonneg _) (le_of_lt hsqrt_pos)

      -- Compute their squares and show they match
      have hDivNonneg :
          0 ≤ (TP * TP) / B :=
        div_nonneg (by
                       -- TP*TP = TP^2
                       have := hNumNonneg
                       simpa [pow_two, mul_comm] using this)
                   hBnonneg

      -- (sqrt(X))^2 = X when X ≥ 0
      have hLeft :
          (Real.sqrt (TP * TP / B)) ^ 2
            = (TP * TP) / B := by
        have := Real.sq_sqrt hDivNonneg
        simpa [pow_two] using this

      -- (|TP| / sqrt B)^2 = TP^2 / B
      have hRight :
          (|TP| / Real.sqrt B) ^ 2
            = (TP * TP) / B := by
        -- (a/b)^2 = a^2 / b^2
        have h1 :
            (|TP| / Real.sqrt B) ^ 2
              = (|TP| ^ 2) / (Real.sqrt B) ^ 2 := by
            simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              (div_pow |TP| (Real.sqrt B) 2)
        -- |TP|^2 = TP^2
        have hAbsSq : |TP| ^ 2 = TP ^ 2 := by
          -- |TP|^2 = |TP| * |TP| = TP * TP = TP^2
          simp [pow_two]
        -- (sqrt B)^2 = B
        have hDenSq :
            (Real.sqrt B) ^ 2 = B := by
          have := Real.sq_sqrt hBnonneg
          simpa [pow_two] using this
        -- TP^2 = TP * TP
        have hNum : TP ^ 2 = TP * TP := by
          ring
        -- put it together
        calc
          (|TP| / Real.sqrt B) ^ 2
              = (|TP| ^ 2) / (Real.sqrt B) ^ 2 := h1
          _   = (TP ^ 2) / B := by
                  simp [hAbsSq, hDenSq]
          _   = (TP * TP) / B := by
                  simp [hNum]

      -- Now we know L^2 = R^2
      have hEqSq :
          (Real.sqrt (TP * TP / B)) ^ 2
            = (|TP| / Real.sqrt B) ^ 2 := by
        calc
          (Real.sqrt (TP * TP / B)) ^ 2
              = (TP * TP) / B := hLeft
          _   = (|TP| / Real.sqrt B) ^ 2 := hRight.symm

      -- Use sq_eq_sq_iff_eq_or_eq_neg to conclude L = R
      have hcases :
          Real.sqrt (TP * TP / B) = |TP| / Real.sqrt B
          ∨ Real.sqrt (TP * TP / B) = - (|TP| / Real.sqrt B) := by
        exact
          (sq_eq_sq_iff_eq_or_eq_neg :
              (Real.sqrt (TP * TP / B)) ^ 2 =
                  (|TP| / Real.sqrt B) ^ 2
                ↔ Real.sqrt (TP * TP / B) = |TP| / Real.sqrt B
                  ∨ Real.sqrt (TP * TP / B) =
                      - (|TP| / Real.sqrt B)
          ).1 hEqSq

      rcases hcases with h | h
      · exact h
      · -- second case: L = -R; use nonnegativity to show R = 0, so L = R = 0
        have hR_le0 :
            |TP| / Real.sqrt B ≤ 0 := by
          -- from 0 ≤ L = -R, deduce R ≤ 0
          have hx_nonneg : 0 ≤ Real.sqrt (TP * TP / B) := hL_nonneg
          have hx' :
              0 ≤ - (|TP| / Real.sqrt B) := by
            simpa [h] using hx_nonneg
          -- 0 ≤ -R ↔ R ≤ 0
          have : |TP| / Real.sqrt B ≤ 0 := (neg_nonneg).1 hx'
          simpa using this
        have hR_ge0 :
            0 ≤ |TP| / Real.sqrt B := hR_nonneg
        have hR0 :
            |TP| / Real.sqrt B = 0 :=
          le_antisymm hR_le0 hR_ge0
        have hL0 :
            Real.sqrt (TP * TP / B) = 0 := by
          simpa [hR0, neg_zero] using h
        -- now L and R are both 0
        simp [hL0, hR0]

    -- revert B to (TP+FP)*(TP+FN)
    have h2'' :
        Real.sqrt ((TP * TP) / ((TP + FP) * (TP + FN)))
          = |TP| / Real.sqrt ((TP + FP) * (TP + FN)) := by
      simpa [hBdef] using h2'
    exact h2''

  calc
    FM TP FP FN
        = Real.sqrt (TP / (TP + FP) * (TP / (TP + FN))) := rfl
    _   = Real.sqrt ((TP * TP) / ((TP + FP) * (TP + FN))) := h1
    _   = |TP| / Real.sqrt ((TP + FP) * (TP + FN)) := h2

lemma fm_simplified
    {TP FP FN : ℝ}
    (hPPVden : TP + FP ≠ 0)
    (hTPRden : TP + FN ≠ 0)
    (hNonneg1 : 0 ≤ TP + FP)
    (hNonneg2 : 0 ≤ TP + FN)
    (hTP_nonneg : 0 ≤ TP) :
    FM TP FP FN = TP / Real.sqrt ((TP + FP) * (TP + FN)) := by
  have h := fm_simplified_abs (TP := TP) (FP := FP) (FN := FN)
              hPPVden hTPRden hNonneg1 hNonneg2
  -- Rewrite |TP| as TP using the nonneg hypothesis.
  simpa [abs_of_nonneg hTP_nonneg] using h


/--
  Helper: (TP + FP)*(TP + FN)*(TN + FP)*(TN + FN) is nonnegative
  under nonnegativity of each sum.
-/
lemma denom_nonneg
    {TP TN FP FN : ℝ}
    (hNonnegTPFP : 0 ≤ TP + FP)
    (hNonnegTPFN : 0 ≤ TP + FN)
    (hNonnegTNFP : 0 ≤ TN + FP)
    (hNonnegTNFN : 0 ≤ TN + FN) :
    0 ≤ (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN) := by
  have h1 := mul_nonneg hNonnegTPFP hNonnegTPFN
  have h2 := mul_nonneg hNonnegTNFP hNonnegTNFN
  have := mul_nonneg h1 h2
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-
  Limit lemmas:

  - TP - FP*FN/TN → TP
  - (TN+c)/TN → 1
  - sqrt((TP+FP)*(TP+FN)*((TN+FP)/TN)*((TN+FN)/TN)) → sqrt((TP+FP)*(TP+FN))
-/

lemma tendsto_num
    (TP FP FN : ℝ) :
    Tendsto (fun TN : ℝ => TP - FP * FN / TN) atTop (𝓝 TP) := by
  have h1 : Tendsto (fun _ : ℝ => TP) atTop (𝓝 TP) :=
    tendsto_const_nhds
  -- show FP*FN/TN → 0
  have hInv : Tendsto (fun TN : ℝ => (1 : ℝ) / TN) atTop (𝓝 (0 : ℝ)) := by
    -- FIXME: lemma is `tendsto_inv_atTop_zero` in mathlib.
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hConst : Tendsto (fun _ : ℝ => FP * FN) atTop (𝓝 (FP * FN)) :=
    tendsto_const_nhds
  have hMul := hConst.mul hInv
  have h2 : Tendsto (fun TN : ℝ => FP * FN / TN) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hMul
  have hSub := h1.sub h2
  simpa using hSub

lemma tendsto_ratio_to_one (c : ℝ) :
    Tendsto (fun TN : ℝ => (TN + c) / TN) atTop (𝓝 (1 : ℝ)) := by
  -- First show `c / TN → 0`
  have hInv : Tendsto (fun TN : ℝ => (1 : ℝ) / TN) atTop (𝓝 (0 : ℝ)) := by
    -- lemma: `tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)`
    simpa [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hConst : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) :=
    tendsto_const_nhds
  have hMul := hConst.mul hInv
  have hCTN : Tendsto (fun TN : ℝ => c / TN) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div, div_eq_mul_inv] using hMul

  -- Then `1 + c / TN → 1`
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hAdd := hOne.add hCTN
  have hLim1 :
      Tendsto (fun TN : ℝ => 1 + c / TN) atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm] using hAdd

  -- Now show `(TN + c)/TN = 1 + c / TN` *eventually* (for TN ≠ 0).
  have hEq :
      ∀ᶠ TN in atTop, (TN + c) / TN = 1 + c / TN := by
    -- On `atTop`, TN is eventually ≥ 1, hence ≠ 0.
    have hNe0 : ∀ᶠ TN : ℝ in atTop, TN ≠ 0 := by
      refine (eventually_ge_atTop (1 : ℝ)).mono ?_
      intro TN hTN
      have hpos : 0 < TN := by
        -- 0 < 1 ≤ TN
        have : (0 : ℝ) < 1 := zero_lt_one
        exact lt_of_lt_of_le this hTN
      exact ne_of_gt hpos
    refine hNe0.mono ?_
    intro TN hTN
    -- algebra: (TN + c)/TN = TN/TN + c/TN = 1 + c/TN
    field_simp [hTN, div_eq_mul_inv, add_comm, add_left_comm, add_assoc]

  -- Use congruence of limits under eventual equality.
  exact (tendsto_congr' hEq).mpr hLim1

lemma tendsto_den
    {TP FP FN : ℝ}:
    Tendsto
      (fun TN : ℝ =>
        Real.sqrt ((TP + FP) * (TP + FN) * ((TN + FP)/TN) * ((TN + FN)/TN)))
      atTop
      (𝓝 (Real.sqrt ((TP + FP) * (TP + FN)))) := by
  have hConst :
      Tendsto (fun _ : ℝ => (TP + FP) * (TP + FN)) atTop
              (𝓝 ((TP + FP) * (TP + FN))) :=
    tendsto_const_nhds
  have hRatio1 : Tendsto (fun TN : ℝ => (TN + FP) / TN) atTop (𝓝 (1 : ℝ)) :=
    tendsto_ratio_to_one FP
  have hRatio2 : Tendsto (fun TN : ℝ => (TN + FN) / TN) atTop (𝓝 (1 : ℝ)) :=
    tendsto_ratio_to_one FN

  have hProd :
      Tendsto
        (fun TN : ℝ =>
          (TP + FP) * (TP + FN) * ((TN + FP)/TN) * ((TN + FN)/TN))
        atTop
        (𝓝 ((TP + FP) * (TP + FN) * (1 : ℝ) * (1 : ℝ))) := by
    have hProd1 := hConst.mul hRatio1
    have hProd2 := hProd1.mul hRatio2
    simpa [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hProd2

  have hLimitInside :
      Tendsto
        (fun TN : ℝ =>
          (TP + FP) * (TP + FN) * ((TN + FP)/TN) * ((TN + FN)/TN))
        atTop
        (𝓝 ((TP + FP) * (TP + FN))) := by
    simpa [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hProd

  -- Use continuity of sqrt.
  have hSqrt :
      Tendsto
        (fun TN : ℝ =>
          Real.sqrt ((TP + FP) * (TP + FN) * ((TN + FP)/TN) * ((TN + FN)/TN)))
        atTop
        (𝓝 (Real.sqrt ((TP + FP) * (TP + FN)))) := by
    exact (Real.continuous_sqrt.tendsto _).comp hLimitInside
  simpa using hSqrt

/--
  Main target theorem:

    lim_{TN→∞} MCC(TP,TN,FP,FN) = FM(TP,FP,FN)

  under non-degeneracy and `0 ≤ TP`.
-/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : ℝ}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_nonneg : 0 ≤ TP)
    (hFP_nonneg : 0 ≤ FP)
    (hFN_nonneg : 0 ≤ FN) :
    Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (FM TP FP FN)) := by
  -- Short notation for the denominator part we understand well.
  let denScaled (TN : ℝ) :=
    Real.sqrt ((TP + FP) * (TP + FN) * ((TN + FP)/TN) * ((TN + FN)/TN))
  let numScaled (TN : ℝ) :=
    TP - FP * FN / TN

  -- We already know the limits of numScaled and denScaled from the lemmas above.
  have hNum := tendsto_num TP FP FN
  have hDen := tendsto_den (TP := TP) (FP := FP) (FN := FN)

  have hDenLimitNe0 :
      Real.sqrt ((TP + FP) * (TP + FN)) ≠ 0 := by
    have hPos :
        0 < (TP + FP) * (TP + FN) := mul_pos hTPFPpos hTPFNpos
    have hPosSqrt : 0 < Real.sqrt ((TP + FP) * (TP + FN)) :=
      Real.sqrt_pos.mpr hPos
    exact ne_of_gt hPosSqrt

  -- limit of the quotient numScaled / denScaled
  have hQuot :
      Tendsto (fun TN : ℝ => numScaled TN / denScaled TN)
              atTop
              (𝓝 (TP / Real.sqrt ((TP + FP) * (TP + FN)))) := by
    -- `Tendsto.div` on numScaled and denScaled.
    -- FIXME: depending on your mathlib, you might need to open `TopologicalSpace` or use `tendsto_div`.
    simpa [numScaled, denScaled] using hNum.div hDen hDenLimitNe0

  -- FM = TP / sqrt((TP+FP)*(TP+FN))
  have hNonneg1 : 0 ≤ TP + FP := le_of_lt hTPFPpos
  have hNonneg2 : 0 ≤ TP + FN := le_of_lt hTPFNpos
  have hPPVden : TP + FP ≠ 0 := ne_of_gt hTPFPpos
  have hTPRden : TP + FN ≠ 0 := ne_of_gt hTPFNpos
  have hFM :
      FM TP FP FN = TP / Real.sqrt ((TP + FP) * (TP + FN)) :=
    fm_simplified (TP := TP) (FP := FP) (FN := FN)
      hPPVden hTPRden hNonneg1 hNonneg2 hTP_nonneg

  /- Now we need the algebraic fact that MCC coincides with
     numScaled / denScaled, at least for all sufficiently large TN
     with TN > 0. This is exactly the "multiply numerator and
     denominator by 1/TN and factor" trick from the paper.
  -/
  have hRewritePointwise
      (TN : ℝ) (hTNpos : 0 < TN) :
      MCC TP TN FP FN = numScaled TN / denScaled TN := by
    have hTNne : TN ≠ 0 := ne_of_gt hTNpos
    -- Expand MCC
    unfold MCC
    simp only
    -- Numerator: TP*TN - FP*FN = TN * (TP - FP*FN/TN)
    have hNum :
        TP * TN - FP * FN = TN * (TP - FP * FN / TN) := by
      field_simp [hTNne, mul_comm, mul_left_comm, mul_assoc]
    -- Denominator: relate the "raw" expression with the scaled one, via dividing by TN.
    -- Let A = (TP+FP)*(TP+FN), B = (TN+FP)/TN, C = (TN+FN)/TN.
    set A : ℝ := (TP + FP) * (TP + FN) with hAdef
    have hApos : 0 < A := by
      simpa [hAdef, mul_comm, mul_left_comm, mul_assoc] using
        (mul_pos hTPFPpos hTPFNpos)
    have hAnonneg : 0 ≤ A := le_of_lt hApos

    have hDen_sq :
        ((Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) ^ 2)
          = A * ((TN + FP) / TN) * ((TN + FN) / TN) := by
      -- LHS: (sqrt(X) / TN)^2 = X / TN^2
      have hTNpos' : 0 < TN^2 := by
        -- TN^2 > 0 because TN ≠ 0
        have : TN^2 = TN * TN := by ring
        have h0 : (0 : ℝ) < TN * TN := mul_pos hTNpos hTNpos
        simpa [pow_two, this] using h0
      have hDen_nonneg :
          0 ≤ A * (TN + FP) * (TN + FN) := by
        have hApos : 0 < A := by
          have := mul_pos hTPFPpos hTPFNpos
          simpa [hAdef, mul_comm, mul_left_comm, mul_assoc] using this
        have hA_nonneg : 0 ≤ A := le_of_lt hApos
        -- Now we use 0 < TN and 0 ≤ FP, 0 ≤ FN
        have h1 : 0 ≤ TN + FP := by
          have hTN_nonneg : 0 ≤ TN := le_of_lt hTNpos
          exact add_nonneg hTN_nonneg hFP_nonneg
        have h2 : 0 ≤ TN + FN := by
          have hTN_nonneg : 0 ≤ TN := le_of_lt hTNpos
          exact add_nonneg hTN_nonneg hFN_nonneg
        have h3 := mul_nonneg h1 h2
        have := mul_nonneg hA_nonneg h3
        simpa [hAdef, mul_comm, mul_left_comm, mul_assoc] using this
      -- First rewrite (sqrt(X)/TN)^2 as X / TN^2.
      calc
        (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) ^ 2
            = (Real.sqrt (A * (TN + FP) * (TN + FN))) ^ 2 / TN ^ 2 := by
                -- (a/b)^2 = a^2 / b^2
                -- FIXME: this is `sq_div` or can be shown by `field_simp`+`ring`.
                simpa [div_eq_mul_inv] using (div_pow (Real.sqrt (A * (TN + FP) * (TN + FN))) TN (2 : ℕ))
        _   = (A * (TN + FP) * (TN + FN)) / TN ^ 2 := by
                -- (sqrt X)^2 = X (since X ≥ 0)
                -- lemma: `Real.sq_sqrt` or `Real.mul_self_sqrt` with nonneg assumption.
                -- FIXME: replace with the correct lemma, e.g. `by simpa using Real.sq_sqrt hDenNonneg`.
                have hsq :
                    (Real.sqrt (A * (TN + FP) * (TN + FN))) ^ 2 =
                      A * (TN + FP) * (TN + FN) :=
                  Real.sq_sqrt hDen_nonneg
                simp [hsq]
        _   = A * ((TN + FP) / TN) * ((TN + FN) / TN) := by
                -- pure field algebra: move TN^2 into the denominators.
                -- X / TN^2 = A * (TN+FP)*(TN+FN) / TN^2 = A * ((TN+FP)/TN)*((TN+FN)/TN).
                -- This should be a `field_simp` with `hTNne`.
                field_simp [hTNne, pow_two, mul_comm, mul_left_comm, mul_assoc]

    -- Now show that the scaled denominator is exactly `sqrt(...) / TN` for TN>0.
    have hDenScaled_eq :
        denScaled TN
          = Real.sqrt (A * (TN + FP) * (TN + FN)) / TN := by
      -- We know both sides are ≥ 0, and their squares are equal, so they are equal.
      have hDenScaled_nonneg : 0 ≤ denScaled TN := by
        -- sqrt is always ≥ 0
        unfold denScaled
        exact Real.sqrt_nonneg _
      have hRight_nonneg :
          0 ≤ Real.sqrt (A * (TN + FP) * (TN + FN)) / TN := by
        have hSqrtNonneg : 0 ≤ Real.sqrt (A * (TN + FP) * (TN + FN)) :=
          Real.sqrt_nonneg _
        have hTNpos₀ : 0 < TN := hTNpos
        have hTNpos' : 0 ≤ TN := le_of_lt hTNpos₀
        -- dividing a nonnegative by a positive is nonnegative
        have : 0 ≤ (Real.sqrt (A * (TN + FP) * (TN + FN))) / TN :=
          div_nonneg hSqrtNonneg (le_of_lt hTNpos₀)
        exact this
      -- Square both sides and compare with `hDen_sq`.
      have hSq_left :
          (denScaled TN) ^ 2
            = A * ((TN + FP) / TN) * ((TN + FN) / TN) := by
        -- definition of denScaled, then (sqrt x)^2 = x
        unfold denScaled
        have : 0 ≤ (A * ((TN + FP) / TN) * ((TN + FN) / TN)) :=
          by
            -- product of nonnegatives; we know A ≥ 0 and the ratios are ≥ 0 for TN>0.
            have hB : 0 ≤ (TN + FP) / TN :=
              div_nonneg (by linarith) (le_of_lt hTNpos)
            have hC : 0 ≤ (TN + FN) / TN :=
              div_nonneg (by linarith) (le_of_lt hTNpos)
            have := mul_nonneg (mul_nonneg hAnonneg hB) hC
            simpa [mul_comm, mul_left_comm, mul_assoc] using this
        -- lemma: (sqrt x)^2 = x for x ≥ 0, e.g. `Real.sq_sqrt`.
        -- FIXME: replace with correct lemma name; something like:
        have h := Real.sq_sqrt this; simpa using h

      -- Now we have:
      --   (denScaled TN)^2 = RHS
      --   (sqrt(...) / TN)^2 = RHS   (by hDen_sq)
      -- together with both sides ≥ 0, we conclude equality.
      have hEqSq :
          (denScaled TN) ^ 2
            = (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) ^ 2 := by
        -- combine the two equalities to RHS
        have := hDen_sq
        -- FIXME: exact algebra:
        calc
          (denScaled TN) ^ 2
            = A * ((TN + FP) / TN) * ((TN + FN) / TN) := hSq_left
        _   = (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) ^ 2 := by
                simpa using hDen_sq.symm
      -- Use that for nonnegative reals, equality of squares implies equality:
      -- if 0 ≤ x, 0 ≤ y, x^2 = y^2 then x = y.
      -- This lemma exists (something like `sq_eq_sq_iff_eq_of_nonneg`), but
      -- you can also roll your own small lemma if needed.
      -- FIXME: replace with the appropriate lemma; for now we use the pattern:
      --   have := eq_of_mul_self_eq_mul_self_of_nonneg hDenScaled_nonneg hRight_nonneg ?hEq
      -- Use that for nonnegative reals, equality of squares implies equality:
      -- if 0 ≤ x, 0 ≤ y, x^2 = y^2 then x = y.
      -- Use that for reals, x² = y² ↔ x = y ∨ x = -y
      have hcases :
          denScaled TN = Real.sqrt (A * (TN + FP) * (TN + FN)) / TN
          ∨ denScaled TN = - (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) := by
        -- Specialize `sq_eq_sq_iff_eq_or_eq_neg` to our concrete x,y and use hEqSq
        exact
          (sq_eq_sq_iff_eq_or_eq_neg :
              (denScaled TN) ^ 2 =
                  (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) ^ 2
                ↔ denScaled TN =
                      Real.sqrt (A * (TN + FP) * (TN + FN)) / TN
                  ∨ denScaled TN =
                      - (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN)
          ).1 hEqSq

      rcases hcases with h | h
      · -- first case: denScaled TN = RHS
        exact h
      · -- second case: denScaled TN = - RHS; use nonnegativity to conclude RHS = 0
        have hy_le0 :
            Real.sqrt (A * (TN + FP) * (TN + FN)) / TN ≤ 0 := by
          -- from 0 ≤ denScaled TN = -y, we get 0 ≤ -y, hence y ≤ 0
          have hx_nonneg : 0 ≤ denScaled TN := hDenScaled_nonneg
          have hx' :
              0 ≤ -(Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) := by
            simpa [h] using hx_nonneg
          -- 0 ≤ -y ↔ y ≤ 0
          have : Real.sqrt (A * (TN + FP) * (TN + FN)) / TN ≤ 0 :=
            (neg_nonneg).1 hx'
          simpa using this
        have hy_ge0 :
            0 ≤ Real.sqrt (A * (TN + FP) * (TN + FN)) / TN := hRight_nonneg
        have hy0 :
            Real.sqrt (A * (TN + FP) * (TN + FN)) / TN = 0 :=
          le_antisymm hy_le0 hy_ge0
        have hx0 : denScaled TN = 0 := by
          simpa [hy0, neg_zero] using h
        -- both sides are 0, so they are equal
        simp [hx0, hy0]

    -- Now plug num and den equalities back into MCC definition.
    -- MCC = (TP*TN - FP*FN) / sqrt(A*(TN+FP)*(TN+FN))
    --     = TN*(TP - FP*FN/TN) / (TN * denScaled TN) = (TP - FP*FN/TN)/denScaled TN.
    have hDen_nonzero :
        Real.sqrt (A * (TN + FP) * (TN + FN)) ≠ 0 := by
      have h1 : 0 < TN + FP :=
        add_pos_of_pos_of_nonneg hTNpos hFP_nonneg
      have h2 : 0 < TN + FN :=
        add_pos_of_pos_of_nonneg hTNpos hFN_nonneg
      have hApos' : 0 < A := hApos
      have h3 : 0 < (TN + FP) * (TN + FN) := mul_pos h1 h2
      have h4 : 0 < A * ((TN + FP) * (TN + FN)) := mul_pos hApos' h3
      have hInsidePos :
          0 < A * (TN + FP) * (TN + FN) := by
        -- just re-associate
        simpa [mul_comm, mul_left_comm, mul_assoc] using h4
      exact Real.sqrt_ne_zero'.mpr hInsidePos
    have hTNne' : (TN : ℝ) ≠ 0 := hTNne
    calc
      MCC TP TN FP FN
          = (TP * TN - FP * FN) /
            Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) := by
              -- unfold MCC and substitute A
              simp [MCC, mul_comm, mul_left_comm]
      _   = (TP * TN - FP * FN) /
            Real.sqrt (A * (TN + FP) * (TN + FN)) := by
              -- just re-associate factors
              simp [hAdef, mul_comm, mul_left_comm]
      _   = (TN * (TP - FP * FN / TN)) /
            Real.sqrt (A * (TN + FP) * (TN + FN)) := by
              simp [hNum]
      _   = (TP - FP * FN / TN) /
            (Real.sqrt (A * (TN + FP) * (TN + FN)) / TN) := by
              -- factor TN out of the fraction
              -- (TN * X) / Y = X / (Y / TN) provided TN ≠ 0
              field_simp
      _   = (TP - FP * FN / TN) / denScaled TN := by
              simp [hDenScaled_eq]

  -- Now get the eventual equality MCC = numScaled / denScaled on atTop.
  have hRewriteEventually :
      ∀ᶠ TN in atTop,
        MCC TP TN FP FN = numScaled TN / denScaled TN := by
    -- On `atTop`, TN is eventually > 0 (e.g., TN ≥ 1).
    have hPos : ∀ᶠ TN : ℝ in atTop, 0 < TN := by
      refine (eventually_ge_atTop (1 : ℝ)).mono ?_
      intro TN hTN
      have : (0 : ℝ) < 1 := zero_lt_one
      exact lt_of_lt_of_le this hTN
    refine hPos.mono ?_
    intro TN hTN
    exact hRewritePointwise TN hTN

  -- Use `tendsto_congr'` to replace MCC by the scaled version in the limit.
  have hMCC :
      Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop
              (𝓝 (TP / Real.sqrt ((TP + FP) * (TP + FN)))) := by
    -- `hRewriteEventually` is: ∀ᶠ TN, MCC = numScaled/denScaled
    -- `hQuot` is the limit of numScaled/denScaled.
    exact (tendsto_congr' hRewriteEventually).mpr hQuot

  -- Finally rewrite the limit value as FM using hFM.
  simpa [hFM] using hMCC

end ConfusionMatrix
