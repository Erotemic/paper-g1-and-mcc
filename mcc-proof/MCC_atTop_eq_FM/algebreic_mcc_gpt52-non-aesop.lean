import Mathlib.Tactic
open Filter Topology

noncomputable section

/-- Precision (positive predictive value): TP / (TP + FP). -/
def PPV (TP FP : ℝ) : ℝ :=
  TP / (TP + FP)

/-- Recall (true positive rate): TP / (TP + FN). -/
def TPR (TP FN : ℝ) : ℝ :=
  TP / (TP + FN)

/-- Fowlkes–Mallows index: sqrt(PPV * TPR). -/
def FM (TP FP FN : ℝ) : ℝ :=
  Real.sqrt (PPV TP FP * TPR TP FN)

/-- Matthews correlation coefficient (MCC). -/
def MCC (TP TN FP FN : ℝ) : ℝ :=
  (TP * TN - FP * FN) /
    Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))

/-
Limits in Lean are expressed with filters.

`Tendsto f atTop (𝓝 L)` can be read as:
  "as the input variable grows without bound (`atTop`), the values `f x`
   get arbitrarily close to `L`."

Here `𝓝 L` is the neighborhood filter at `L`.
Informally, `U ∈ 𝓝 L` means "U contains an open interval around L".
So `Tendsto f atTop (𝓝 L)` means:
  for every neighborhood U of L, there is a threshold T such that
  for all x ≥ T, we have f x ∈ U.
-/
lemma tendsto_const_div_atTop_nhds_0 (c : ℝ) :
    Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Filter.tendsto_id

/-- If c/x → 0 then 1 + c/x → 1 (limit rule for addition). -/
lemma tendsto_one_add_const_div_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => (1 : ℝ) + c / x) atTop (𝓝 1) := by
  simpa using (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_0 c))

/-- If c/x → 0 then a - c/x → a (limit rule for subtraction). -/
lemma tendsto_const_sub_const_div_atTop (a c : ℝ) :
    Tendsto (fun x : ℝ => a - c / x) atTop (𝓝 a) := by
  simpa using (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_0 c))

/-
If (1 + c/x) → 1 and (1 + d/x) → 1, then their product → 1.
This is the limit rule for multiplication.
-/
lemma tendsto_mul_one_add_const_div_atTop (c d : ℝ) :
    Tendsto (fun x : ℝ => (1 + c / x) * (1 + d / x)) atTop (𝓝 1) := by
  simpa using (tendsto_one_add_const_div_atTop c).mul (tendsto_one_add_const_div_atTop d)

/-
A common pattern: A * (1 + c/x) * (1 + d/x) → A.
(Here A is constant, and the parenthesized factors both tend to 1.)
-/
lemma tendsto_const_mul_one_add_mul_one_add_div_atTop (A c d : ℝ) :
    Tendsto (fun x : ℝ => A * (1 + c / x) * (1 + d / x)) atTop (𝓝 A) := by
  have hA : Tendsto (fun _ : ℝ => A) atTop (𝓝 A) := tendsto_const_nhds
  have hprod :
      Tendsto (fun x : ℝ => (1 + c / x) * (1 + d / x)) atTop (𝓝 1) :=
    tendsto_mul_one_add_const_div_atTop c d
  have h := hA.mul hprod
  -- Normalize the function shape and the limit value (A * 1 = A).
  simpa [mul_assoc] using h

/-
Continuity of sqrt: if g(x) → G then sqrt(g(x)) → sqrt(G).
We specialize it to the previous lemma’s pattern.
-/
lemma tendsto_sqrt_const_mul_one_add_mul_one_add_div_atTop (A c d : ℝ) :
    Tendsto (fun x : ℝ => Real.sqrt (A * (1 + c / x) * (1 + d / x)))
      atTop (𝓝 (Real.sqrt A)) := by
  simpa using (Filter.Tendsto.sqrt (tendsto_const_mul_one_add_mul_one_add_div_atTop A c d))

/-- If a > 0 then sqrt(a) ≠ 0 (since sqrt(a) > 0). -/
lemma sqrt_ne_zero_of_pos {a : ℝ} (ha : 0 < a) : Real.sqrt a ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr ha)

/-
A generic algebraic step used in the denominator manipulation:

  sqrt(x) / t = sqrt(x / t^2)   (assuming 0 ≤ x and 0 ≤ t).

This packages the common “rewrite t as sqrt(t^2), then use sqrt_div” move.
-/
lemma sqrt_div_eq_sqrt_div_sq {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    Real.sqrt x / t = Real.sqrt (x / (t ^ 2)) := by
    simp_all only [Real.sqrt_div, Real.sqrt_sq]

/-- Main theorem. -/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : ℝ}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_nonneg : 0 ≤ TP)
    (hFP_nonneg : 0 ≤ FP)
    (hFN_nonneg : 0 ≤ FN) :
    Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (FM TP FP FN)) := by

  /-
  A “hypothesis” is an assumed fact provided by the theorem statement.
  For example, `hTPFPpos : 0 < TP + FP` is available anywhere below, and it can be
  used to justify steps such as dividing by (TP + FP), since positivity implies nonzero.
  -/

  -- Abbreviation used in the limit stage:
  let A : ℝ := (TP + FP) * (TP + FN)

  -- The expression after the Step-3 rewrite, defined locally:
  let post_step3 : ℝ → ℝ := fun TN =>
    (TP - FP * FN / TN) / Real.sqrt (A * (1 + FP / TN) * (1 + FN / TN))

  ----------------------------------------------------------------------
  -- Step 1/2/3 algebraic rewrite: for TN > 0, MCC(TN) = post_step3(TN).
  ----------------------------------------------------------------------

  /-
  `Filter.EventuallyEq atTop f g` means: f(TN) = g(TN) for all sufficiently large TN.
  This is how we formalize “for large TN” in a way that lets us divide by TN (TN ≠ 0).
  -/
  have h_steps :
      Filter.EventuallyEq atTop
        (fun TN : ℝ => MCC TP TN FP FN)
        post_step3 := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with TN hTN
    have hTN0 : TN ≠ 0 := ne_of_gt hTN
    have hTNle : 0 ≤ TN := le_of_lt hTN

    -- Unfold MCC and post_step3; the goal becomes a concrete algebraic identity.
    simp [MCC, post_step3, A]

    -- Distribute 1/TN into the numerator.
    have h_num :
        (TP * TN - FP * FN) / TN =
        TP - FP * FN / TN := by
      field_simp [hTN0]

    -- Rewrite (TN + FP)/TN and (TN + FN)/TN as 1 + FP/TN and 1 + FN/TN.
    have h_inside :
        ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / (TN ^ 2) =
        (TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN) := by
      field_simp [hTN0]

    -- Side condition needed for sqrt_div: the numerator inside sqrt is ≥ 0.
    have hx :
        0 ≤ (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN) := by
      positivity

    -- Pull the factor 1/TN through sqrt using the packaged lemma `sqrt_div_eq_sqrt_div_sq`.
    have h_sqrt :
        Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN =
        Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN)) := by
      calc
        Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN =
          Real.sqrt (((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / (TN ^ 2)) := by
            simpa using
              (sqrt_div_eq_sqrt_div_sq hx hTNle : Real.sqrt _ / TN = Real.sqrt (_ / (TN ^ 2)))
        _ =
          Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN)) := by
            simp [h_inside]

    -- Combine the rewrite into the final fraction identity (divide numerator & denominator by TN).
    calc
      (TP * TN - FP * FN) /
          Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) =
        ((TP * TN - FP * FN) / TN) /
          (Real.sqrt ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN) := by
            field_simp [hTN0]
      _ =
        (TP - FP * FN / TN) /
          Real.sqrt ((TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN)) := by
            simp [h_num, h_sqrt]

  ----------------------------------------------------------------------
  -- Limit of post_step3: bundle the “c/TN → 0” work using generic lemmas.
  ----------------------------------------------------------------------

  -- Numerator: TP - (FP*FN)/TN → TP.
  have h_num_lim :
      Tendsto (fun TN : ℝ => TP - FP * FN / TN) atTop (𝓝 TP) := by
    -- This is `a - c/TN → a` with a=TP and c=FP*FN.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_const_sub_const_div_atTop TP (FP * FN))

  -- Denominator: sqrt(A * (1 + FP/TN) * (1 + FN/TN)) → sqrt(A).
  have h_den_lim :
      Tendsto (fun TN : ℝ => Real.sqrt (A * (1 + FP / TN) * (1 + FN / TN)))
        atTop (𝓝 (Real.sqrt A)) :=
    tendsto_sqrt_const_mul_one_add_mul_one_add_div_atTop A FP FN

  have h_den_ne : Real.sqrt A ≠ 0 := by
    have hApos : 0 < A := by
      -- A = (TP+FP)(TP+FN) and both factors are positive.
      simpa [A] using (mul_pos hTPFPpos hTPFNpos)
    exact sqrt_ne_zero_of_pos hApos

  /-
  Quotient limit rule:
    if num(TN) → Num and den(TN) → Den with Den ≠ 0,
    then (num/den)(TN) → Num/Den.
  Lean’s lemma is `Filter.Tendsto.div`.
  -/
  have h_post_lim :
      Tendsto post_step3 atTop (𝓝 (TP / Real.sqrt A)) := by
    exact Filter.Tendsto.div h_num_lim h_den_lim h_den_ne

  -- Transfer the limit back from post_step3 to MCC using eventual equality.
  have h_mcc_lim :
      Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (TP / Real.sqrt A)) := by
    exact h_post_lim.congr' (Filter.EventuallyEq.symm h_steps)

  ----------------------------------------------------------------------
  -- FM rearrangement: FM = TP / sqrt((TP+FP)(TP+FN)) = TP / sqrt(A).
  ----------------------------------------------------------------------
  have h_FM :
      FM TP FP FN = TP / Real.sqrt A := by
    unfold FM PPV TPR
    have h1 : TP + FP ≠ 0 := hTPFPpos.ne'
    have h2 : TP + FN ≠ 0 := hTPFNpos.ne'

    have hfrac :
        TP / (TP + FP) * (TP / (TP + FN)) =
        (TP ^ 2) / ((TP + FP) * (TP + FN)) := by
      field_simp [h1, h2]

    calc
      Real.sqrt (TP / (TP + FP) * (TP / (TP + FN))) =
        Real.sqrt ((TP ^ 2) / ((TP + FP) * (TP + FN))) := by simp [hfrac]
      _ =
        Real.sqrt (TP ^ 2) / Real.sqrt ((TP + FP) * (TP + FN)) := by
          simpa using
            (Real.sqrt_div (by positivity : 0 ≤ (TP ^ 2)) ((TP + FP) * (TP + FN)))
      _ =
        TP / Real.sqrt ((TP + FP) * (TP + FN)) := by
          simp [Real.sqrt_sq hTP_nonneg]
      _ =
        TP / Real.sqrt A := by
          simp [A]

  simpa [h_FM] using h_mcc_lim
