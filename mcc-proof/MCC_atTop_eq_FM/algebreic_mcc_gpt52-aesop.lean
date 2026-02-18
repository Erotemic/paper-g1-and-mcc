import Mathlib.Tactic
open Filter Topology

noncomputable section

/-- Precision (positive predictive value) -/
def PPV (TP FP : ℝ) : ℝ := TP / (TP + FP)

/-- Recall (true positive rate) -/
def TPR (TP FN : ℝ) : ℝ := TP / (TP + FN)

/-- Fowlkes–Mallows index -/
def FM (TP FP FN : ℝ) : ℝ := √ (PPV TP FP * TPR TP FN)

/-- Matthews correlation coefficient -/
def MCC (TP TN FP FN : ℝ) : ℝ :=
  (TP * TN - FP * FN) / √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))

/- We start by defining lemmas proving generic facts that will be useful later on -/

/-- The basic fact `c / x → 0` as `x → +∞`.
Limits in Lean are expressed with filters.
`Tendsto f atTop (𝓝 L)` is the Lean form of `lim_{x → +∞} f x = L`. -/
lemma tendsto_const_div_atTop_nhds_0 (c : ℝ) :
    Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Filter.tendsto_id

/-- If `c/x → 0` then `1 + c/x → 1` (limit rule for addition). -/
lemma tendsto_one_add_const_div_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => (1 : ℝ) + c / x) atTop (𝓝 1) := by
  simpa using (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_0 c))

/-- If `c/x → 0` then `a - c/x → a` (limit rule for subtraction). -/
lemma tendsto_const_sub_const_div_atTop (a c : ℝ) :
    Tendsto (fun x : ℝ => a - c / x) atTop (𝓝 a) := by
  simpa using (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_0 c))

/- A common pattern we will use: `A * (1 + c/x) * (1 + d/x) → A`.
This is just the limit rule for multiplication, plus the fact that constants tend to
themselves, and `(1 + c/x) → 1`.-/
lemma tendsto_const_mul_one_add_mul_one_add_div_atTop (A c d : ℝ) :
    Tendsto (fun x : ℝ => A * (1 + c / x) * (1 + d / x)) atTop (𝓝 A) := by
  have := (tendsto_one_add_const_div_atTop c).mul (tendsto_one_add_const_div_atTop d)
  simpa [mul_assoc] using (tendsto_const_nhds.mul this)

/-- If `a > 0` then `sqrt(a) ≠ 0` (since `sqrt(a) > 0`).
In Lean, a theorem or lemma is stated in the context of named hypotheses
(assumptions). Read this as: given the condition `h_agt0` the following claim is true. -/
lemma sqrt_of_pos_ne_zero {a : ℝ} (h_agt0 : 0 < a) : √ a ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr h_agt0)

/- A generic algebraic step used in the MCC denominator manipulation.
`sqrt(x) / t = sqrt(x / t^2)`  (assuming `0 ≤ x` and `0 ≤ t`).
`aesop` (Automated Extensible Search for Obvious Proofs) is an automation tactic.
It performs a small proof search using simp rules and standard lemmas. -/
lemma sqrt_div_eq_sqrt_div_sq {x t : ℝ} (h_xge0 : 0 ≤ x) (h_tge0 : 0 ≤ t) :
    √ x / t = √ (x / (t ^ 2)) := by aesop

/--
Main theorem: as the number of true negatives `TN` tends to `+∞`,
the MCC tends to the FM index (informally, `lim_{TN → ∞} MCC = FM`). -/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : ℝ}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_geq0 : 0 ≤ TP)
    (hFP_geq0 : 0 ≤ FP)
    (hFN_geq0 : 0 ≤ FN) :
    Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (FM TP FP FN)) := by
  -- `A` is the constant factor that does not depend on TN.
  let A : ℝ := (TP + FP) * (TP + FN)
  -- This is the “post step 3” expression: the same one that appears in the algebraic limit.
  let post_step3 : ℝ → ℝ := fun TN =>
    (TP - FP * FN / TN) / √ (A * (1 + FP / TN) * (1 + FN / TN))
  ----------------------------------------------------------------------
  -- Step 1/2/3 algebraic rewrite: for TN > 0, MCC(TN) = post_step3(TN).
  ----------------------------------------------------------------------
  -- `f =ᶠ[atTop] g` means: `f TN` eventually equals `g TN` for all sufficiently large `TN`.
  have h_steps_123 :
      (fun TN : ℝ => MCC TP TN FP FN) =ᶠ[atTop] post_step3 := by
    -- `filter_upwards` is a convenient way to work with “eventually” statements.
    -- Here it gives us an arbitrary `TN` with the assumption `0 < TN`.
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with TN hTN_gt0

    -- After unfolding, the goal is a concrete identity between real expressions.
    simp [MCC, post_step3, A]
    -- Step 2: distribute the factor `1/TN` into the numerator.
    have h_num : (TP * TN - FP * FN) / TN = TP - FP * FN / TN := by
      field_simp [hTN_gt0.ne'] -- `field_simp` clears denominators; it needs `TN ≠ 0`.
    -- Step 3: rewrite `(TN + FP)/TN` as `1 + FP/TN`, similarly for `FN`.
    have h_inside :
        ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / (TN ^ 2) =
          (TP + FP) * (TP + FN) * (1 + FP / TN) * (1 + FN / TN) := by field_simp [hTN_gt0.ne']
    -- Name the large product under the MCC square root.
    let mcc_inside_denom : ℝ := (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)
    -- Side condition needed to move division under `sqrt`.
    have hDenomGe0 : 0 ≤ mcc_inside_denom := by simp [mcc_inside_denom]; positivity
    -- Denominator rewrite: push `/TN` inside `sqrt`, then substitute the Step-3 identity.
    have h_sqrt :
        √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN =
          √ (A * (1 + FP / TN) * (1 + FN / TN)) := by
      simpa [mcc_inside_denom, A] using
        (sqrt_div_eq_sqrt_div_sq (x := mcc_inside_denom) (t := TN) hDenomGe0 hTN_gt0.le).trans
          (by aesop)
    -- Final algebraic combination: divide numerator and denominator by TN.
    calc
      (TP * TN - FP * FN) / √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) =
        ((TP * TN - FP * FN) / TN) /
          (√ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN) := by field_simp [hTN_gt0.ne']
      _ = (TP - FP * FN / TN) / √ (A * (1 + FP / TN) * (1 + FN / TN)) := by aesop
  ----------------------------------------------------------------------
  -- Limit of post_step3: as TN → +∞, the small fractions FP/TN and FN/TN go to 0.
  ----------------------------------------------------------------------
  -- Numerator limit: `TP - (FP*FN)/TN → TP`.
  have h_num_lim :
      Tendsto (fun TN : ℝ => TP - FP * FN / TN) atTop (𝓝 TP) :=
    tendsto_const_sub_const_div_atTop TP (FP * FN)
  -- Denominator limit: `sqrt(A * (1 + FP/TN) * (1 + FN/TN)) → sqrt(A)`.
  have h_den_lim :
      Tendsto (fun TN : ℝ => √ (A * (1 + FP / TN) * (1 + FN / TN))) atTop (𝓝 (√ A)) :=
      by simpa using
       (Filter.Tendsto.sqrt (tendsto_const_mul_one_add_mul_one_add_div_atTop A FP FN))
  -- The quotient limit rule needs the limit denominator to be nonzero.
  have h_den_ne : √ A ≠ 0 := by
     have hApos : 0 < A := by simpa [A] using (mul_pos hTPFPpos hTPFNpos)
     exact sqrt_of_pos_ne_zero hApos
  -- Quotient limit rule: if num → Num and den → Den with Den ≠ 0, then num/den → Num/Den.
  have h_post_lim : Tendsto post_step3 atTop (𝓝 (TP / √ A)) := by
    exact Filter.Tendsto.div h_num_lim h_den_lim h_den_ne
  -- Transfer the limit from `post_step3` back to `MCC` using eventual equality.
  have h_mcc_lim :
      Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (TP / √ A)) := by
    exact h_post_lim.congr' (Filter.EventuallyEq.symm h_steps_123)
  ----------------------------------------------------------------------
  -- Rewrite FM into the same closed form `TP / sqrt(A)`.
  ----------------------------------------------------------------------
  have h_FM : FM TP FP FN = TP / √ A := by
    have: TP / (TP + FP) * (TP / (TP + FN)) = (TP ^ 2) / ((TP + FP) * (TP + FN)) := by
      field_simp [hTPFPpos.ne', hTPFNpos.ne']
    simp_all [FM, PPV, TPR, A]
  /- `h_mcc_lim` shows the limit is `TP / sqrt A`. `h_FM` shows `FM` can be rewritten as the same
  value. Substituting this rewrite into the target of `h_mcc_lim` completes the proof. -/
  simpa [h_FM] using h_mcc_lim
