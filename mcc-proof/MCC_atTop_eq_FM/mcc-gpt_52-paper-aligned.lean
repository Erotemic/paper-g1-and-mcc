import Mathlib.Tactic

/-
This file is a companion Lean proof to the algebraic/prose proof in the paper.

Goal (informal): as the number of true negatives `TN → +∞`,
  `MCC TP TN FP FN → FM TP FP FN`.

Style: we mirror the paper’s *named algebraic steps* (lee_step1/2/3) with lemmas,
then we take limits only after the algebra has been packaged into a single
“post-step-3” expression.

Along the way we add tutorial-style comments the first time a Lean concept
appears (filters, `calc`, `field_simp`, `=ᶠ[atTop]`, ...).
-/

open Filter Topology

/-
`noncomputable section` is a common Mathlib idiom:
we allow classical choice/real analysis facts that are noncomputable.
-/
noncomputable section

/-- Precision (positive predictive value). -/
def PPV (TP FP : ℝ) : ℝ := TP / (TP + FP)

/-- Recall (true positive rate). -/
def TPR (TP FN : ℝ) : ℝ := TP / (TP + FN)

/-- Fowlkes–Mallows index. -/
def FM (TP FP FN : ℝ) : ℝ := √ (PPV TP FP * TPR TP FN)

/-- Matthews correlation coefficient. -/
def MCC (TP TN FP FN : ℝ) : ℝ :=
  (TP * TN - FP * FN) / √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))

/-! ### Generic limit facts used in the “post-step-3” limit -/

/-
### Filters and limits (Lean tutorial)

Lean expresses limits using *filters*.

* `atTop` is the filter corresponding to “tends to +∞”.
* `𝓝 L` (written `\n` then `L`) is the *neighborhood filter* at `L`.

So the Lean statement

  `Tendsto f atTop (𝓝 L)`

means: `f x → L` as `x → +∞`.
-/

/-- `c / x → 0` as `x → +∞`. -/
lemma tendsto_const_div_atTop_nhds_0 (c : ℝ) :
    Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
  -- `tendsto_const_nhds` says a constant function tends to that constant.
  -- `Filter.tendsto_id` says `x ↦ x` tends to `atTop`.
  -- `.div_atTop` is a standard limit rule: `const / x → 0` as `x → +∞`.
  tendsto_const_nhds.div_atTop Filter.tendsto_id

/-- `1 + c/x → 1` as `x → +∞`. -/
lemma tendsto_one_add_const_div_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => (1 : ℝ) + c / x) atTop (𝓝 1) := by
  -- `by` starts a tactic proof.
  -- `simpa` means: simplify the goal using rewriting/simp rules.
  simpa using (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_0 c))

/-- `a - c/x → a` as `x → +∞`. -/
lemma tendsto_const_sub_const_div_atTop (a c : ℝ) :
    Tendsto (fun x : ℝ => a - c / x) atTop (𝓝 a) := by
  simpa using (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_0 c))

/-- `A * (1 + c/x) * (1 + d/x) → A` as `x → +∞`. -/
lemma tendsto_const_mul_one_add_mul_one_add_div_atTop (A c d : ℝ) :
    Tendsto (fun x : ℝ => A * (1 + c / x) * (1 + d / x)) atTop (𝓝 A) := by
  -- `Tendsto.mul` is the multiplication limit rule.
  have h := (tendsto_one_add_const_div_atTop c).mul (tendsto_one_add_const_div_atTop d)
  simpa [mul_assoc] using (tendsto_const_nhds.mul h)

/-- If `a > 0` then `sqrt(a) ≠ 0`. -/
lemma sqrt_of_pos_ne_zero {a : ℝ} (ha : 0 < a) : √ a ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr ha)

/-- `sqrt(x)/t = sqrt(x / t^2)` for `0 ≤ x` and `0 ≤ t`. -/
lemma sqrt_div_eq_sqrt_div_sq {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    √ x / t = √ (x / (t ^ 2)) := by
  -- `aesop` is a small proof-search automation tactic.
  -- We keep this lemma tiny so the main algebraic `calc` chain stays readable.
  aesop

/-! ### Algebraic steps (mirrors Eq. (lee_step1/2/3) in the paper) -/

/-
### Algebra (Lean tutorial)

* `simp [defs]` unfolds definitions and simplifies.
* `field_simp [h]` clears denominators in rational expressions, using hypotheses
  like `h : TN ≠ 0` to justify division.
* `calc` is Lean’s equational reasoning block.  It reads like a chain of
  equalities/rewrites, matching the paper’s line-by-line algebra.
-/

/-- Eq. (lee_step1): divide numerator and denominator by `TN`. -/
lemma mcc_lee_step1 (TP TN FP FN : ℝ) (hTN : TN ≠ 0) :
    MCC TP TN FP FN
      =
    ((TP * TN - FP * FN) / TN) /
      (√ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN) := by
  -- After unfolding `MCC`, this is “multiply numerator and denominator by 1/TN”.
  simp [MCC]
  field_simp [hTN]

/-- Eq. (lee_step2), numerator: `(TP*TN - FP*FN)/TN = TP - FP*FN/TN`. -/
lemma mcc_lee_step2 (TP TN FP FN : ℝ) (hTN : TN ≠ 0) :
    (TP * TN - FP * FN) / TN = TP - FP * FN / TN := by
  field_simp [hTN]

/-- Eq. (lee_step3), denominator: rewrite `((TN+FP)/TN)` as `(1 + FP/TN)` (and same for `FN`). -/
lemma mcc_lee_step3
    (TP TN FP FN : ℝ)
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hFP_ge0 : 0 ≤ FP)
    (hFN_ge0 : 0 ≤ FN)
    (hTNpos : 0 < TN) :
    √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN
      =
    √ (((TP + FP) * (TP + FN)) * (1 + FP / TN) * (1 + FN / TN)) := by
  -- `let` introduces a local definition (like a “where”/“set” in the prose proof).
  let A : ℝ := (TP + FP) * (TP + FN)
  let D : ℝ := (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)

  -- `have` introduces an intermediate claim with a name.
  have hD_ge0 : 0 ≤ D := by
    -- `positivity` is a tactic that proves nonnegativity/positivity goals.
    simp [D]; positivity

  -- This identity is the literal Lean version of the paper’s Step-3 rewrite:
  --   (TN+FP)/TN = 1 + FP/TN   and   (TN+FN)/TN = 1 + FN/TN.
  have h_inside :
      D / (TN ^ 2) = A * (1 + FP / TN) * (1 + FN / TN) := by
    simp [A, D]
    field_simp [hTNpos.ne']

  -- `calc` chains together the substeps, matching the paper line-by-line.
  calc
    √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN
        = √ D / TN := by simp [D]
    _   = √ (D / (TN ^ 2)) := by
            simpa [D] using (sqrt_div_eq_sqrt_div_sq (x := D) (t := TN) hD_ge0 hTNpos.le)
    _   = √ (A * (1 + FP / TN) * (1 + FN / TN)) := by simpa [h_inside]
    _   = √ (((TP + FP) * (TP + FN)) * (1 + FP / TN) * (1 + FN / TN)) := by simp [A]

/-- “Post step 3” closed form (the body of Eq. (lee_step3)). -/
def post_step3 (TP TN FP FN : ℝ) : ℝ :=
  let A : ℝ := (TP + FP) * (TP + FN)
  (TP - FP * FN / TN) / √ (A * (1 + FP / TN) * (1 + FN / TN))

/-- Combine Eq. (lee_step1/2/3): for `TN > 0`, `MCC = post_step3`. -/
lemma mcc_eq_post_step3
    (TP TN FP FN : ℝ)
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hFP_ge0 : 0 ≤ FP)
    (hFN_ge0 : 0 ≤ FN)
    (hTNpos : 0 < TN) :
    MCC TP TN FP FN = post_step3 TP TN FP FN := by
  let A : ℝ := (TP + FP) * (TP + FN)
  have h1 := mcc_lee_step1 TP TN FP FN hTNpos.ne'
  have h2 := mcc_lee_step2 TP TN FP FN hTNpos.ne'
  have h3 := mcc_lee_step3 TP TN FP FN hTPFPpos hTPFNpos hFP_ge0 hFN_ge0 hTNpos

  -- The `calc` chain below is the Lean companion to the paper’s Eq. (lee_step1/2/3).
  calc
    MCC TP TN FP FN
        = ((TP * TN - FP * FN) / TN) /
            (√ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN) := h1
    _   = (TP - FP * FN / TN) /
            (√ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN) := by
            simpa [h2]
    _   = (TP - FP * FN / TN) /
            √ (A * (1 + FP / TN) * (1 + FN / TN)) := by
            simpa [A, h3]
    _   = post_step3 TP TN FP FN := by simp [post_step3, A]

/-! ### Main limit theorem -/

/-
### “Eventually equal” and taking the limit (Lean tutorial)

After we finish the algebra, we avoid manipulating limits inside the MCC
expression directly.  Instead we prove an *eventual equality*:

  `(fun TN => MCC ...) =ᶠ[atTop] (fun TN => post_step3 ...)`

Read `=ᶠ[atTop]` as: “for all sufficiently large TN, the two functions agree”.

Then we:
1. compute the limit of `post_step3`,
2. transfer that limit back to `MCC` using `Tendsto.congr'`.
-/

theorem tendsto_MCC_atTop_eq_FM2
    {TP FP FN : ℝ}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_ge0 : 0 ≤ TP)
    (hFP_ge0 : 0 ≤ FP)
    (hFN_ge0 : 0 ≤ FN) :
    Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (FM TP FP FN)) := by

  let A : ℝ := (TP + FP) * (TP + FN)

  -- “Work inside the limit”: for all sufficiently large `TN` (here: all `TN > 0`),
  -- we have `MCC = post_step3`.
  have h_eq :
      (fun TN : ℝ => MCC TP TN FP FN) =ᶠ[atTop] (fun TN => post_step3 TP TN FP FN) := by
    -- `filter_upwards` is a convenient way to prove an “eventually” statement.
    -- It gives us an arbitrary `TN` together with the hypothesis `0 < TN`.
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with TN hTNpos
    simpa using (mcc_eq_post_step3 TP TN FP FN hTPFPpos hTPFNpos hFP_ge0 hFN_ge0 hTNpos)

  ----------------------------------------------------------------------
  -- Limit of the post-step-3 expression (“postlimit” simplification)
  ----------------------------------------------------------------------

  -- Numerator: `TP - (FP*FN)/TN → TP`.
  have h_num :
      Tendsto (fun TN : ℝ => TP - FP * FN / TN) atTop (𝓝 TP) :=
    tendsto_const_sub_const_div_atTop TP (FP * FN)

  -- Denominator (inside sqrt): `A * (1 + FP/TN) * (1 + FN/TN) → A`.
  have h_den_inside :
      Tendsto (fun TN : ℝ => A * (1 + FP / TN) * (1 + FN / TN)) atTop (𝓝 A) := by
    simpa using (tendsto_const_mul_one_add_mul_one_add_div_atTop A FP FN)

  -- Taking `sqrt` is continuous on `ℝ`, so we can map limits through `sqrt`.
  have h_den :
      Tendsto (fun TN : ℝ => √ (A * (1 + FP / TN) * (1 + FN / TN))) atTop (𝓝 (√ A)) :=
    (Filter.Tendsto.sqrt h_den_inside)

  -- The quotient limit rule requires the limiting denominator to be nonzero.
  have h_den_ne : √ A ≠ 0 := by
    have hApos : 0 < A := by simpa [A] using (mul_pos hTPFPpos hTPFNpos)
    exact sqrt_of_pos_ne_zero hApos

  -- Quotient limit rule: if `num → Num` and `den → Den` with `Den ≠ 0`, then `num/den → Num/Den`.
  have h_post :
      Tendsto (fun TN : ℝ => post_step3 TP TN FP FN) atTop (𝓝 (TP / √ A)) := by
    -- `simpa` expands `post_step3` into `num / den`.
    simpa [post_step3, A] using (Filter.Tendsto.div h_num h_den h_den_ne)

  -- Transfer the limit from `post_step3` back to `MCC` using eventual equality.
  have h_mcc :
      Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (TP / √ A)) :=
    h_post.congr' (Filter.EventuallyEq.symm h_eq)

  ----------------------------------------------------------------------
  -- Rewrite FM into the same closed form `TP / √A`.
  ----------------------------------------------------------------------

  have h_FM : FM TP FP FN = TP / √ A := by
    -- `field_simp` is the workhorse for simplifying rational expressions.
    have hmul :
        TP / (TP + FP) * (TP / (TP + FN)) =
          (TP ^ 2) / ((TP + FP) * (TP + FN)) := by
      field_simp [hTPFPpos.ne', hTPFNpos.ne']

    -- `simp_all` runs `simp` using *all* local hypotheses.
    -- Here it uses `hTP_ge0` to simplify `sqrt (TP^2)` to `TP`.
    simp_all [FM, PPV, TPR, A]

  -- Replace the target limit value `TP/√A` by the equal expression `FM`.
  simpa [h_FM] using h_mcc


/-
Main limit theorem:
If TP, FP, and FN are fixed, then as TN → +∞,
the Matthews correlation coefficient converges to the Fowlkes–Mallows index:

  MCC(TP, TN, FP, FN) → FM(TP, FP, FN)  as  TN → +∞.

Lean expresses limits using *filters*:
* `atTop` is the filter corresponding to “the variable tends to +∞”
* `𝓝 L` is the neighborhood filter at `L`, meaning “values arbitrarily close to L”

So the Lean statement: `Tendsto f atTop (𝓝 L)` means `L = lim_{x → ∞} f(x)`
-/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : ℝ}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_ge0 : 0 ≤ TP)
    (hFP_ge0 : 0 ≤ FP)
    (hFN_ge0 : 0 ≤ FN) :
    Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (FM TP FP FN)) := by
  sorry

  
  let A : ℝ := (TP + FP) * (TP + FN)

  -- “Work inside the limit”: for all sufficiently large `TN` (here: all `TN > 0`),
  -- we have `MCC = post_step3`.
  have h_eq :
      (fun TN : ℝ => MCC TP TN FP FN) =ᶠ[atTop] (fun TN => post_step3 TP TN FP FN) := by
    -- `filter_upwards` is a convenient way to prove an “eventually” statement.
    -- It gives us an arbitrary `TN` together with the hypothesis `0 < TN`.
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with TN hTNpos
    simpa using (mcc_eq_post_step3 TP TN FP FN hTPFPpos hTPFNpos hFP_ge0 hFN_ge0 hTNpos)

  ----------------------------------------------------------------------
  -- Limit of the post-step-3 expression (“postlimit” simplification)
  ----------------------------------------------------------------------

  -- Numerator: `TP - (FP*FN)/TN → TP`.
  have h_num :
      Tendsto (fun TN : ℝ => TP - FP * FN / TN) atTop (𝓝 TP) :=
    tendsto_const_sub_const_div_atTop TP (FP * FN)

  -- Denominator (inside sqrt): `A * (1 + FP/TN) * (1 + FN/TN) → A`.
  have h_den_inside :
      Tendsto (fun TN : ℝ => A * (1 + FP / TN) * (1 + FN / TN)) atTop (𝓝 A) := by
    simpa using (tendsto_const_mul_one_add_mul_one_add_div_atTop A FP FN)

  -- Taking `sqrt` is continuous on `ℝ`, so we can map limits through `sqrt`.
  have h_den :
      Tendsto (fun TN : ℝ => √ (A * (1 + FP / TN) * (1 + FN / TN))) atTop (𝓝 (√ A)) :=
    (Filter.Tendsto.sqrt h_den_inside)

  -- The quotient limit rule requires the limiting denominator to be nonzero.
  have h_den_ne : √ A ≠ 0 := by
    have hApos : 0 < A := by simpa [A] using (mul_pos hTPFPpos hTPFNpos)
    exact sqrt_of_pos_ne_zero hApos

  -- Quotient limit rule: if `num → Num` and `den → Den` with `Den ≠ 0`, then `num/den → Num/Den`.
  have h_post :
      Tendsto (fun TN : ℝ => post_step3 TP TN FP FN) atTop (𝓝 (TP / √ A)) := by
    -- `simpa` expands `post_step3` into `num / den`.
    simpa [post_step3, A] using (Filter.Tendsto.div h_num h_den h_den_ne)

  -- Transfer the limit from `post_step3` back to `MCC` using eventual equality.
  have h_mcc :
      Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (TP / √ A)) :=
    h_post.congr' (Filter.EventuallyEq.symm h_eq)

  ----------------------------------------------------------------------
  -- Rewrite FM into the same closed form `TP / √A`.
  ----------------------------------------------------------------------

  have h_FM : FM TP FP FN = TP / √ A := by
    -- `field_simp` is the workhorse for simplifying rational expressions.
    have hmul :
        TP / (TP + FP) * (TP / (TP + FN)) =
          (TP ^ 2) / ((TP + FP) * (TP + FN)) := by
      field_simp [hTPFPpos.ne', hTPFNpos.ne']

    -- `simp_all` runs `simp` using *all* local hypotheses.
    -- Here it uses `hTP_ge0` to simplify `sqrt (TP^2)` to `TP`.
    simp_all [FM, PPV, TPR, A]

  -- Replace the target limit value `TP/√A` by the equal expression `FM`.
  simpa [h_FM] using h_mcc