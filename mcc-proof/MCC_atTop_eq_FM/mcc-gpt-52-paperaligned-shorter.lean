import Mathlib.Tactic
open Filter Topology

noncomputable section

/-- Precision (positive predictive value). -/
def PPV (TP FP : ℝ) : ℝ := TP / (TP + FP)

/-- Recall (true positive rate). -/
def TPR (TP FN : ℝ) : ℝ := TP / (TP + FN)

/-- Fowlkes–Mallows index. -/
def FM (TP FP FN : ℝ) : ℝ :=
    √ (PPV TP FP * TPR TP FN)

/-- Matthews correlation coefficient. -/
def MCC (TP TN FP FN : ℝ) : ℝ :=
  (TP * TN - FP * FN) / √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))

/-!
## Bundling *data* and *assumptions* (paper-style “fix TP,FP,FN”)

In the paper, we *fix* three numbers `TP, FP, FN` (true positives / false positives / false negatives)
throughout the argument, and then study the behavior as `TN → +∞`.

In Lean, if we write every lemma as

```
∀ TP FP FN, (0 < TP+FP) → (0 < TP+FN) → (0 ≤ TP) → (0 ≤ FP) → (0 ≤ FN) → ...
```

the statements become long and the proof stops looking like the prose.

So we **bundle** the fixed parameters *and* their standing assumptions into one structure.
This is the closest Lean analogue to the paper’s “Assume TP,FP,FN satisfy …, then …”.
-/


/-- Fixed parameters for the MCC→FM limit proof, together with the standing assumptions.


Field names are chosen so that later proofs read like prose: `c.TP`, `c.FP`, `c.FN`, etc. -/
structure MCCCtx where
  TP : ℝ
  FP : ℝ
  FN : ℝ
  TPFP_pos : 0 < TP + FP
  TPFN_pos : 0 < TP + FN
  TP_nonneg : 0 ≤ TP
  FP_nonneg : 0 ≤ FP
  FN_nonneg : 0 ≤ FN

/-- The common product appearing in the limit: `A = (TP+FP)(TP+FN)`.

We keep it as a definition so `simp [A]` can unfold it when needed. -/
def A (c : MCCCtx) : ℝ := (c.TP + c.FP) * (c.TP + c.FN)

/-- The “post step 3” expression (the body of Eq. (lee_step3) in the paper), as a function of `TN`.

This is what we actually take the limit of; we only transfer the limit back to `MCC` afterwards
using *eventual equality* (`=ᶠ[atTop]`). -/
def post_step3 (c : MCCCtx) (TN : ℝ) : ℝ :=
  (c.TP - c.FP * c.FN / TN) / √ (A c * (1 + c.FP / TN) * (1 + c.FN / TN))

/-!
## Generic limit facts used in the “post-step-3” limit

These are reusable “calculus facts” (really: filter limits) that keep the main proof short.
Each lemma is a direct Lean encoding of a single analytic sentence.
-/

/-- `c / x → 0` as `x → +∞`. -/
lemma tendsto_const_div_atTop_nhds_0 (c : ℝ) :
    Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Filter.tendsto_id

/-- `1 + c/x → 1` as `x → +∞`. -/
lemma tendsto_one_add_const_div_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => (1 : ℝ) + c / x) atTop (𝓝 1) := by
  simpa using (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_0 c))

/-- `a - c/x → a` as `x → +∞`. -/
lemma tendsto_const_sub_const_div_atTop (a c : ℝ) :
    Tendsto (fun x : ℝ => a - c / x) atTop (𝓝 a) := by
  simpa using (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_0 c))

/-- `A * (1 + c/x) * (1 + d/x) → A` as `x → +∞`. -/
lemma tendsto_const_mul_one_add_mul_one_add_div_atTop (A c d : ℝ) :
    Tendsto (fun x : ℝ => A * (1 + c / x) * (1 + d / x)) atTop (𝓝 A) := by
  have h := (tendsto_one_add_const_div_atTop c).mul (tendsto_one_add_const_div_atTop d)
  simpa [mul_assoc] using (tendsto_const_nhds.mul h)

/-- If `a > 0` then `sqrt(a) ≠ 0`.

Lean needs this explicitly to use the quotient limit theorem (`Tendsto.div`). -/
lemma sqrt_of_pos_ne_zero {a : ℝ} (ha : 0 < a) : √ a ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr ha)

/-- `sqrt(x)/t = sqrt(x / t^2)` for `0 ≤ x` and `0 ≤ t`.

This is the formal version of “push a division by `TN` under the square root”. -/
lemma sqrt_div_eq_sqrt_div_sq {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    √ x / t = √ (x / (t ^ 2)) := by
  aesop

/-!
## Algebraic steps (mirrors Eq. (lee_step1/2/3) in the paper)

These lemmas are stated for raw variables `(TP, TN, FP, FN)` so they can be reused
even if we later change how we package parameters.

In the main argument we will *apply* them with `TP := c.TP`, `FP := c.FP`, `FN := c.FN`.
-/

/-- Eq. (lee_step1): divide numerator and denominator by `TN`.

**Lean-forced detail:** we must assume `TN ≠ 0` to justify `field_simp`. -/
lemma mcc_lee_step1 (TP TN FP FN : ℝ) (hTN : TN ≠ 0) :
    MCC TP TN FP FN
      =
    ((TP * TN - FP * FN) / TN) /
      (√ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN) := by
  simp [MCC]
  field_simp [hTN]

/-- Eq. (lee_step2), numerator: `(TP*TN - FP*FN)/TN = TP - FP*FN/TN`.

Again, `TN ≠ 0` is required for denominator clearing. -/
lemma mcc_lee_step2 (TP TN FP FN : ℝ) (hTN : TN ≠ 0) :
    (TP * TN - FP * FN) / TN = TP - FP * FN / TN := by
  field_simp [hTN]

/-- Eq. (lee_step3), denominator rewrite.

This is the paper’s step where
`(TN+FP)/TN = 1 + FP/TN` and `(TN+FN)/TN = 1 + FN/TN`, and `/TN` is pushed under `sqrt`.

**Lean-forced details:**
- to move a division under `sqrt` we must prove nonnegativity of the radicand,
- and we must assume `TN > 0` (so `TN ≠ 0` and `0 ≤ TN`). -/
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
  let A : ℝ := (TP + FP) * (TP + FN)
  let D : ℝ := (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)
  have hD_ge0 : 0 ≤ D := by
    -- each factor is nonnegative; `positivity` is a small tactic that discharges such goals
    simp [D]; positivity
  have h_inside :
      D / (TN ^ 2) = A * (1 + FP / TN) * (1 + FN / TN) := by
    -- This is the exact algebra behind “(TN+FP)/TN = 1 + FP/TN”.
    simp [A, D]
    field_simp [hTNpos.ne']
  calc
    √ ((TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)) / TN
        = √ D / TN := by simp [D]
    _   = √ (D / (TN ^ 2)) := by
            simpa [D] using (sqrt_div_eq_sqrt_div_sq (x := D) (t := TN) hD_ge0 hTNpos.le)
    _   = √ (A * (1 + FP / TN) * (1 + FN / TN)) := by simpa [h_inside]
    _   = √ (((TP + FP) * (TP + FN)) * (1 + FP / TN) * (1 + FN / TN)) := by simp [A]

/-- Combine Eq. (lee_step1/2/3): for `TN > 0`, the original `MCC` equals `post_step3`.

This lemma is the *exact* calc-chain companion to the prose proof.
All subsequent limit work happens only on `post_step3`. -/
lemma mcc_eq_post_step3 (c : MCCCtx) (TN : ℝ) (hTNpos : 0 < TN) :
    MCC c.TP TN c.FP c.FN = post_step3 c TN := by
  -- the calc chain below matches the paper’s Eq. (lee_step1/2/3)
  have h1 := mcc_lee_step1 c.TP TN c.FP c.FN hTNpos.ne'
  have h2 := mcc_lee_step2 c.TP TN c.FP c.FN hTNpos.ne'
  have h3 := mcc_lee_step3 c.TP TN c.FP c.FN c.TPFP_pos c.TPFN_pos c.FP_nonneg c.FN_nonneg hTNpos
  calc
    MCC c.TP TN c.FP c.FN
        = ((c.TP * TN - c.FP * c.FN) / TN) /
            (√ ((c.TP + c.FP) * (c.TP + c.FN) * (TN + c.FP) * (TN + c.FN)) / TN) := h1
    _   = (c.TP - c.FP * c.FN / TN) /
            (√ ((c.TP + c.FP) * (c.TP + c.FN) * (TN + c.FP) * (TN + c.FN)) / TN) := by
            simpa [h2]
    _   = (c.TP - c.FP * c.FN / TN) / √ (A c * (1 + c.FP / TN) * (1 + c.FN / TN)) := by
            simpa [A, h3]
    _   = post_step3 c TN := by simp [post_step3]

/-!
## “Do algebra first, then limits” (the paper’s structure)

A key stylistic choice: we avoid touching limits until the algebraic rewriting is complete.
In Lean, the clean way to do this is via **eventual equality** (`=ᶠ[atTop]`).

`f =ᶠ[atTop] g` means “for all sufficiently large inputs, `f x = g x`”.
Then `Tendsto` facts can be transferred using `Tendsto.congr'`.
-/

section
  variable (c : MCCCtx)

  /-- For all sufficiently large `TN` (indeed: for all `TN > 0`),
  `MCC(TN) = post_step3(TN)`.

  This is the formal version of the paper’s “for large TN we may divide by TN”. -/
  lemma eventuallyEq_MCC_post_step3 :
      (fun TN : ℝ => MCC c.TP TN c.FP c.FN) =ᶠ[atTop] (fun TN => post_step3 c TN) := by
    -- `filter_upwards` lets us prove an “eventually” statement by working with an
    -- arbitrary large `TN` together with the side-condition we requested.
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with TN hTNpos
    simpa using (mcc_eq_post_step3 c TN hTNpos)

  /-- The limit of the post-step-3 expression. This is the only place we do real “limit algebra”. -/
  lemma tendsto_post_step3_atTop :
      Tendsto (fun TN : ℝ => post_step3 c TN) atTop (𝓝 (c.TP / √ (A c))) := by
    -- Numerator: `TP - (FP*FN)/TN → TP`.
    have h_num :
        Tendsto (fun TN : ℝ => c.TP - c.FP * c.FN / TN) atTop (𝓝 c.TP) :=
      tendsto_const_sub_const_div_atTop c.TP (c.FP * c.FN)

    -- Denominator inside `sqrt`: `A * (1 + FP/TN) * (1 + FN/TN) → A`.
    have h_den_inside :
        Tendsto (fun TN : ℝ => A c * (1 + c.FP / TN) * (1 + c.FN / TN)) atTop (𝓝 (A c)) := by
      simpa using (tendsto_const_mul_one_add_mul_one_add_div_atTop (A c) c.FP c.FN)

    -- `sqrt` is continuous, so we can map the limit through `sqrt`.
    have h_den :
        Tendsto (fun TN : ℝ => √ (A c * (1 + c.FP / TN) * (1 + c.FN / TN))) atTop (𝓝 (√ (A c))) :=
      (Filter.Tendsto.sqrt h_den_inside)

    -- **Lean-forced detail:** the quotient limit rule needs the limiting denominator `≠ 0`.
    have h_den_ne : √ (A c) ≠ 0 := by
      have hApos : 0 < A c := by
        -- `A > 0` because both factors are positive.
        simpa [A] using (mul_pos c.TPFP_pos c.TPFN_pos)
      exact sqrt_of_pos_ne_zero hApos

    -- Put numerator/denominator together using `Tendsto.div`.
    simpa [post_step3] using (Filter.Tendsto.div h_num h_den h_den_ne)

  /-- Transfer the post-step-3 limit back to the original `MCC` by eventual equality. -/
  lemma tendsto_MCC_atTop_eq_TP_div_sqrtA :
      Tendsto (fun TN : ℝ => MCC c.TP TN c.FP c.FN) atTop (𝓝 (c.TP / √ (A c))) := by
    have h_eq := eventuallyEq_MCC_post_step3 c
    have h_post := tendsto_post_step3_atTop c
    -- `Tendsto.congr'` rewrites the limiting function using “eventually equal”.
    exact h_post.congr' (Filter.EventuallyEq.symm h_eq)

end

/-!
## FM rearrangement (pulled out as a lemma)

The paper does this algebra in one line. Lean forces us to be explicit about:
- denominators not being zero, and
- using `0 ≤ TP` so that `√(TP^2) = TP`.
-/

/-- Closed form: `FM = TP / √((TP+FP)*(TP+FN))`. -/
lemma FM_eq_TP_div_sqrtA (c : MCCCtx) :
    FM c.TP c.FP c.FN = c.TP / √ (A c) := by
  -- `simp` will reduce the goal to algebraic rewriting once we provide the needed side-conditions.
  have hA_ne : A c ≠ 0 :=
    ne_of_gt (by
      -- `A > 0` because both factors are positive
      simpa [A] using mul_pos c.TPFP_pos c.TPFN_pos)

  -- A small algebra lemma that `field_simp` likes to have around.
  have hmul :
      c.TP / (c.TP + c.FP) * (c.TP / (c.TP + c.FN)) = (c.TP ^ 2) / (A c) := by
    field_simp [c.TPFP_pos.ne', c.TPFN_pos.ne', hA_ne]
    ring

  -- Now unfold FM/PPV/TPR and let `simp_all` use *all* local hypotheses.
  -- **Lean-forced detail:** `c.TP_nonneg` is what lets Lean rewrite `√(TP^2)` as `TP`.
  have hFM : FM c.TP c.FP c.FN = c.TP / √ (A c) := by
    simp_all [FM, PPV, TPR, A]

  simpa using hFM

/-!
## Main theorem (small): assemble the pieces
-/

theorem tendsto_MCC_atTop_eq_FM (c : MCCCtx) :
    Tendsto (fun TN : ℝ => MCC c.TP TN c.FP c.FN) atTop (𝓝 (FM c.TP c.FP c.FN)) := by
  have h_mcc := tendsto_MCC_atTop_eq_TP_div_sqrtA c
  have h_FM := FM_eq_TP_div_sqrtA c
  simpa [h_FM] using h_mcc
