
import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic


noncomputable section

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
  (TP * TN - FP * FN) / (Real.sqrt ( (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN)))

def MCC_top (TP TN FP FN : ℝ) : ℝ := (TP * TN - FP * FN) / TN
def MCC_bot (TP TN FP FN : ℝ) : ℝ := (TP + FP) * (TP + FN) * ((TN + FP) / TN) * ((TN + FN) / TN)

end

theorem mcc_eq (TP TN FP FN : ℝ) (h : TN > 0) (h1 : 0 <= MCC_bot TP TN FP FN) :
   MCC TP TN FP FN = MCC_top TP TN FP FN / (Real.sqrt (MCC_bot TP TN FP FN)) := by
  have hgeq : 0 ≤ TN := by positivity
  have htop : (TP * TN - FP * FN) = (MCC_top TP TN FP FN) * TN := by
    unfold MCC_top; rw [<- mul_div_mul_right _ _ (by positivity)]; field_simp
  have hbot : (Real.sqrt ( (TP + FP) * (TP + FN) * (TN + FP) * (TN + FN))) = (Real.sqrt (MCC_bot TP TN FP FN)) * TN := by
    nth_rewrite 4 [<- Real.sqrt_sq hgeq]; rw [<- Real.sqrt_mul]; unfold MCC_bot; field_simp; assumption
  unfold MCC; rw [htop, hbot]; field_simp

open Filter Topology


theorem t1 (c : ℝ) : Tendsto (fun x: ℝ => c * x / x) atTop (𝓝 c) := by
  apply tendsto_atTop_of_eventually_const (i₀ := 1)
  exact fun i hi => by field_simp

theorem t2 (c : ℝ) : Tendsto (fun x: ℝ => c / x) atTop (𝓝 0) := by
  have h2 : Filter.Tendsto (fun x : ℝ => c • x⁻¹) Filter.atTop (𝓝 0 ) :=  by
    rw [<- smul_zero c]; exact Tendsto.const_smul tendsto_inv_atTop_zero c
  simp [div_eq_mul_inv]; simpa [smul_eq_mul]

/--
This proof is from TongKe Xue on the Lean Zulip chat:

https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Can.20this.20GPT.205.2E1.20be.20simplified.3F/with/561031593
-/
theorem tendsto_MCC_atTop_eq_FM
    {TP FP FN : ℝ}
    (hTPFPpos : 0 < TP + FP)
    (hTPFNpos : 0 < TP + FN)
    (hTP_nonneg : 0 ≤ TP)
    (hFP_nonneg : 0 ≤ FP)
    (hFN_nonneg : 0 ≤ FN) :
    Tendsto (fun TN : ℝ => MCC TP TN FP FN) atTop (𝓝 (FM TP FP FN)) := by

  have h0 (c : ℝ) : Tendsto (fun x: ℝ => (x + c) / x) atTop (𝓝 1) := by
    rw [ <- add_zero 1]; simp only [add_div]; apply Tendsto.add _ (t2 c);
    apply Tendsto.congr (f₁ := fun x => (1*x) / x); intro x; simp; apply t1

  have h1 : Tendsto (fun TN : ℝ => MCC_top TP TN FP FN) Filter.atTop (𝓝 TP) := by
    nth_rewrite 2 [<- sub_zero TP]; unfold MCC_top; simp only [sub_div] ; apply Tendsto.sub (t1 _) (t2 _)

  have h2 : Tendsto (fun TN : ℝ => MCC_bot TP TN FP FN) Filter.atTop (𝓝 ((TP + FP) * (TP + FN))) := by
    rw [<- mul_one ((TP + FP) * (TP + FN))]
    rw [<- mul_one ((TP + FP) * (TP + FN))]
    unfold MCC_bot; apply Tendsto.mul (Tendsto.mul (Tendsto.mul tendsto_const_nhds tendsto_const_nhds) (h0 _)) (h0 _)

  have h3: Tendsto (fun TN : ℝ => (MCC_top TP TN FP FN) / (Real.sqrt (MCC_bot TP TN FP FN))) atTop (𝓝 (FM TP FP FN)) := by
    unfold FM; unfold PPV; unfold TPR; field_simp; rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity) ]
    apply Tendsto.div h1 (Tendsto.sqrt h2) (by positivity)

  have h4: ∀ (TN : ℝ), 0 ≤ TN -> 0 ≤ MCC_bot TP TN FP FN := by intro TN hTN; unfold MCC_bot; positivity

  have h5: Tendsto (fun TN : ℝ => MCC TP TN FP FN - ((MCC_top TP TN FP FN) / (Real.sqrt (MCC_bot TP TN FP FN)))) atTop (𝓝 0) := by
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    intro TN hTN; rw [mcc_eq _ _ _ _ (by positivity) (h4 _ (by positivity))]; simp

  have h7 := Tendsto.add h5 h3; simp at h7; exact h7
