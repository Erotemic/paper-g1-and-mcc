-- This is a WIP as I learn lean in order to codify the proof
import Mathlib
import Lake
open Filter 
open Real


section mcc_section

-- The definition of the MCC
noncomputable def MCC (tp tn fp fn : ℝ) : ℝ := 
    ( tp * tn - fp * fn ) / 
        Real.sqrt (( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) )

noncomputable def MCC_v2 (tp tn fp fn : ℝ) : ℝ := 
    (tp - fp * (fn / tn)) / 
        Real.sqrt (( tp + fp ) * ( tp + fn ) * ( 1 + fp/tn ) * ( 1 + fn/tn ) )

-- Filter.Tendsto (fun k => Finset.sum (Finset.range k) fun i => (-1) ^ i / (2 * ↑i + 1)) Filter.atTop (nhds (Real.pi / 4))

-- The definition of FM
noncomputable def FM (tp fp fn : ℝ) : ℝ := 
    Real.sqrt  (( tp / ( tp + fn ) ) * ( tp / ( tp + fp ) ) )

#check MCC 
#check FM

-- #eval MCC 4 1000000 8 3
-- #eval FM 4 8 3

variable (tp fp fn : ℝ)

noncomputable def MCC_tn := fun (tn : ℝ) => MCC tp tn fp fn
noncomputable def FM_ := FM tp fp fn

variable (x: ℝ)

-- https://github.com/PatrickMassot/GlimpseOfLean/blob/master/GlimpseOfLean/Introduction.lean
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Help.20proving.20lim_.7Bx-.3Einf.7D.201.2Fx.20.3D.200

--theorem inv_x_as_x_increases_tendsto_zero : Filter.Tendsto (fun (x : ℝ) => x⁻¹) atTop (nhds 0) := by
-- refine tendsto_inv_atTop_zero


theorem inv_x_as_x_increases_tendsto_zero : Tendsto (fun x => x⁻¹) atTop (nhds (0:ℝ)) := by {
  exact tendsto_inv_atTop_zero
}

-- theorem inv_x_as_x_increases_tendsto_zero : Tendsto (fun x => 1 / x) atTop (nhds 0) := by refine
--  tendsto_inv_atTop_zero

-- help options
/-
theorem tendsto_MCC_tn_atTop_FM : Tendsto MCC_tn atTop (nhds FM_) := by {
}
-/
-- theorem foobar : MCC_tn = ()


end mcc_section


example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
}

--example : MCC_v2 = MCC := by ring

--set_option pp.implicit true
-- set_option pp.universes true
set_option pp.notation false
--set_option pp.numerals false


example (a b c : ℝ) (h1 : a + b = r1) (h2 : b + a = r2) : r1 = r2 := by {
  -- add_comm
  --rw 
  --show r1 = r2
  -- example (z : ℝ) : (a + b = r1) -> (z + a + b = z + r1) := refl
  -- rw [h1] at h2
}


/-{


example (a b c d : ℝ) (h : c = d*a - b) (h' : b = a*d) : c = 0 := by {
  rw [h'] at h
  ring at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h
}


example (a b c d : ℝ) (h : c = d*a - b) (h' : b = a*d) : c = 0 := by 

  -- intro h1 : b = (y : ℝ) + (x : ℝ)
  -- intro y : ℝ
   
 --  def foo (x y : ℝ) : b = x + y := by {
  --  ring
  -- }

   rw [h'] at h 
   ring at h'

  rw [h'] at h
  ring at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h
}
-/
