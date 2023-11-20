-- This is a WIP as I learn lean in order to codify the proof
import Mathlib
import Lake
import Mathlib.Tactic.Positivity

open Filter 
open Real
open NNReal 


section mcc_section

-- The definition of the MCC
noncomputable def MCC (tp tn fp fn : ℝ≥0) : ℝ := 
    ( tp * tn - fp * fn ) / 
        NNReal.sqrt (( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) )

-- The definition of FM
noncomputable def FM (tp fp fn : ℝ≥0) : ℝ≥0 := 
    NNReal.sqrt  (( tp / ( tp + fn ) ) * ( tp / ( tp + fp ) ) )

--- The overall goal

variable (tp fp fn : ℝ≥0)
noncomputable def MCC_tn := fun (tn : ℝ≥0) => MCC tp tn fp fn
noncomputable def FM_ := FM tp fp fn

/-
--- What needs to be shown:

theorem tendsto_MCC_tn_atTop_FM : Tendsto MCC_tn atTop (nhds FM_) := by {
  sorry
}

-/

/-
Helper Theorems
-/

theorem mul_fractions (a b c d : ℝ) : (a/b) * (c/d) = (a * c) / (b * d) := by {
  ring
}

theorem div_is_mul_inv (a b: ℝ) : a / b = a * b⁻¹ := by {
  ring
}

theorem sqrt_one : Real.sqrt 1 = 1 := by {
  rw [sqrt_eq_one]
}

theorem sqrt_of_square (a c : ℝ≥0) : NNReal.sqrt (a * a * c) = a * NNReal.sqrt (c):= by {
  rw [NNReal.sqrt_mul]
  rw [NNReal.sqrt_mul_self]
}

theorem sqrt_of_frac (a b: ℝ≥0) : NNReal.sqrt (a / b) = (NNReal.sqrt a) / (NNReal.sqrt b) := by {
  rw [NNReal.sqrt_div]
}

-- Going to show that FM_v1 simplifies to FM_v2

noncomputable def FM_v1 (tp fp fn : ℝ≥0) : ℝ≥0 := 
    NNReal.sqrt  (( tp / ( tp + fn ) ) * ( tp / ( tp + fp ) ) )

noncomputable def FM_v2 (tp fp fn : ℝ≥0) : ℝ≥0 := 
    tp / NNReal.sqrt  ( ( tp + fn ) * ( tp + fp ) )


theorem FM_simplify : FM_v1 tp fp fn = FM_v2 tp fp fn := by {
  rw [FM_v1]
  rw [FM_v2]
  rw [div_eq_inv_mul]
  rw [div_eq_inv_mul]
  rw [div_eq_inv_mul]
  have u1 := (tp + fn)⁻¹
  have u2 := (tp + fp)⁻¹
  rw [u1]

  rw [mul_comm (tp + fn)⁻¹ tp]
  rw [mul_comm (tp + fp)⁻¹ tp]
  
  --rw [← mul_assoc (tp + fn)⁻¹ tp (tp + fp)⁻¹]
  --rw [← mul_assoc (tp + fp)⁻¹]

}



/-

An outline of what the above proof should look like:

* Consider the MCC:

MCC

* Expanding the MCC:

( tp * tn - fp * fn ) / Real.sqrt (( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) )

* Multiply by 1 = (tn⁻¹/tn⁻¹), so we also have to assert tn > 0

(tn⁻¹/tn⁻¹) * (( tp * tn - fp * fn ) / Real.sqrt (( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) ))

* Bring tn⁻¹ into numer and denom terms 

(tn⁻¹ * ( tp * tn - fp * fn )) / (tn⁻¹ * Real.sqrt ( ( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) ))

--- Numerator Algebra ---

* Consider the numerator

Let numer = (tn⁻¹ * ( tp * tn - fp * fn )) 

* Distribute tn⁻¹ over the addition

(tn⁻¹ * tp * tn) - (tn⁻¹ * fp * fn)

* Commute multiplication and cancel inverses

numer = (tp) - (tn⁻¹ * fp * fn)

--- Denominator Algebra ---

* Consider the denominator

Let denom = (tn⁻¹ * Real.sqrt ( ( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) ))

* Bring  tn⁻¹ inside the sqrt

Real.sqrt ( tn⁻¹ * tn⁻¹ * ( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) )

* Commute the tn⁻¹'s 

Real.sqrt (* ( tp + fp ) * ( tp + fn ) *  tn⁻¹ * ( tn + fp ) *  tn⁻¹ * ( tn + fn ) )

* Distribute the tn⁻¹'s 

Real.sqrt (* ( tp + fp ) * ( tp + fn ) *  ( tn⁻¹ * tn + tn⁻¹ * fp ) *  (tn⁻¹ * tn + tn⁻¹ * fn ) )

* Cancel multiplicative inverses

denom = Real.sqrt ( ( tp + fp ) * ( tp + fn ) *  (1 + tn⁻¹ * fp ) *  (1 + tn⁻¹ * fn ) )

--- Limit Part ---

* Recall the new numer

numer = (tp) - (tn⁻¹ * fp * fn)

* Consider the new numer as tn tends to infinity

Limit(numer) = (tp) - (0 * fp * fn)

* Cancel the term multiplied by zero

Limit(numer) = (tp) 

* Recall the nuw denom

denom = Real.sqrt ( ( tp + fp ) * ( tp + fn ) *  (1 + tn⁻¹ * fp ) *  (1 + tn⁻¹ * fn ) )

* Consider the new denom as tn tends to infinity

Limit(denom) = Real.sqrt ( ( tp + fp ) * ( tp + fn ) *  (1 + 0 * fp ) *  (1 + 0 * fn ) )

* Cancel the terms multiplied by zero, apply addative identity

Limit(denom) = Real.sqrt ( ( tp + fp ) * ( tp + fn ) *  (1) * (1) )

* Apply multiplicative identity

Limit(denom) = Real.sqrt ( ( tp + fp ) * ( tp + fn ) )

* Apply: Limit(numer/denom) = Limit(numer)/Limit(denom)

Limit(MCC) = tp / Real.sqrt ( ( tp + fp ) * ( tp + fn ) )

--- Rearrange FM Part

* Consider the FM:

FM 

* Not sure what the matlib names for these are:
* Axiom mul_fractions : (a/b) * (c/d) = (a * b) / (c * d)
* Axiom div_is_mul_inv : a / b = a * b⁻¹
* Axiom sqrt_of_square : Real.sqrt(a * a * c) = a * Real.sqrt(c)
* Axiom sqrt_of_frac : Real.sqrt(a / b) = Real.sqrt(a) * Real.sqrt(b)
* Axiom sqrt_one : Real.sqrt(1) = 1

* Expanding the FM:

Real.sqrt  (( tp / ( tp + fn ) ) * ( tp / ( tp + fp ) ) )

* Apply div_is_mul_inv:

Real.sqrt  (( tp * ( tp + fn )⁻¹ ) * ( tp * ( tp + fp )⁻¹ ) )

* Associativity and communitivty to rearange internal terms:

Real.sqrt  ( tp * tp * ( tp + fn )⁻¹ * ( tp + fp )⁻¹ )

* Apply sqrt_of_square to extract tp: 

tp * Real.sqrt ( ( tp + fn )⁻¹ * ( tp + fp )⁻¹ )

* Revert to division

tp * Real.sqrt  ( 1 /( tp + fn ) * 1 / ( tp + fp ) )

* Apply: mul_fractions

tp * Real.sqrt  ( 1 / (( tp + fn ) * ( tp + fp )) )

* Apply sqrt_of_frac

tp * Real.sqrt (1) / Real.sqrt( (( tp + fn ) * ( tp + fp )) )

* Apply sqrt_one and mul identity

FM = tp / Real.sqrt( ( tp + fn ) * ( tp + fp ) )

* Thus We find

Lim(MCC) = FM by exact

-/

--- Breakup The MCC and try to tackle smaller parts of the problem

noncomputable def MCC_v2 (tp tn fp fn : ℝ) : ℝ := 
    (tp - fp * (fn / tn)) / 
        Real.sqrt (( tp + fp ) * ( tp + fn ) * ( 1 + fp/tn ) * ( 1 + fn/tn ) )

noncomputable def MCC_numer_v1 (tp tn fp fn : ℝ) : ℝ := 
    ( tp * tn - fp * fn )
    
noncomputable def MCC_sqrd_denom_v1 (tp tn fp fn : ℝ) : ℝ := 
        ( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn )

noncomputable def MCC_numer_v2 (tp tn fp fn : ℝ) : ℝ := 
     tn * (tp - fp * (fn / tn))
    
noncomputable def MCC_sqrd_denom_v2 (tp tn fp fn : ℝ) : ℝ := 
        tn *  ( 1 + fp/tn ) * ( tp + fp ) * ( tp + fn ) * ( 1 + fn/tn ) 

/-
theorem show_part 
    (tn_is_pos: tn > 0) (fp_is_pos: fp > 0):
    (tn * fp) = tn * ( 1 + fp/tn) := by {
      conv =>
      rhs
      rw [mul_assoc] 

      -- inv_mul_cancel_left
      -- case right =>

    }

theorem mcc_numers_eq 
    (tp tn fp fn : ℝ) (tp_is_pos: tp > 0) 
    (tn_is_pos: tn > 0) (fp_is_pos: fp > 0) (fn_is_pos: fn > 0): 
    (MCC_sqrd_denom_v1 tp tn fp fn) = (MCC_sqrd_denom_v2 tp tn fp fn) := by {
  
  rw [MCC_sqrd_denom_v1]
  rw [MCC_sqrd_denom_v2]
  --rw [← mul_assoc mcc_numers_eq.rhs]
}

-/


-- Filter.Tendsto (fun k => Finset.sum (Finset.range k) fun i => (-1) ^ i / (2 * ↑i + 1)) Filter.atTop (nhds (Real.pi / 4))

#check MCC
#check FM
#print MCC
#print FM

-- #eval MCC 4 1000000 8 3
-- #eval FM 4 8 3

variable (tp fp fn : ℝ)

--noncomputable def MCC_tn := fun (tn : ℝ) => MCC tp tn fp fn
--noncomputable def FM_ := FM tp fp fn

variable (x: ℝ) 
-- https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2022/Part_C/tactics/intro.html
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
  --
  ring
  --
}

--example : MCC_v2 = MCC := by ring

--set_option pp.raw true
--set_option pp.raw.maxDepth 10

-- set_option pp.implicit true
-- set_option pp.explicit true
-- set_option pp.universes true
--set_option pp.notation false
--set_option pp.numerals false

--set_option autoImplicit false


#check Eq.symm

example (a b r1 r2: ℝ) (h1 : a + b = r1) (h2 : b + a = r2) : r1 = r2 := by {

  have h3 := Eq.symm h1
  have h4 := Eq.symm h2
  rw [h3]
  rw [h4]
  rw [add_comm]
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
