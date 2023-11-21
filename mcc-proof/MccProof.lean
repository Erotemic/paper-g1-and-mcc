-- This is a WIP as I learn lean in order to codify the proof
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Help.20Understanding.20Goal.20Manipulation
import Mathlib
import Lake
import Mathlib.Tactic.Positivity

open Filter 
open Real
open NNReal 


-- The definition of the MCC
noncomputable def MCC (tp tn fp fn : ℝ≥0) := 
    ( tp * tn - fp * fn ) / 
        NNReal.sqrt (( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) )

-- The definition of FM
noncomputable def FM (tp fp fn : ℝ≥0) : ℝ≥0 := 
    NNReal.sqrt  (( tp / ( tp + fn ) ) * ( tp / ( tp + fp ) ) )

--- The overall goal

--variable (tp fp fn : ℝ≥0)
--noncomputable def MCC_tn := fun (tn : ℝ≥0) => MCC tp tn fp fn
--noncomputable def FM_ := FM tp fp fn

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

theorem sqrt_inv_rule (a b: ℝ≥0) : NNReal.sqrt (a⁻¹ * b⁻¹) = (NNReal.sqrt (a * b))⁻¹ := by {
    rw [← NNReal.sqrt_inv]
    rw [mul_inv_rev]
    rw [mul_comm]
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
  generalize h1 : (tp + fn) = u1
  generalize h2 : (tp + fp) = u2
  generalize h3 : u1⁻¹ = u3
  generalize h4 : u2⁻¹ = u4
  rw [mul_comm u3 tp]
  rw [mul_comm u4 tp]   
  rw [mul_assoc tp u3]  
  rw [← mul_assoc u3]   
  rw [mul_comm u3 tp]   
  rw [mul_assoc tp]   
  rw [← mul_assoc tp]   
  rw [sqrt_of_square]
  rw [← h3]
  rw [← h4]
  rw [sqrt_inv_rule]
  rw [mul_comm tp]
}


--- Breakup The MCC and try to tackle smaller parts of the problem

noncomputable def MCC_v2 (tp tn fp fn : ℝ) := 
    (tp - fp * (fn / tn)) / 
        Real.sqrt (( tp + fp ) * ( tp + fn ) * ( 1 + fp/tn ) * ( 1 + fn/tn ) )

noncomputable def MCC_numer_v1 (tp tn fp fn : ℝ) := 
    ( tp * tn - fp * fn )
    
noncomputable def MCC_sqrd_denom_v1 (tp tn fp fn : ℝ) := 
        ( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn )

noncomputable def MCC_numer_v2 (tp tn fp fn : ℝ) := 
     tn * (tp - fp * (fn / tn))
    
noncomputable def MCC_sqrd_denom_v2 (tp tn fp fn : ℝ) := 
        tn * tn *  ( 1 + fp/tn ) * ( tp + fp ) * ( tp + fn ) * ( 1 + fn/tn ) 


-- FIXME: What's the right way to prove these?
-- We need to encode the assumption that a > 0
-- but I dont know how
axiom factor_rule (a b : ℝ≥0):
    a * a * (1 + b/a) = a * (a + b)
    --(a + b) = a * ( 1 + b/a) := by {
--    := by {
--      ring_nf
      --conv =>
      --rhs
      --rw [mul_assoc] 
--    }

axiom factor_rule2 (a b : ℝ):
    a * a * (1 + b/a) = a * (a + b)

axiom factor_rule3 (tn fn u1 u2 u3: ℝ≥0):
    tn * u3 * u1 * u2 * (1 + fn / tn) = u3 * u1 * u2 * (tn + fn)


theorem mcc_numers_eq 
    (tp tn fp fn : ℝ≥0)
    --(tn_is_pos: tn > 0)
    : 
    ( tp + fp ) * ( tp + fn ) * ( tn + fp ) * ( tn + fn ) = 
    tn * tn *  ( 1 + fp/tn ) * ( tp + fp ) * ( tp + fn ) * ( 1 + fn/tn )  := by {
  -- generalize 
  rw [factor_rule tn fp]
  generalize h1 : tp + fp = u1
  generalize h2 : tp + fn = u2
  generalize h3 : tn + fp = u3
  generalize h4 : tn + fn = u4
  rw [factor_rule3]
  rw [← h1]
  rw [← h2]
  rw [← h3]
  rw [← h4]
  ring
  -- rw [MCC_sqrd_denom_v1]
  -- rw [MCC_sqrd_denom_v2] -- why did I get unbound variables?
  --rw [factor_rule tn fn]
  --conv =>
  --rhs
  --rw [mul_comm]
  --rw [mul_comm]
  --rw [← mul_assoc mcc_numers_eq.rhs]
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

* Given mul_fractions : (a/b) * (c/d) = (a * b) / (c * d)
* Given div_is_mul_inv : a / b = a * b⁻¹
* Given sqrt_of_square : Real.sqrt(a * a * c) = a * Real.sqrt(c)
* Given sqrt_of_frac : Real.sqrt(a / b) = Real.sqrt(a) * Real.sqrt(b)
* Given sqrt_one : Real.sqrt(1) = 1

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



--section mcc_section

--end mcc_section


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
