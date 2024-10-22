import Interval.Interval.Exp
import Interval.Interval.Log

/-!
## Interval powers

These are easy on top of `exp` and `log`.
-/

open Set
open scoped Real

/-- `x^y = exp (x.log * y)` -/
@[irreducible] def Interval.pow (x : Interval) (y : Interval) : Interval :=
  (x.log * y).exp

instance : Pow Interval Interval := ⟨Interval.pow⟩

lemma Interval.pow_def {x y : Interval} : x ^ y = (x.log * y).exp := by
  trans x.pow y
  · rfl
  · rw [Interval.pow]


/--
    **TODO delete or use!!!**
Natural powers
* allows negative inputs (not powers)
* more precise for small powers
-/
def Interval.pown (x : Interval) (n : ℕ) : Interval := match n with
  | 0 => 1
  | n + 1 => x * x.pown n

/-- Enable `_ ^ _` notation with natural powers.
could **instead** use the version `Interval.pown`, maybe for part of the range?
Nevertheless, use the "normal" `pow` that takes `Interval` exponenets -/
instance istHPowIntervalNat : HPow Interval ℕ Interval where
  hPow x n := x.pow (.ofNat n)


/-- `Interval.pow` is conservative -/
@[approx] lemma Interval.mem_approx_pow {x : Interval} {y : Interval} {x' y' : ℝ}
    (xm : x' ∈ approx x) (ym : y' ∈ approx y) : x' ^ y' ∈ approx (x ^ y) := by
  rw [pow_def]
  by_cases x0 : 0 < x'
  · rw [Real.rpow_def_of_pos x0]; approx
  · simp only [not_lt] at x0
    rw [Interval.log_nonpos x0 xm, Interval.nan_mul, Interval.exp_nan]
    simp only [approx_nan, mem_univ]

/-- `Interval.pow` is conservative for `ℕ` powers -/
@[approx] lemma Interval.mem_approx_pow_nat {x : Interval} {n : ℕ} {x' : ℝ}
    (xm : x' ∈ approx x) : x' ^ n ∈ approx (x ^ (n : Interval)) := by
  simp only [← Real.rpow_natCast]
  approx
