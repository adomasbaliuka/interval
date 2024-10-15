import Interval.Floating.Floor
import Interval.Interval.Basic

/-!
## NatFloor for `Int64`, `Floating`, and `Interval`
-/

open Set
open scoped Real
open scoped UInt64.CommRing

/-- The greatest natural `≤ n` (that is, `max 0 n`) -/
def Int64.natFloor (n : Int64) : ℕ :=
  bif n.isNeg then 0 else n.n.toNat

/-- The greatest natural definitely `≤ x` (or 0 if that fails) -/
def Interval.natFloor (x : Interval) : ℕ :=
  x.lo.floor.n.natFloor

/-- `natFloor` in terms of `n : ℤ` -/
lemma Int64.natFloor_eq (n : Int64) : n.natFloor = ⌊(n : ℤ)⌋₊ := by
  rw [natFloor, bif_eq_if]
  by_cases neg : n.isNeg
  · simp [neg, coe_of_neg neg]
  · simp only [neg, Bool.false_eq_true, ↓reduceIte, Nat.floor_int]
    simp only [Bool.not_eq_true] at neg
    simp only [coe_of_nonneg neg, Int.toNat_ofNat]

@[simp] lemma Interval.natFloor_nan : (nan : Interval).natFloor = 0 := by rfl

@[simp] lemma Int.natFloor_cast (n : ℤ) : ⌊(n : ℝ)⌋₊ = ⌊n⌋₊ := by
  induction' n using  Int.induction_overlap with n n
  · simp
  · simp only [cast_neg, cast_natCast, Nat.floor_int, toNat_neg_nat, Nat.floor_eq_zero]
    refine lt_of_le_of_lt ?_ zero_lt_one
    simp only [Left.neg_nonpos_iff, Nat.cast_nonneg]

lemma Interval.le_natFloor {a : ℝ} {x : Interval} (ax : a ∈ approx x) : x.natFloor ≤ ⌊a⌋₊ := by
  rw [natFloor, Int64.natFloor_eq]
  by_cases fn : x.lo.floor = nan
  · simp [fn]
  have af := Floating.mem_approx_floor x.lo
  simp only [approx, ne_eq, fn, not_false_eq_true, Floating.ne_nan_of_floor, ↓reduceIte, mem_Icc,
    mem_singleton_iff] at ax af
  trans ⌊x.lo.floor.val⌋₊
  · simp [Fixed.val_of_s0]
  · simp only [← af]
    apply Nat.floor_le_floor
    refine le_trans ?_ ax.1
    apply Int.floor_le
