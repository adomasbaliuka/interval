Conservative interval arithmetic in Lean
========================================

We implement conservative interval arithmetic in Lean, on top of a software implementation of
floating point (since Lean's `Float` is untrusted). The key types are

1. `Floating`: 64+64 bit software floating point, with 64 bits of mantissa (roughly, as the high
   bit is explicit) and 64 bits of exponent. All arithmetic is conservatively rounded up or down.
2. `Interval`: Lower and upper `Floating` bounds representing a conservative interval.
3. `Box`: Real and imaginary `Interval`s approximating a complex number.
3. `Approx A R`: Typeclass that says that `A` is a conservative approximation of `R`.  The key
   examples are `Approx Interval ℝ` and `Approx Box ℂ`. There are a variety of associated
   typeclasses showing that particular arithmetic operations are conservative (respect the
   approximation), such as `ApproxAdd` and `ApproxField`.

On top of `Interval`, we implement conservative versions of field arithmetic and various special
functions (`exp`, `log`, powers).

## Building

1. Install [`elan`](https://github.com/leanprover/elan) (`brew install elan-init` on Mac)
2. `lake build`

## Optimization and debugging tricks

I'm going to keep a list here, since otherwise I will forget them.

```
-- Tracing options
set_option trace.aesop true in

-- Print compiler IR, such as to see how well inlining worked:
set_option trace.compiler.ir.result true in
def ...
```
