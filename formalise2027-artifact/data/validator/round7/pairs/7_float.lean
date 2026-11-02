-- ============================================================
-- IEEE754 floating point (opaque stubs)
-- ============================================================

/- HOL4: fp64 ops — IEEE 754 binary64 operations. The HOL4 development
   models fp64 values as 64-bit words and operates on them through
   IEEE-aware functions. We delegate to Lean's `Float` (which is binary64)
   via `Float.ofBits` / `Float.toBits`. The rounding-mode argument is
   ignored (Lean uses round-to-nearest-even). -/
private def fpOfBits (a : word64) : Float := Float.ofBits a
private def fpToBits (f : Float) : word64 := f.toBits

def fp64_lessThan (a b : word64) : Bool := decide (fpOfBits a < fpOfBits b)
def fp64_lessEqual (a b : word64) : Bool := decide (fpOfBits a ≤ fpOfBits b)
def fp64_greaterThan (a b : word64) : Bool := decide (fpOfBits b < fpOfBits a)
def fp64_greaterEqual (a b : word64) : Bool := decide (fpOfBits b ≤ fpOfBits a)
def fp64_equal (a b : word64) : Bool := fpOfBits a == fpOfBits b
def fp64_abs (a : word64) : word64 := fpToBits (fpOfBits a).abs
def fp64_negate (a : word64) : word64 := fpToBits (-(fpOfBits a))
def fp64_sqrt (_rm : Unit) (a : word64) : word64 := fpToBits (fpOfBits a).sqrt
def fp64_add (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a + fpOfBits b)
def fp64_sub (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a - fpOfBits b)
def fp64_mul (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a * fpOfBits b)
def fp64_div (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a / fpOfBits b)
/- Note: this is not a true fused multiply-add (no FMA primitive in Lean
   core); we compute `a*b + c` with two roundings. This is a translation
   gap relative to HOL4's `fp64_mul_add` which uses a single FMA rounding. -/
def fp64_mul_add (_rm : Unit) (a b c : word64) : word64 :=
  fpToBits (fpOfBits a * fpOfBits b + fpOfBits c)
def roundTiesToEven : Unit := ()

