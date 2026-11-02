/-
Prelude shift / FMA defects, checked on the Direct endpoint (branch proof2-direct).
The word shift definitions in HOL4Prelude.lean are unchanged between de795c9f6 and proof2-direct
(the only prelude changes there are CARD and the LawfulBEq derivation).
Run from r2\direct\lean_type_sound:  lake env lean <this file>

Cause: Lean's UInt8/UInt64 `<<<` and `>>>` take the shift amount modulo the bit width
(and `Nat.toUInt8` wraps mod 256), while HOL4 `word_lsl`/`word_lsr`/`word_asr` shift by the full
amount (shifting a w-bit word by n >= w gives 0, or all sign bits for asr).
-/
import LeanTypeSound
open HOL4

-- 8-bit
example : word_lsl_8 1 8 = 1 := by decide          -- HOL4: 1w << 8 = 0w
example : word_lsr_8 0x80 8 = 0x80 := by decide    -- HOL4: 0x80w >>> 8 = 0w
example : word_asr_8 0x80 0 = 0xFF := by decide    -- HOL4: 0x80w >> 0 = 0x80w (unchanged)
example : word_asr_8 0x01 8 = 0x01 := by decide    -- HOL4: 1w >> 8 = 0w
-- 64-bit
example : word_lsl_64 1 64 = 1 := by decide
example : word_lsr_64 0x8000000000000000 64 = 0x8000000000000000 := by decide
example : word_asr_64 0x8000000000000000 0 = 0xFFFFFFFFFFFFFFFF := by decide
example : word_asr_64 0x01 64 = 0x01 := by decide
-- wrap of the Nat shift amount: 256 becomes 0 for word8
example : word_lsl_8 1 256 = 1 := by decide

-- fp64_mul_add rounds twice (a*b, then +c); IEEE fma rounds once.
-- a = b = 1 + 2^-52, c = -(1 + 2^-51): exact a*b + c = 2^-104, fma gives 2^-104 (0x3970000000000000),
-- the two-rounding version gives 0.
#eval fp64_mul_add () 0x3FF0000000000001 0x3FF0000000000001 0xBFF0000000000002  -- expect 0 (fma: 0x3970000000000000)
