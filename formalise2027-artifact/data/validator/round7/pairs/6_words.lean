-- ============================================================
-- Word types (opaque stubs)
-- ============================================================

/- HOL4: word8 -/
abbrev word8 := UInt8

/- HOL4: word64 -/
abbrev word64 := UInt64

/- HOL4: word_add, word_sub, etc. for word8 -/
def word_add_8 (a b : word8) : word8 := a + b
def word_sub_8 (a b : word8) : word8 := a - b
def word_and_8 (a b : word8) : word8 := a &&& b
def word_or_8 (a b : word8) : word8 := a ||| b
def word_xor_8 (a b : word8) : word8 := a ^^^ b
def word_lsl_8 (a : word8) (n : Nat) : word8 := a <<< n.toUInt8
def word_lsr_8 (a : word8) (n : Nat) : word8 := a >>> n.toUInt8
/- Arithmetic right shift: sign-extend. UInt8 has no native ASR; emulate
   by sign-extending the top bit. -/
def word_asr_8 (a : word8) (n : Nat) : word8 :=
  let signMask : word8 := if a &&& 0x80 != 0 then
      ((0xFF : word8) <<< (8 - min 8 n).toUInt8)
    else 0
  (a >>> n.toUInt8) ||| signMask
/- Rotate right. -/
def word_ror_8 (a : word8) (n : Nat) : word8 :=
  let m := n % 8
  (a >>> m.toUInt8) ||| (a <<< (8 - m).toUInt8)

/- HOL4: word_add, word_sub, etc. for word64 -/
def word_add_64 (a b : word64) : word64 := a + b
def word_sub_64 (a b : word64) : word64 := a - b
def word_and_64 (a b : word64) : word64 := a &&& b
def word_or_64 (a b : word64) : word64 := a ||| b
def word_xor_64 (a b : word64) : word64 := a ^^^ b
def word_lsl_64 (a : word64) (n : Nat) : word64 := a <<< n.toUInt64
def word_lsr_64 (a : word64) (n : Nat) : word64 := a >>> n.toUInt64
/- Arithmetic right shift on 64-bit. -/
def word_asr_64 (a : word64) (n : Nat) : word64 :=
  let signMask : word64 :=
    if a &&& 0x8000000000000000 != 0 then
      ((0xFFFFFFFFFFFFFFFF : word64) <<< (64 - min 64 n).toUInt64)
    else 0
  (a >>> n.toUInt64) ||| signMask
/- Rotate right on 64-bit. -/
def word_ror_64 (a : word64) (n : Nat) : word64 :=
  let m := n % 64
  (a >>> m.toUInt64) ||| (a <<< (64 - m).toUInt64)

/- HOL4: w2n -/
def w2n_8 (w : word8) : Nat := w.toNat
def w2n_64 (w : word64) : Nat := w.toNat

/- HOL4: n2w -/
def n2w_8 (n : Nat) : word8 := n.toUInt8
def n2w_64 (n : Nat) : word64 := n.toUInt64

/- HOL4: i2w — convert an integer to a machine word, taking the result
   modulo `2^width`. Negative integers are represented in two's complement. -/
def i2w_8 (i : Int) : word8 := (i % 256 + 256).toNat.toUInt8
def i2w_64 (i : Int) : word64 := (i % (2^64 : Int) + (2^64 : Int)).toNat.toUInt64

