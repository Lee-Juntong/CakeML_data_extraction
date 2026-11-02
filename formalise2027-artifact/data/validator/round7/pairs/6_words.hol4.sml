(* from src/n-bit/wordsScript.sml:317-319 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_add_def[nocompute]:
  word_add (v:'a word) (w:'a word) = (n2w:num->'a word) (w2n v + w2n w)
End

(* from src/n-bit/wordsScript.sml:343-345 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_sub_def:
  word_sub (v:'a word) (w:'a word) = word_add v (word_2comp w)
End

(* from src/n-bit/wordsScript.sml:137-140 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_and_def[nocompute]:
  word_and (v:'a word) (w:'a word) =
    (FCP i. (v ' i) /\ (w ' i)):'a word
End

(* from src/n-bit/wordsScript.sml:142-145 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_or_def[nocompute]:
  word_or (v:'a word) (w:'a word) =
    (FCP i. (v ' i) \/ (w ' i)):'a word
End

(* from src/n-bit/wordsScript.sml:147-150 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_xor_def[nocompute]:
  word_xor (v:'a word) (w:'a word) =
    (FCP i. ~((v ' i) = (w ' i))):'a word
End

(* from src/n-bit/wordsScript.sml:489-492 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_lsl_def[nocompute]:
  word_lsl (w:'a word) n =
    (FCP i. i < ^WL /\ n <= i /\ w ' (i - n)):'a word
End

(* from src/n-bit/wordsScript.sml:494-497 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_lsr_def[nocompute]:
  word_lsr (w:'a word) n =
    (FCP i. i + n < ^WL /\ w ' (i + n)):'a word
End

(* from src/n-bit/wordsScript.sml:499-505 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_asr_def[nocompute]:
  word_asr (w:'a word) n =
    (FCP i. if ^WL <= i + n then
              word_msb w
            else
              w ' (i + n)):'a word
End

(* from src/n-bit/wordsScript.sml:507-510 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition word_ror_def[nocompute]:
  word_ror (w:'a word) n =
    (FCP i. w ' ((i + n) MOD ^WL)):'a word
End

(* from src/n-bit/wordsScript.sml:50-52 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition w2n_def[nocompute]:
  w2n (w:'a word) = SUM ^WL (\i. SBIT (w ' i) i)
End

(* from src/n-bit/wordsScript.sml:54-56 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116 *)
Definition n2w_def[nocompute]:
  (n2w:num->'a word) n = FCP i. BIT i n
End

(* from src/integer/integer_wordScript.sml:29-32 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 a8f9a0c1533d805c75ad2b1a27f11369c3a1e4d4364fd7e3c372e6cb2391757f *)
Definition i2w_def:
  i2w (i : int) : 'a word =
    if i < 0 then -(n2w (Num(-i))) else n2w (Num i)
End

(* word8: NOT FOUND in fetched HOL4 sources. no word8/word64 definition in wordsScript/wordsLib/wordsSyntax; nearest is generic word type (words:34) *)

(* word64: NOT FOUND in fetched HOL4 sources. same as word8 *)

