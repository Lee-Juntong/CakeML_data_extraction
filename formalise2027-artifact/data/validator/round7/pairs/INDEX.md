# Prelude to HOL4 index

HOL4 commit sha: UNKNOWN (GitHub API access was denied for this session, so no sha could be resolved).
Source ref: develop on raw.githubusercontent.com/HOL-Theorem-Prover/HOL, fetched 2026-10-15T10:29:52Z (ref develop, sha unknown, fetched 2026-10-15T10:29:52Z).

Lean file: HOL4Prelude_de795c9f6.lean (495 lines). Line numbers in the table are Lean line numbers.

## HOL4 files used (sha256 of fetched bytes)

- `src/bool/boolScript.sml` sha256 `a235171997f339a7629627acfc898d5deafadd28a33a54041f47bc5a862ec1eb`
- `src/coalgebras/llistScript.sml` sha256 `f98d61fdbbb10fd69cea06b92a1c2317e9b32dd313f0079f8e666f1168146955`
- `src/coretypes/optionScript.sml` sha256 `0b0ac193e454a35e3320a7b8095ebd7b88db257ea9b07f4ed2d1afbf47797752`
- `src/finite_maps/alistScript.sml` sha256 `0c043051862508cee23adf396b0cabb523d10c177f3d47a1a98dd88bae4e2a87`
- `src/finite_maps/finite_mapScript.sml` sha256 `6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee`
- `src/finite_maps/sptreeScript.sml` sha256 `97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71`
- `src/floating-point/binary_ieeeScript.sml` sha256 `829e79462e94857142b8ef283ccb7fb96328712d1e86cfebfb5bafb6bb05afd5`
- `src/floating-point/machine_ieeeLib.sml` sha256 `260250183515ce07e00a4a5f944b05cdf89b9d76696c7f24601513db230b362b`
- `src/integer/integer_wordScript.sml` sha256 `a8f9a0c1533d805c75ad2b1a27f11369c3a1e4d4364fd7e3c372e6cb2391757f`
- `src/list/src/listScript.sml` sha256 `737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0`
- `src/list/src/rich_listScript.sml` sha256 `81072413b1535bb76676e96595a8813ab08d5d6c78ef0bb9dd2773e2981986f7`
- `src/n-bit/wordsScript.sml` sha256 `defe07cc3bf441646762207a7a1b43c191519c9f75d338f0f48ff32534afd116`
- `src/pred_set/src/pred_setScript.sml` sha256 `71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c`
- `src/relation/relationScript.sml` sha256 `b56ddc461e512d6adde5ab16ae65bd9b591baccf623af75873a94881d3beca24`
- `src/sort/sortingScript.sml` sha256 `47f7e4cc622495e5d5a58a75e9d28f8f7a5f47c576d086c4d38da053d83effd4`
- `src/string/stringScript.sml` sha256 `c3839af5eda2e4d063374780f66c18c1083dc7c0a881efe2565cef147dd676a7`

## Declarations

| Lean name | Section | Lean line | HOL4 constant | HOL4 file:lines | Note |
|---|---|---|---|---|---|
| Set (type) | 1_sets | 14 | set (type abbreviation) | src/pred_set/src/pred_setScript.sml:81-81 |  |
| Set instance Membership | 1_sets | 18 | IN | src/bool/boolScript.sml:252-253 |  |
| Set.empty | 1_sets | 20 | EMPTY | src/pred_set/src/pred_setScript.sml:316-317 |  |
| Set instance EmptyCollection | 1_sets | 21 | EMPTY | src/pred_set/src/pred_setScript.sml:316-317 |  |
| Set.univ | 1_sets | 23 | UNIV | src/pred_set/src/pred_setScript.sml:348-349 |  |
| Set.insert | 1_sets | 25 | INSERT | src/pred_set/src/pred_setScript.sml:1086-1088 |  |
| Set.union | 1_sets | 27 | UNION | src/pred_set/src/pred_setScript.sml:629-630 |  |
| Set instance Union | 1_sets | 28 | UNION | src/pred_set/src/pred_setScript.sml:629-630 |  |
| Set.inter | 1_sets | 30 | INTER | src/pred_set/src/pred_setScript.sml:724-726 |  |
| Set instance Inter | 1_sets | 31 | INTER | src/pred_set/src/pred_setScript.sml:724-726 |  |
| Set.sdiff | 1_sets | 33 | DIFF | src/pred_set/src/pred_setScript.sml:949-951 |  |
| Set instance SDiff | 1_sets | 34 | DIFF | src/pred_set/src/pred_setScript.sml:949-951 |  |
| Set.image | 1_sets | 36 | IMAGE | src/pred_set/src/pred_setScript.sml:1808-1810 |  |
| Set.sUnion | 1_sets | 38 | BIGUNION | src/pred_set/src/pred_setScript.sml:4761-4763 |  |
| Set.Disjoint | 1_sets | 40 | DISJOINT | src/pred_set/src/pred_setScript.sml:836-837 | HOL4 DISJOINT s t = (s INTER t = EMPTY) |
| Set.subset | 1_sets | 42 | SUBSET | src/pred_set/src/pred_setScript.sml:410-412 |  |
| Set instance HasSubset | 1_sets | 43 | SUBSET | src/pred_set/src/pred_setScript.sml:410-412 |  |
| notation f  s | 1_sets | 48 | IMAGE | src/pred_set/src/pred_setScript.sml:1808-1810 |  |
| notation ⋃₀ ss | 1_sets | 49 | BIGUNION | src/pred_set/src/pred_setScript.sml:4761-4763 |  |
| notation {a} | 1_sets | 50 | INSERT / EMPTY (singleton {a} = a INSERT {}) | src/pred_set/src/pred_setScript.sml:1086-1088; src/pred_set/src/pred_setScript.sml:316-317 |  |
| ALOOKUP | 2_list_ops | 59 | ALOOKUP | src/finite_maps/alistScript.sml:32-35 |  |
| LUPDATE | 2_list_ops | 64 | LUPDATE | src/list/src/listScript.sml:3933-3936 |  |
| EL | 2_list_ops | 68 | EL | src/list/src/listScript.sml:239-242 |  |
| TAKE | 2_list_ops | 72 | TAKE | src/list/src/listScript.sml:2213-2216 |  |
| DROP | 2_list_ops | 76 | DROP | src/list/src/listScript.sml:2218-2221 |  |
| GENLIST | 2_list_ops | 80 | GENLIST | src/list/src/listScript.sml:3260-3263 |  |
| ZIP | 2_list_ops | 84 | ZIP | src/list/src/listScript.sml:1778-1805 | defined with Rsyntax.new_specification (HOL ZIP takes a pair) |
| UNZIP | 2_list_ops | 88 | UNZIP | src/list/src/listScript.sml:1837-1842 |  |
| EVERY | 2_list_ops | 95 | EVERY | src/list/src/listScript.sml:229-232 |  |
| EXISTS_ | 2_list_ops | 99 | EXISTS | src/list/src/listScript.sml:234-237 |  |
| ALL_DISTINCT | 2_list_ops | 103 | ALL_DISTINCT | src/list/src/listScript.sml:2507-2510; src/list/src/listScript.sml:198-198; src/list/src/listScript.sml:190-192 |  |
| LIST_REL | 2_list_ops | 108 | LIST_REL | src/list/src/listScript.sml:1454-1458 | HOL4 LIST_REL comes from the datatype package; only the characterising theorem is in listScript (no Definition block) |
| PERM | 2_list_ops | 114 | PERM | src/sort/sortingScript.sml:17-18 |  |
| REPLICATE | 2_list_ops | 117 | REPLICATE | src/list/src/rich_listScript.sml:57-60 |  |
| FLAT | 2_list_ops | 121 | FLAT | src/list/src/listScript.sml:167-170 |  |
| MAP2 | 2_list_ops | 125 | MAP2 | src/list/src/listScript.sml:266-269 |  |
| FILTER | 2_list_ops | 131 | FILTER | src/list/src/listScript.sml:214-217 |  |
| nub | 2_list_ops | 135 | nub | src/list/src/listScript.sml:4583-4586 |  |
| MEM | 2_list_ops | 140 | MEM | src/list/src/listScript.sml:198-198; src/list/src/listScript.sml:190-192 |  |
| SNOC | 2_list_ops | 144 | SNOC | src/list/src/listScript.sml:3045-3048 |  |
| REVERSE | 2_list_ops | 148 | REVERSE | src/list/src/listScript.sml:2053-2056 |  |
| IS_PREFIX | 2_list_ops | 152 | IS_PREFIX | src/list/src/rich_listScript.sml:307-307; src/list/src/listScript.sml:3010-3014 |  |
| oEL | 2_list_ops | 156 | oEL | src/list/src/listScript.sml:5551-5554 |  |
| OPT_MMAP | 3_option_finmap | 164 | OPT_MMAP | src/list/src/listScript.sml:5469-5473 |  |
| IS_SOME | 3_option_finmap | 172 | IS_SOME | src/coretypes/optionScript.sml:164-168 |  |
| IS_NONE | 3_option_finmap | 177 | IS_NONE | src/coretypes/optionScript.sml:170-174 |  |
| THE | 3_option_finmap | 182 | THE | src/coretypes/optionScript.sml:176-180 | HOL4 THE NONE is unspecified; Lean returns default |
| Finmap (type) | 3_option_finmap | 196 | fmap (type 'a |-> 'b) | src/finite_maps/finite_mapScript.sml:90-90 |  |
| Finmap.FEMPTY | 3_option_finmap | 201 | FEMPTY | src/finite_maps/finite_mapScript.sml:176-178 |  |
| Finmap.FLOOKUP | 3_option_finmap | 204 | FLOOKUP | src/finite_maps/finite_mapScript.sml:1079-1081 |  |
| Finmap.FUPDATE | 3_option_finmap | 208 | FUPDATE | src/finite_maps/finite_mapScript.sml:169-172 |  |
| Finmap.FDOM | 3_option_finmap | 212 | FDOM | src/finite_maps/finite_mapScript.sml:187-189 |  |
| Finmap.FRANGE | 3_option_finmap | 215 | FRANGE | src/finite_maps/finite_mapScript.sml:1447-1449 |  |
| Finmap.FEVERY | 3_option_finmap | 218 | FEVERY | src/finite_maps/finite_mapScript.sml:1310-1312 |  |
| Finmap.FUPDATE_LIST | 3_option_finmap | 222 | FUPDATE_LIST | src/finite_maps/finite_mapScript.sml:1876-1878 |  |
| Finmap.o_f | 3_option_finmap | 226 | o_f | src/finite_maps/finite_mapScript.sml:1380-1384; src/finite_maps/finite_mapScript.sml:1393-1395 |  |
| Finmap.alist_to_fmap | 3_option_finmap | 230 | alist_to_fmap | src/finite_maps/alistScript.sml:21-24 |  |
| Finmap.SUBMAP | 3_option_finmap | 234 | SUBMAP | src/finite_maps/finite_mapScript.sml:635-638 |  |
| Finmap.FUNION | 3_option_finmap | 238 | FUNION | src/finite_maps/finite_mapScript.sml:849-853; src/finite_maps/finite_mapScript.sml:865-867 |  |
| Sptree (type) | 4_sptree_lazylist | 254 | spt (datatype) | src/finite_maps/sptreeScript.sml:30-31 |  |
| Sptree.lookup | 4_sptree_lazylist | 259 | sptree$lookup | src/finite_maps/sptreeScript.sml:46-56 |  |
| Sptree.insert | 4_sptree_lazylist | 263 | sptree$insert | src/finite_maps/sptreeScript.sml:67-85 |  |
| Sptree.delete | 4_sptree_lazylist | 267 | sptree$delete | src/finite_maps/sptreeScript.sml:99-114 |  |
| Sptree.fromAList | 4_sptree_lazylist | 271 | fromAList | src/finite_maps/sptreeScript.sml:1478-1481 |  |
| Sptree.domain | 4_sptree_lazylist | 274 | sptree$domain | src/finite_maps/sptreeScript.sml:473-482 |  |
| Sptree.toList | 4_sptree_lazylist | 277 | sptree$toList | src/finite_maps/sptreeScript.sml:1106-1111; src/finite_maps/sptreeScript.sml:1132-1133 | HOL4 toList returns values via toListA (key order) |
| Sptree.toAList | 4_sptree_lazylist | 280 | toAList | src/finite_maps/sptreeScript.sml:737-748; src/finite_maps/sptreeScript.sml:898-900 |  |
| LazyList (type) | 4_sptree_lazylist | 294 | llist (type) | src/coalgebras/llistScript.sml:64-64 |  |
| LazyList.LPREFIX | 4_sptree_lazylist | 302 | LPREFIX | src/coalgebras/llistScript.sml:2655-2663 |  |
| LazyList.fromList | 4_sptree_lazylist | 306 | llist$fromList | src/coalgebras/llistScript.sml:1154-1156 |  |
| LazyList.toList | 4_sptree_lazylist | 311 | llist$toList | src/coalgebras/llistScript.sml:1140-1142 |  |
| DISJOINT | 5_set_ops | 325 | DISJOINT | src/pred_set/src/pred_setScript.sml:836-837 |  |
| IMAGE | 5_set_ops | 329 | IMAGE | src/pred_set/src/pred_setScript.sml:1808-1810 |  |
| BIGUNION | 5_set_ops | 333 | BIGUNION | src/pred_set/src/pred_setScript.sml:4761-4763 |  |
| FINITE | 5_set_ops | 337 | FINITE | src/pred_set/src/pred_setScript.sml:2909-2913 |  |
| CARD | 5_set_ops | 344 | CARD | src/pred_set/src/pred_setScript.sml:3428-3428 | CARD introduced by new_specification from CARD_EXISTS |
| BIJ | 5_set_ops | 351 | BIJ | src/pred_set/src/pred_setScript.sml:2018-2023; src/pred_set/src/pred_setScript.sml:2113-2118; src/pred_set/src/pred_setScript.sml:2184-2187 |  |
| TOKENS | 5_set_ops | 358 | TOKENS | src/string/stringScript.sml:277-289 | HOL4 TOKENS is on strings (char lists); also uses SPLITP |
| word8 | 6_words | 366 | word8 (type abbreviation) | NOT FOUND | no word8/word64 definition in wordsScript/wordsLib/wordsSyntax; nearest is generic word type (words:34) |
| word64 | 6_words | 369 | word64 (type abbreviation) | NOT FOUND | same as word8 |
| word_add_8 | 6_words | 372 | word_add | src/n-bit/wordsScript.sml:317-319 |  |
| word_sub_8 | 6_words | 373 | word_sub | src/n-bit/wordsScript.sml:343-345 | HOL4 word_sub uses word_2comp |
| word_and_8 | 6_words | 374 | word_and | src/n-bit/wordsScript.sml:137-140 |  |
| word_or_8 | 6_words | 375 | word_or | src/n-bit/wordsScript.sml:142-145 |  |
| word_xor_8 | 6_words | 376 | word_xor | src/n-bit/wordsScript.sml:147-150 |  |
| word_lsl_8 | 6_words | 377 | word_lsl | src/n-bit/wordsScript.sml:489-492 |  |
| word_lsr_8 | 6_words | 378 | word_lsr | src/n-bit/wordsScript.sml:494-497 |  |
| word_asr_8 | 6_words | 381 | word_asr | src/n-bit/wordsScript.sml:499-505 |  |
| word_ror_8 | 6_words | 387 | word_ror | src/n-bit/wordsScript.sml:507-510 |  |
| word_add_64 | 6_words | 392 | word_add | src/n-bit/wordsScript.sml:317-319 |  |
| word_sub_64 | 6_words | 393 | word_sub | src/n-bit/wordsScript.sml:343-345 | HOL4 word_sub uses word_2comp |
| word_and_64 | 6_words | 394 | word_and | src/n-bit/wordsScript.sml:137-140 |  |
| word_or_64 | 6_words | 395 | word_or | src/n-bit/wordsScript.sml:142-145 |  |
| word_xor_64 | 6_words | 396 | word_xor | src/n-bit/wordsScript.sml:147-150 |  |
| word_lsl_64 | 6_words | 397 | word_lsl | src/n-bit/wordsScript.sml:489-492 |  |
| word_lsr_64 | 6_words | 398 | word_lsr | src/n-bit/wordsScript.sml:494-497 |  |
| word_asr_64 | 6_words | 400 | word_asr | src/n-bit/wordsScript.sml:499-505 |  |
| word_ror_64 | 6_words | 407 | word_ror | src/n-bit/wordsScript.sml:507-510 |  |
| w2n_8 | 6_words | 412 | w2n | src/n-bit/wordsScript.sml:50-52 |  |
| w2n_64 | 6_words | 413 | w2n | src/n-bit/wordsScript.sml:50-52 |  |
| n2w_8 | 6_words | 416 | n2w | src/n-bit/wordsScript.sml:54-56 |  |
| n2w_64 | 6_words | 417 | n2w | src/n-bit/wordsScript.sml:54-56 |  |
| i2w_8 | 6_words | 421 | i2w | src/integer/integer_wordScript.sml:29-32 |  |
| i2w_64 | 6_words | 422 | i2w | src/integer/integer_wordScript.sml:29-32 |  |
| fpOfBits (private) | 7_float | 433 | fp64_to_float | src/floating-point/machine_ieeeLib.sml:49-67 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fpToBits (private) | 7_float | 434 | float_to_fp64 | src/floating-point/machine_ieeeLib.sml:68-79 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_lessThan | 7_float | 436 | fp64_lessThan | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_lessEqual | 7_float | 437 | fp64_lessEqual | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_greaterThan | 7_float | 438 | fp64_greaterThan | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_greaterEqual | 7_float | 439 | fp64_greaterEqual | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_equal | 7_float | 440 | fp64_equal | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_abs | 7_float | 441 | fp64_abs | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_negate | 7_float | 442 | fp64_negate | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_sqrt | 7_float | 443 | fp64_sqrt | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_add | 7_float | 444 | fp64_add | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_sub | 7_float | 445 | fp64_sub | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_mul | 7_float | 446 | fp64_mul | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_div | 7_float | 447 | fp64_div | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| fp64_mul_add | 7_float | 451 | fp64_mul_add | src/floating-point/machine_ieeeLib.sml:147-281; src/floating-point/machine_ieeeLib.sml:419-513 | fp64 ops generated by ML (machine_ieeeLib.mk_fp_encoding), not a literal Definition block; shown is the generator source |
| roundTiesToEven | 7_float | 453 | roundTiesToEven (constructor of rounding) | src/floating-point/binary_ieeeScript.sml:246-251 |  |
| ordering (inductive) | 8_misc | 460 | ordering (LESS, EQUAL, GREATER) | NOT FOUND | datatype definition not in fetched files; only used at totoScript.sml:43 (TypeBase.distinct_of ``:ordering``) |
| ORD | 8_misc | 471 | ORD | src/string/stringScript.sml:24-30 | ORD/CHR defined via define_new_type_bijections on char |
| CHR | 8_misc | 474 | CHR | src/string/stringScript.sml:24-30 |  |
| FOLDR | 8_misc | 481 | FOLDR | src/list/src/listScript.sml:219-222 |  |
| FOLDL | 8_misc | 485 | FOLDL | src/list/src/listScript.sml:224-227 |  |
| RTC (inductive) | 8_misc | 489 | RTC | src/relation/relationScript.sml:94-98 |  |
