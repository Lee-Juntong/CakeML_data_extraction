(* from src/floating-point/machine_ieeeLib.sml:49-67 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 260250183515ce07e00a4a5f944b05cdf89b9d76696c7f24601513db230b362b *)
   fun mk_fp_to_float fp fp_ty float_ty pre_k t t_ty w_ty =
      let
         val fp_to_float = fp ^ "_to_float"
         val fp_to_float_var = Term.mk_var (fp_to_float, fp_ty --> float_ty)
         val w = Term.mk_var ("w", fp_ty)
         val s = i2t pre_k
         val float =
            TypeBase.mk_record (float_ty,
               [("Sign", wordsSyntax.mk_word_extract (s, s, w, ``:1``)),
                ("Exponent", wordsSyntax.mk_word_extract
                                (i2t (pre_k - 1), i2t t, w, w_ty)),
                ("Significand", wordsSyntax.mk_word_extract
                                   (i2t (t - 1), i2t 0, w, t_ty))])
         val def =
            Definition.new_definition (fp_to_float ^ "_def",
               fp_to_float_var & w == float)
      in
         (get_function def, def)
      end

(* from src/floating-point/machine_ieeeLib.sml:68-79 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 260250183515ce07e00a4a5f944b05cdf89b9d76696c7f24601513db230b362b *)
   fun mk_float_to_fp fp fp_ty float_ty t_ty w_ty =
      let
         val float_to_fp = "float_to_" ^ fp
         val float_to_fp_var = Term.mk_var (float_to_fp, float_ty --> fp_ty)
         val x = Term.mk_var ("x", float_ty)
         val def =
            Definition.new_definition (float_to_fp ^ "_def",
              float_to_fp_var & x ==
              mk_float_sign x @@ mk_float_exponent x @@ mk_float_significand x)
      in
         (get_function def, def)
      end

(* from src/floating-point/machine_ieeeLib.sml:147-281 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 260250183515ce07e00a4a5f944b05cdf89b9d76696c7f24601513db230b362b *)
   fun lift1 float_to_fp fp_to_float fp_ty float_ty with_flags has_flags =
      let
         val ty1 =
           if with_flags then fp_ty --> flags_ty ** fp_ty else fp_ty --> fp_ty
         val ty2 = if has_flags then float_ty --> flags_ty ** float_ty
                   else float_ty --> float_ty
         val snd_tm = Term.inst [alpha |-> flags_ty, beta |-> float_ty]
                      pairSyntax.snd_tm
      in
         fn (s, f) =>
            let
               val (v, tm) =
                  (Term.mk_var (s, ty1), Term.mk_const (f, ty2))
                  handle HOL_ERR _ =>
                    (Term.mk_var (s, rounding_ty --> ty1) & mode,
                     Term.mk_const (f, rounding_ty --> ty2) & mode)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v == (if with_flags then
                             mk_I_hashhash float_to_fp o' tm o' fp_to_float
                           else if has_flags then
                             float_to_fp o' snd_tm o' tm o' fp_to_float
                           else float_to_fp o' tm o' fp_to_float))
            in
               def
            end
      end
   fun lift1b fp_to_float fp_ty float_ty =
      let
         val ty1 = fp_ty --> Type.bool
         val ty2 = float_ty --> Type.bool
      in
         fn (s, f) =>
            let
               val (v, tm) = (Term.mk_var (s, ty1), Term.mk_const (f, ty2))
               val def =
                  Definition.new_definition (s ^ "_def",
                     v == tm o' fp_to_float)
            in
               def
            end
      end
   fun lift1c float_to_fp fp_ty float_ty =
      let
         val dim_ty = dest_float_ty float_ty
         val ty = Type.mk_type ("itself", [dim_ty]) --> float_ty
         val a = boolSyntax.mk_itself dim_ty
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, fp_ty)
               val tm = Term.mk_const (f, ty) & a
               val def =
                  Definition.new_definition (s ^ "_def", v == float_to_fp & tm)
            in
               def
            end
      end
   fun lift2 float_to_fp fp_to_float fp_ty float_ty with_flags =
      let
         val ty1 =
           if with_flags then
             rounding_ty --> fp_ty --> fp_ty --> flags_ty ** fp_ty
           else rounding_ty --> fp_ty --> fp_ty --> fp_ty
         val ty2 =
           rounding_ty --> float_ty --> float_ty --> flags_ty ** float_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
         val snd_tm = Term.inst [alpha |-> flags_ty, beta |-> float_ty]
                      pairSyntax.snd_tm
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val x = tm & mode & (fp_to_float & a) & (fp_to_float & b)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & mode & a & b ==
                     (if with_flags then
                        mk_I_hashhash float_to_fp & x
                      else float_to_fp & (snd_tm & x)))
            in
               def
            end
      end
   fun lift2b fp_to_float fp_ty float_ty res_ty =
      let
         val ty1 = fp_ty --> fp_ty --> res_ty
         val ty2 = float_ty --> float_ty --> res_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & a & b ==
                     tm & (fp_to_float & a) & (fp_to_float & b))
            in
               def
            end
      end
   fun lift3 float_to_fp fp_to_float fp_ty float_ty with_flags =
      let
         val ty1 =
           if with_flags then
             rounding_ty --> fp_ty --> fp_ty --> fp_ty --> flags_ty ** fp_ty
           else rounding_ty --> fp_ty --> fp_ty --> fp_ty --> fp_ty
         val ty2 = rounding_ty --> float_ty --> float_ty --> float_ty -->
                   flags_ty ** float_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
         val c = Term.mk_var ("c", fp_ty)
         val snd_tm = Term.inst [alpha |-> flags_ty, beta |-> float_ty]
                      pairSyntax.snd_tm
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val x = tm & mode & (fp_to_float & a) & (fp_to_float & b) &
                                   (fp_to_float & c)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & mode & a & b & c ==
                     (if with_flags then
                        mk_I_hashhash float_to_fp & x
                      else float_to_fp & (snd_tm & x)))
            in
               def
            end
      end

(* from src/floating-point/machine_ieeeLib.sml:419-513 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 260250183515ce07e00a4a5f944b05cdf89b9d76696c7f24601513db230b362b *)
        val lift1 = lift1 float_to_fp fp_to_float fp_ty float_ty
        val lift1b = lift1b fp_to_float fp_ty float_ty
        val lift1c = lift1c float_to_fp fp_ty float_ty
        val lift2 = lift2 float_to_fp fp_to_float fp_ty float_ty
        val lift2c = lift2b fp_to_float fp_ty float_ty float_compare_ty
        val lift2b = lift2b fp_to_float fp_ty float_ty Type.bool
        val lift3 = lift3 float_to_fp fp_to_float fp_ty float_ty
        val fp_roundToIntegral_def =
          lift1 false false (fp ^ "_roundToIntegral", "float_round_to_integral")
        val fp_to_int_def = mk_fp_to_int fp fp_to_float fp_ty float_ty
        val fp_sqrt_def = lift1 false true (fp ^ "_sqrt", "float_sqrt")
        val fp_sqrt_with_flags_def =
          lift1 true true (fp ^ "_sqrt_with_flags", "float_sqrt")
        val fp_negate_def = lift1 false false (fp ^ "_negate", "float_negate")
        val fp_abs_def = lift1 false false (fp ^ "_abs", "float_abs")
        val fp_isnan_def = lift1b (fp ^ "_isNan", "float_is_nan")
        val fp_issignallingnan_def =
          lift1b (fp ^ "_isSignallingNan", "float_is_signalling")
        val fp_isintegral_def =
           lift1b (fp ^ "_isIntegral", "float_is_integral")
        val fp_iszero_def = lift1b (fp ^ "_isZero", "float_is_zero")
        val fp_isnormal_def = lift1b (fp ^ "_isNormal", "float_is_normal")
        val fp_issubnormal_def =
           lift1b (fp ^ "_isSubnormal", "float_is_subnormal")
        val fp_isfinite_def = lift1b (fp ^ "_isFinite", "float_is_finite")
        val fp_isinfinite_def =
           lift1b (fp ^ "_isInfinite", "float_is_infinite")
        val fp_posinf_def = lift1c (fp ^ "_posInf", "float_plus_infinity")
        val fp_neginf_def = lift1c (fp ^ "_negInf", "float_minus_infinity")
        val fp_poszero_def = lift1c (fp ^ "_posZero", "float_plus_zero")
        val fp_negzero_def = lift1c (fp ^ "_negZero", "float_minus_zero")
        val fp_minpos_def = lift1c (fp ^ "_posMin", "float_plus_min")
        val fp_minneg_def = lift1c (fp ^ "_negMin", "float_minus_min")
        val fp_top_def = lift1c (fp ^ "_top", "float_top")
        val fp_bottom_def = lift1c (fp ^ "_bottom", "float_bottom")
        val fp_add_def = lift2 false (fp ^ "_add", "float_add")
        val fp_sub_def = lift2 false (fp ^ "_sub", "float_sub")
        val fp_mul_def = lift2 false (fp ^ "_mul", "float_mul")
        val fp_div_def = lift2 false (fp ^ "_div", "float_div")
        val fp_add_with_flags_def =
          lift2 true (fp ^ "_add_with_flags", "float_add")
        val fp_sub_with_flags_def =
          lift2 true (fp ^ "_sub_with_flags", "float_sub")
        val fp_mul_with_flags_def =
          lift2 true (fp ^ "_mul_with_flags", "float_mul")
        val fp_div_with_flags_def =
          lift2 true (fp ^ "_div_with_flags", "float_div")
        val fp_compare_def = lift2c (fp ^ "_compare", "float_compare")
        val fp_equal_def = lift2b (fp ^ "_equal", "float_equal")
        val fp_lessthan_def = lift2b (fp ^ "_lessThan", "float_less_than")
        val fp_lessequal_def = lift2b (fp ^ "_lessEqual", "float_less_equal")
        val fp_greaterthan_def =
           lift2b (fp ^ "_greaterThan", "float_greater_than")
        val fp_greaterequal_def =
           lift2b (fp ^ "_greaterEqual", "float_greater_equal")
        val fp_mul_add_def = lift3 false (fp ^ "_mul_add", "float_mul_add")
        val fp_mul_sub_def = lift3 false (fp ^ "_mul_sub", "float_mul_sub")
        val fp_mul_add_with_flags_def =
          lift3 true (fp ^ "_mul_add_with_flags", "float_mul_add")
        val fp_mul_sub_with_flags_def =
          lift3 true (fp ^ "_mul_sub_with_flags", "float_mul_sub")
        val (fp_to_float_11, float_to_fp_11,
             float_to_fp_fp_to_float, fp_to_float_float_to_fp,
             fp_nchotomy, float_nchotomy) =
           encoding_thms (fp, fp_to_float_def, float_to_fp_def)
        val monop = monop fp_to_float_float_to_fp
        val binop = binop fp_to_float_float_to_fp
        val triop = triop fp_to_float_float_to_fp
        val fp_to_float_n2w = fp_to_float_n2w (fp, t, w, fp_to_float_def)
     in
        case a of
           SOME name => Parse.type_abbrev (name, float_ty)
         | NONE => ()
      ; [monop fp_sqrt_def] @
        List.map binop
          [fp_add_def, fp_sub_def, fp_mul_def, fp_div_def, fp_compare_def,
           fp_equal_def, fp_lessthan_def, fp_lessequal_def,
           fp_greaterthan_def, fp_greaterequal_def] @
        [fp_to_float_float_to_fp, fp_to_float_n2w, real_to_fp_def,
         real_to_fp_with_flags_def, int_to_fp_def, fp_posinf_def, fp_neginf_def,
         fp_poszero_def, fp_negzero_def, fp_minpos_def, fp_minneg_def,
         fp_top_def, fp_bottom_def, float_to_fp_fp_to_float,
         fp_to_float_float_to_fp] @
        List.map monop
          [fp_to_real_def, fp_to_value_def, fp_to_int_def, fp_abs_def,
           fp_negate_def, fp_isnan_def, fp_issignallingnan_def,
           fp_isintegral_def, fp_iszero_def, fp_isnormal_def,
           fp_issubnormal_def, fp_isfinite_def, fp_isinfinite_def,
           fp_roundToIntegral_def, fp_sqrt_with_flags_def] @
        List.map binop
          [fp_add_with_flags_def, fp_sub_with_flags_def, fp_mul_with_flags_def,
           fp_div_with_flags_def] @
        List.map triop
          [fp_mul_add_def, fp_mul_sub_def, fp_mul_add_with_flags_def,
           fp_mul_sub_with_flags_def]

(* from src/floating-point/binary_ieeeScript.sml:246-251 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 829e79462e94857142b8ef283ccb7fb96328712d1e86cfebfb5bafb6bb05afd5 *)
Datatype:
   rounding = roundTiesToEven
            | roundTowardPositive
            | roundTowardNegative
            | roundTowardZero
End

