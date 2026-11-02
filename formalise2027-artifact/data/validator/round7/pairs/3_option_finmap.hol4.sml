(* from src/list/src/listScript.sml:5469-5473 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition OPT_MMAP_def[simp]:
  (OPT_MMAP f [] = SOME []) /\
  (OPT_MMAP f (h0::t0) =
     OPTION_BIND (f h0) (\h. OPTION_BIND (OPT_MMAP f t0) (\t. SOME (h::t))))
End

(* from src/coretypes/optionScript.sml:164-168 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 0b0ac193e454a35e3320a7b8095ebd7b88db257ea9b07f4ed2d1afbf47797752 *)
Theorem IS_SOME_DEF[compute,simp,allow_rebind] = new_recursive_definition
  {name="IS_SOME_DEF",
   rec_axiom=option_Axiom,
   def = “(IS_SOME (SOME x) = T) /\ (IS_SOME NONE = F)”};
val _ = ot0 "IS_SOME" "isSome"

(* from src/coretypes/optionScript.sml:170-174 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 0b0ac193e454a35e3320a7b8095ebd7b88db257ea9b07f4ed2d1afbf47797752 *)
Theorem IS_NONE_DEF[compute,simp,allow_rebind] = new_recursive_definition {
  name = "IS_NONE_DEF",
  rec_axiom = option_Axiom,
  def = Term`(IS_NONE (SOME x) = F) /\ (IS_NONE NONE = T)`};
val _ = ot0 "IS_NONE" "isNone"

(* from src/coretypes/optionScript.sml:176-180 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 0b0ac193e454a35e3320a7b8095ebd7b88db257ea9b07f4ed2d1afbf47797752 *)
Theorem THE_DEF[compute,simp,allow_rebind] = new_recursive_definition
  {name="THE_DEF",
   rec_axiom=option_Axiom,
   def = Term `THE (SOME x) = x`};
val _ = ot0 "THE" "the"

(* from src/finite_maps/finite_mapScript.sml:90-90 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
val fmap_TY_DEF = new_type_definition("fmap", EXISTENCE_THM);

(* from src/finite_maps/finite_mapScript.sml:176-178 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FEMPTY_DEF[nocompute]:
 (FEMPTY:'a |-> 'b) = fmap_ABS (\a. INR one)
End

(* from src/finite_maps/finite_mapScript.sml:1079-1081 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FLOOKUP_DEF[nocompute]:
 FLOOKUP ^fmap x = if x IN FDOM f then SOME (FAPPLY f x) else NONE
End

(* from src/finite_maps/finite_mapScript.sml:169-172 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FUPDATE_DEF[nocompute]:
 FUPDATE (f:'a |-> 'b) (x,y)
    = fmap_ABS (\a. if a=x then INL y else fmap_REP f a)
End

(* from src/finite_maps/finite_mapScript.sml:187-189 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FDOM_DEF[nocompute]:
 FDOM (f:'a |-> 'b) x = ISL (fmap_REP f x)
End

(* from src/finite_maps/finite_mapScript.sml:1447-1449 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FRANGE_DEF[nocompute]:
 FRANGE ^fmap = { y | ?x. x IN FDOM f /\ (FAPPLY f x = y)}
End

(* from src/finite_maps/finite_mapScript.sml:1310-1312 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FEVERY_DEF[nocompute]:
 FEVERY P ^fmap = !x. x IN FDOM f ==> P (x, FAPPLY f x)
End

(* from src/finite_maps/finite_mapScript.sml:1876-1878 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition FUPDATE_LIST:
  FUPDATE_LIST = FOLDL FUPDATE
End

(* from src/finite_maps/finite_mapScript.sml:1380-1384 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Theorem o_f_lemma[local]:
  !f:'b->'c.
  !g:'a|->'b.
    ?comp. (FDOM comp = FDOM g)
      /\   (!x. x IN FDOM comp ==> (FAPPLY comp x = f (FAPPLY g x)))

(* from src/finite_maps/finite_mapScript.sml:1393-1395 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
val o_f_DEF = new_specification
  ("o_f_DEF", ["o_f"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) o_f_lemma);

(* from src/finite_maps/alistScript.sml:21-24 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 0c043051862508cee23adf396b0cabb523d10c177f3d47a1a98dd88bae4e2a87 *)
Definition alist_to_fmap_def:
  alist_to_fmap s = FOLDR (\(k,v) f.f|+(k,v)) FEMPTY s
End


(* from src/finite_maps/finite_mapScript.sml:635-638 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Definition SUBMAP_DEF[nocompute]:
  $SUBMAP ^fmap g =
  !x. x IN FDOM f ==> x IN FDOM g /\ (FAPPLY f x = FAPPLY g x)
End

(* from src/finite_maps/finite_mapScript.sml:849-853 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
Theorem union_lemma[local]:
  !^fmap g.
     ?union.
       (FDOM union = FDOM f UNION FDOM g) /\
       (!x. FAPPLY union x = if x IN FDOM f then FAPPLY f x else FAPPLY g x)

(* from src/finite_maps/finite_mapScript.sml:865-867 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 6c33ff7b0e3fbb5fa0f354012632c6c3bcf1596fc465dd0f9fc79f7b9a667eee *)
val FUNION_DEF = new_specification
  ("FUNION_DEF", ["FUNION"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) union_lemma);

