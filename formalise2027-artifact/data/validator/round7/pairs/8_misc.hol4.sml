(* from src/string/stringScript.sml:24-30 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 c3839af5eda2e4d063374780f66c18c1083dc7c0a881efe2565cef147dd676a7 *)

val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS);

val CHAR_TYPE_FACTS =
    (define_new_type_bijections
       {ABS="CHR", REP="ORD",name="char_BIJ", tyax=CHAR_TYPE});


(* from src/list/src/listScript.sml:219-222 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition FOLDR:
  FOLDR (f:'a->'b->'b) e [] = e /\
  FOLDR f e (x::l) = f x (FOLDR f e l)
End

(* from src/list/src/listScript.sml:224-227 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition FOLDL:
  FOLDL (f:'b->'a->'b) e [] = e /\
  FOLDL f e (x::l) = FOLDL f (f e x) l
End

(* from src/relation/relationScript.sml:94-98 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 b56ddc461e512d6adde5ab16ae65bd9b591baccf623af75873a94881d3beca24 *)
Inductive RTC:
  (!x. RTC R x x)
    /\
  (!x y z. R x y /\ RTC R y z ==> RTC R x z)
End

(* ordering (inductive): NOT FOUND in fetched HOL4 sources. datatype definition not in fetched files; only used at totoScript.sml:43 (TypeBase.distinct_of ``:ordering``) *)

