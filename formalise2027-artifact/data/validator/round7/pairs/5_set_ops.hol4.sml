(* from src/pred_set/src/pred_setScript.sml:836-837 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val DISJOINT_DEF = new_definition ("DISJOINT_DEF",
(“DISJOINT (s:'a set) t = ((s INTER t) = EMPTY)”));

(* from src/pred_set/src/pred_setScript.sml:1808-1810 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val IMAGE_DEF =
    new_definition
    ("IMAGE_DEF", (“IMAGE (f:'a->'b) s = {f x | x IN s}”));

(* from src/pred_set/src/pred_setScript.sml:4761-4763 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
Definition BIGUNION[nocompute]:
  BIGUNION P = { x | ?s. s IN P /\ x IN s}
End

(* from src/pred_set/src/pred_setScript.sml:2909-2913 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val FINITE_DEF =
 new_definition
 ("FINITE_DEF",
  (“!s:'a set.
    FINITE s = !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s”));

(* from src/pred_set/src/pred_setScript.sml:3428-3428 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val CARD_DEF = new_specification ("CARD_DEF", ["CARD"], CARD_EXISTS);

(* from src/pred_set/src/pred_setScript.sml:2018-2023 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val INJ_DEF =
    new_definition
    ("INJ_DEF",
     (“INJ (f:'a->'b) s t <=>
          (!x. x IN s ==> (f x) IN t) /\
          (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y))”));

(* from src/pred_set/src/pred_setScript.sml:2113-2118 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val SURJ_DEF =
    new_definition
    ("SURJ_DEF",
     (“SURJ (f:'a->'b) s t <=>
           (!x. x IN s ==> (f x) IN t) /\
           (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))”));

(* from src/pred_set/src/pred_setScript.sml:2184-2187 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val BIJ_DEF =
    new_definition
    ("BIJ_DEF",
     (“BIJ (f:'a->'b) s t <=> INJ f s t /\ SURJ f s t”));

(* from src/string/stringScript.sml:277-289 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 c3839af5eda2e4d063374780f66c18c1083dc7c0a881efe2565cef147dd676a7 *)
Definition TOKENS_def:
  (TOKENS P ([]:string) = []) /\
  (TOKENS P (h::t) =
      let (l,r) = SPLITP P (h::t) in
        if NULL l then
          TOKENS P (TL r)
        else
          l::TOKENS P r)
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
    THEN SRW_TAC [] [NULL_EQ_NIL, SPLITP]
    THEN METIS_TAC [SPLITP_MONO, DECIDE ``a <= b ==> a < SUC b``]
End

