(* from src/pred_set/src/pred_setScript.sml:81-81 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
Type set = “:'a -> bool”;

(* from src/bool/boolScript.sml:252-253 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 a235171997f339a7629627acfc898d5deafadd28a33a54041f47bc5a862ec1eb *)
val IN_DEF = def (#(FILE), #(LINE))
   ("IN_DEF",         “IN = \x (f:'a->bool). f x”);

(* from src/pred_set/src/pred_setScript.sml:316-317 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val EMPTY_DEF = new_definition
    ("EMPTY_DEF", (“EMPTY = (\x:'a.F)”));

(* from src/pred_set/src/pred_setScript.sml:348-349 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val UNIV_DEF = new_definition
    ("UNIV_DEF",(“UNIV = (\x:'a.T)”));

(* from src/pred_set/src/pred_setScript.sml:1086-1088 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val INSERT_DEF =
    new_infixr_definition
    ("INSERT_DEF", (“INSERT (x:'a) s = {y | (y = x) \/ y IN s}”),490);

(* from src/pred_set/src/pred_setScript.sml:629-630 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val UNION_DEF = new_infixl_definition
     ("UNION_DEF", (“UNION s t = {x:'a | x IN s \/ x IN t}”),500);

(* from src/pred_set/src/pred_setScript.sml:724-726 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val INTER_DEF = new_infixl_definition
     ("INTER_DEF",
      (“INTER s t = {x:'a | x IN s /\ x IN t}”), 600);

(* from src/pred_set/src/pred_setScript.sml:949-951 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val DIFF_DEF = new_infixl_definition
    ("DIFF_DEF",
     (“DIFF s t = {x:'a | x IN s /\ ~ (x IN t)}”),500);

(* from src/pred_set/src/pred_setScript.sml:1808-1810 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val IMAGE_DEF =
    new_definition
    ("IMAGE_DEF", (“IMAGE (f:'a->'b) s = {f x | x IN s}”));

(* from src/pred_set/src/pred_setScript.sml:4761-4763 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
Definition BIGUNION[nocompute]:
  BIGUNION P = { x | ?s. s IN P /\ x IN s}
End

(* from src/pred_set/src/pred_setScript.sml:836-837 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
val DISJOINT_DEF = new_definition ("DISJOINT_DEF",
(“DISJOINT (s:'a set) t = ((s INTER t) = EMPTY)”));

(* from src/pred_set/src/pred_setScript.sml:410-412 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 71ffc8f9e57a2ec90489d4b43e1e11efc4b9b11784ee45b3aec0835d4c35df9c *)
Definition SUBSET_DEF[nocompute]:
  $SUBSET s t = !x:'a. x IN s ==> x IN t
End

