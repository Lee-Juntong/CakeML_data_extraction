(* from src/finite_maps/sptreeScript.sml:30-31 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt
End

(* from src/finite_maps/sptreeScript.sml:46-56 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition lookup_def[nocompute]:
  (lookup k LN = NONE) /\
  (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
  (lookup k (BN t1 t2) =
     if k = 0 then NONE
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
  (lookup k (BS t1 a t2) =
     if k = 0 then SOME a
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2))
Termination WF_REL_TAC `measure FST` >> simp[DIV_LT_X]
End

(* from src/finite_maps/sptreeScript.sml:67-85 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition insert_def[nocompute]:
  (insert k a LN = if k = 0 then LS a
                     else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                     else BN LN (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (LS a') =
     if k = 0 then LS a
     else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
     else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (BN t1 t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
     else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
  (insert k a (BS t1 a' t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
     else BS t1 a' (insert ((k - 1) DIV 2) a t2))
Termination
  WF_REL_TAC `measure FST` >> simp[DIV_LT_X]
End

(* from src/finite_maps/sptreeScript.sml:99-114 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition delete_def[nocompute]:
  (delete k LN = LN) /\
  (delete k (LS a) = if k = 0 then LN else LS a) /\
  (delete k (BN t1 t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       mk_BN (delete ((k - 1) DIV 2) t1) t2
     else
       mk_BN t1 (delete ((k - 1) DIV 2) t2)) /\
  (delete k (BS t1 a t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       mk_BS (delete ((k - 1) DIV 2) t1) a t2
     else
       mk_BS t1 a (delete ((k - 1) DIV 2) t2))
End

(* from src/finite_maps/sptreeScript.sml:1478-1481 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition fromAList_def[simp]:
  (fromAList [] = LN) /\
  (fromAList ((x,y)::xs) = insert x y (fromAList xs))
End

(* from src/finite_maps/sptreeScript.sml:473-482 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition domain_def[simp,nocompute]:
  domain LN = {} /\
  domain (LS _) = {0} /\
  domain (BN t1 t2) =
     IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2) /\
  domain (BS t1 _ t2) =
     {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2)
End

(* from src/finite_maps/sptreeScript.sml:1106-1111 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition toListA_def:
  (toListA acc LN = acc) /\
  (toListA acc (LS a) = a::acc) /\
  (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
  (toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1)
End

(* from src/finite_maps/sptreeScript.sml:1132-1133 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition toList_def:  toList m = toListA [] m
End

(* from src/finite_maps/sptreeScript.sml:737-748 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition foldi_def:
  (foldi f i acc LN = acc) /\
  (foldi f i acc (LS a) = f i a acc) /\
  (foldi f i acc (BN t1 t2) =
     let inc = lrnext i
     in
       foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2) /\
  (foldi f i acc (BS t1 a t2) =
     let inc = lrnext i
     in
       foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2)
End

(* from src/finite_maps/sptreeScript.sml:898-900 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 97791ac7f3f7b0de823afb00f6f1fbd18cd158b9fe8a818a272b39daa0e49b71 *)
Definition toAList_def:
  toAList = foldi (\k v a. (k,v)::a) 0 []
End

(* from src/coalgebras/llistScript.sml:64-64 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 f98d61fdbbb10fd69cea06b92a1c2317e9b32dd313f0079f8e666f1168146955 *)
val llist_tydef = new_type_definition ("llist", type_inhabited);

(* from src/coalgebras/llistScript.sml:2655-2663 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 f98d61fdbbb10fd69cea06b92a1c2317e9b32dd313f0079f8e666f1168146955 *)
Definition LPREFIX_def:
  LPREFIX l1 l2 =
    case toList l1 of
    | NONE => (l1 = l2)
    | SOME xs =>
        case toList l2 of
        | NONE => LTAKE (LENGTH xs) l2 = SOME xs
        | SOME ys => isPREFIX xs ys
End

(* from src/coalgebras/llistScript.sml:1154-1156 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 f98d61fdbbb10fd69cea06b92a1c2317e9b32dd313f0079f8e666f1168146955 *)
Definition fromList_def[simp]:
  (fromList [] = LNIL) /\ (fromList (h::t) = LCONS h (fromList t))
End

(* from src/coalgebras/llistScript.sml:1140-1142 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 f98d61fdbbb10fd69cea06b92a1c2317e9b32dd313f0079f8e666f1168146955 *)
Definition toList[nocompute]:
  toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE
End

