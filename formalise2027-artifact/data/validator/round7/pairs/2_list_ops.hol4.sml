(* from src/finite_maps/alistScript.sml:32-35 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 0c043051862508cee23adf396b0cabb523d10c177f3d47a1a98dd88bae4e2a87 *)
Definition ALOOKUP_def[simp]:
  (ALOOKUP [] q = NONE) /\
  (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q)
End

(* from src/list/src/listScript.sml:3933-3936 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition LUPDATE_DEF[notuserdef,nocompute]:
  LUPDATE e n [] = [] /\
  LUPDATE e n (x::l) = if n = 0 then e :: l else x :: LUPDATE e (PRE n) l
End

(* from src/list/src/listScript.sml:239-242 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition EL_def:
  EL 0 l = (HD l:'a) /\
  EL (SUC n) l = EL n (TL l)
End

(* from src/list/src/listScript.sml:2213-2216 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition TAKE_def[nocompute]:
  (TAKE n [] = []) /\
  (TAKE n (x::xs) = if n = 0 then [] else x :: TAKE (n - 1) xs)
End

(* from src/list/src/listScript.sml:2218-2221 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition DROP_def[nocompute]:
  (DROP n [] = []) /\
  (DROP n (x::xs) = if n = 0 then x::xs else DROP (n - 1) xs)
End

(* from src/list/src/listScript.sml:3260-3263 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition GENLIST:
  GENLIST (f:num->'a) 0 = [] /\
  GENLIST f (SUC n) = SNOC (f n) (GENLIST f n)
End

(* from src/list/src/listScript.sml:1778-1805 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
val ZIP_def =
    let val lemma = prove(
    (“?ZIP.
       (!l2. ZIP ([], l2) = []) /\
       (!l1. ZIP (l1, []) = []) /\
       (!(x1:'a) l1 (x2:'b) l2.
        ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2)(ZIP (l1, l2)))”),
    let val th = prove_rec_fn_exists list_Axiom
        (“(fn [] l = []) /\
         (fn (CONS (x:'a) l') (l:'b list) =
            if l = [] then [] else
              CONS (x, (HD l)) (fn  l' (TL l)))”)
        in
    STRIP_ASSUME_TAC th
    THEN EXISTS_TAC
           (“UNCURRY (fn:('a)list -> (('b)list -> ('a # 'b)list))”)
    THEN ASM_REWRITE_TAC[pairTheory.UNCURRY_DEF, HD, TL, NOT_CONS_NIL]
    THEN STRIP_TAC
    THEN STRIP_ASSUME_TAC (SPEC “l1:'a list” list_CASES)
    THEN ASM_REWRITE_TAC[]
     end)
    in
    Rsyntax.new_specification
        {consts = [{const_name = "ZIP", fixity = NONE}],
         name = "ZIP_def",
         sat_thm = lemma
        }
    end;

(* from src/list/src/listScript.sml:1837-1842 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition UNZIP:
    (UNZIP [] = ([], [])) /\
    (UNZIP (CONS (x:'a # 'b) l) =
               (CONS (FST x) (FST (UNZIP l)),
                CONS (SND x) (SND (UNZIP l))))
End

(* from src/list/src/listScript.sml:229-232 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition EVERY_DEF[simp]:
  (EVERY P [] <=> T) /\
  (EVERY P (h::t) <=> P h /\ EVERY P t)
End

(* from src/list/src/listScript.sml:234-237 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition EXISTS_DEF[simp]:
  (EXISTS P [] <=> F) /\
  (EXISTS P (h::t) <=> P h \/ EXISTS P t)
End

(* from src/list/src/listScript.sml:2507-2510 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition ALL_DISTINCT[nocompute,simp]:
  (ALL_DISTINCT [] <=> T) /\
  (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t)
End

(* from src/list/src/listScript.sml:198-198 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Overload MEM = “\h:'a l:'a list. h IN LIST_TO_SET l”

(* from src/list/src/listScript.sml:190-192 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Theorem LIST_TO_SET_DEF[simp,compute]:
  (!x. LIST_TO_SET [] x <=> F) /\
  (!h t x. LIST_TO_SET (h::t) x <=> (x = h) \/ LIST_TO_SET t x)

(* from src/list/src/listScript.sml:1454-1458 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Theorem LIST_REL_def[simp,compute,allow_rebind]:
  (LIST_REL R []      []      <=> T) /\
  (LIST_REL R (a::as) []      <=> F) /\
  (LIST_REL R []      (b::bs) <=> F) /\
  (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs)

(* from src/sort/sortingScript.sml:17-18 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 47f7e4cc622495e5d5a58a75e9d28f8f7a5f47c576d086c4d38da053d83effd4 *)
Definition PERM_DEF:  PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2
End

(* from src/list/src/rich_listScript.sml:57-60 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 81072413b1535bb76676e96595a8813ab08d5d6c78ef0bb9dd2773e2981986f7 *)
Definition REPLICATE[simp]:
   (REPLICATE 0 x = []) /\
   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))
End

(* from src/list/src/listScript.sml:167-170 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition FLAT[simp]:
  FLAT []     = [] /\
  FLAT (h::t) = APPEND h (FLAT t)
End

(* from src/list/src/listScript.sml:266-269 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition MAP2_DEF[simp]:
  (MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2) /\
  (MAP2 f x y = [])
End

(* from src/list/src/listScript.sml:214-217 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition FILTER[simp]:
  FILTER P [] = [] /\
  FILTER P (h::t) = if P h then (h::FILTER P t) else FILTER P t
End

(* from src/list/src/listScript.sml:4583-4586 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition nub_def:
   (nub [] = []) /\
   (nub (x::l) = if MEM x l then nub l else x :: nub l)
End

(* from src/list/src/listScript.sml:3045-3048 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition SNOC[simp]:
  (SNOC x [] = [x]) /\
  (SNOC x (CONS x' l) = CONS x' (SNOC x l))
End

(* from src/list/src/listScript.sml:2053-2056 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition REVERSE_DEF[nocompute,simp]:
  (REVERSE [] = []) /\
  (REVERSE (h::t) = (REVERSE t) ++ [h])
End

(* from src/list/src/rich_listScript.sml:307-307 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 81072413b1535bb76676e96595a8813ab08d5d6c78ef0bb9dd2773e2981986f7 *)
Overload IS_PREFIX = ``\x y. isPREFIX y x``

(* from src/list/src/listScript.sml:3010-3014 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition isPREFIX[simp]:
  (isPREFIX [] l = T) /\
  (isPREFIX (h::t) l = case l of [] => F
                               | h'::t' => (h = h') /\ isPREFIX t t')
End

(* from src/list/src/listScript.sml:5551-5554 at ref develop, sha unknown, fetched 2026-10-15T10:29:52Z; file sha256 737cad11d350bed7a2532b40c7e81cbeb05db21dffe37a569514675f1ee351e0 *)
Definition oEL_def:
  (oEL n [] = NONE) /\
  (oEL n (x::xs) = if n = 0 then SOME x else oEL (n - 1) xs)
End

