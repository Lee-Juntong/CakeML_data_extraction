(*
  Pure functions for the List module.
*)
Theory mllist
Libs
  preamble
Ancestors
  indexedLists[qualified] toto[qualified]
  sorting mergesort

Definition sort_def:
  sort = mergesort$mergesort_tail
End

Definition nth_def:
  nth l i = EL i l
End

(* these definitions are in A normal form in
   order to be able to prove CF specs about them
   (in addition to the translator-generated ones)
   (the CF specs allow more general arguments f) *)

Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End

