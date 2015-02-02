(*
** Project Euler: P2
** See https://projecteuler.net
*)
(* ****** ****** *)
//
// Author: Hongwei Xi
// Authoremail: gmhwxiATgmailDOTcom
// Start time: January 13, 2015
//
(* ****** ****** *)
//
// Author: Brandon Barker
// Authoremail: brandonDOTbarkerATgmailDOTcom
// Start time: January 31, 2015
//
(* ****** ****** *)
//
#include "share/atspre_define.hats"
//
(* ****** ****** *)
//
staload
"{$LIBATSHWXI}/PEULER/SATS/peuler.sats"
//
(* ****** ****** *)
//
staload P2 = "{$PATSHOMERELOC}/projects/MEDIUM/PEULER/P2/P2.sats"
//
(* ****** ****** *)
//
#define LIMIT 4000000
//
(* ****** ****** *)
//
// MYSUM (n2, n1, t) =
// t = sum of all the even fibs <= LIMIT starting from n2, n1
//
dataprop MYSUM
(
  int(*n2*), int(*n1*), int(*t*)
) =
  | {n2,n1:nat | n1 + n2 > LIMIT}
    {t1:int}
    MYSUM_fin (n2, n1 + n2, t1) of MYSUM (n2, n1, t1)
  | {n2,n1:nat | n1 + n2 <= LIMIT; (n1 + n2) mod 2 > 0}
    {t1:int}
    MYSUM_same (n1, n1 + n2, t1) of MYSUM (n2, n1, t1)
  | {n2,n1:nat | n1 + n2 <= LIMIT; (n1 + n2) mod 2 == 0}
    {t1:int}
    MYSUM_inc (n1, n1 + n2, n1 + n2 + t1) of MYSUM (n2, n1, t1)
// end of [MYSUM]

(* ****** ****** *)
//
// Now we should show that the original, abstract definition of
// MYSUM is equivalent to the MYSUM defined above. More precisely,
// we should show the MYSUM above implies $P2.MYSUM, as strict
// equivalence is not necessary as long as we satisfy the specification
// of $P2.MYSUM.
//
(* ****** ****** *)

// Note recurrence subscripts as follows: x_n = x_(n-1) - x_(n-2)
//                                                (*n1*)    (*n2*)
//
praxi
MYSUM_sat
  {n1,n2,t:nat}
  (pf1: MYSUM(n2, n1, t)):
  ($P2.FIB(n2, n1+n2), $P2.MYSUM(n2, t))


praxi
MYSUM_un_same
  {n1,n2,t:nat | n1 + n2 <= LIMIT; (n1 + n2) mod 2 > 0}
  (pf1: MYSUM(n2, n1, t)): MYSUM(n1, n1 + n2, t)
//
praxi
MYSUM_un_fin
  {n1,n2,t:nat | n1 + n2 > LIMIT}
  (pf1: MYSUM(n2, n1, t)): MYSUM(n1, n1 + n2, t)
//
praxi
MYSUM_un_inc
  {n1,n2,t:nat | n1 + n2 <= LIMIT; (n1 + n2) mod 2 == 0}
  (pf1: MYSUM(n2, n1, t)): MYSUM(n1, n1 + n2, t + n1 + n2)


//
(* ****** ****** *)

praxi
MYSUM_BAS (n2: int 1, n1: int 2, t: int 2):
  [n1o,n2o,to:int | n1o == 2; n2o == 1; to == 2] MYSUM(n2o, n1o, to)


//
// TODO: annotate inputs with FIB relationship
//
fun mysum (x_n2: int 1, x_n1: int 2, tl: int 2):
  [n2f,n1f,tf: nat] (MYSUM (n2f, n1f, tf) | int tf)
//