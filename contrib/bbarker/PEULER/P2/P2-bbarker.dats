(*
** Project Euler: P2
** See https://projecteuler.net
*)
(* ****** ****** *)
//
// Author: Brandon Barker
// Authoremail: brandonDOTbarkerATgmailDOTcom
// Start time: January 31, 2015
//
(* ****** ****** *)
//
#include
"share/atspre_define.hats"
#include
"share/atspre_staload.hats"
//
(* ****** ****** *)
//
staload "P2-bbarker.sats"
//
(* ****** ****** *)
//
#define LIMIT 4000000
//
(* ****** ****** *)

extern
praxi
my_mod2 {n:nat} (int(n)): [m:nat | m == n; m mod 2 == 0] int m //int(n%2)


implement
mysum (x_n2, x_n1, t) = let
//
prval pf0 = MYSUM_BAS(x_n2, x_n1, t)
//
fun
loop
{ln2,ln1,lt:nat}
(
  pf1: MYSUM(ln2, ln1, lt)
  | x_n2: int ln2, x_n1: int ln1, t: int lt
) : [t1:nat] (MYSUM (ln1, ln1 + ln2, t1) | int t1) = let
//
val x_n = x_n1 + x_n2
val (pf_r_xn | r_xn) =  nmod2_g1int_int1(x_n, 2)
//
(*
val () =
  println! (x_n, ", ", x_n1, ", ", x_n2, ", ", t)
*)
//
in
//
if
x_n > LIMIT
then (MYSUM_un_fin(pf1) | t)
else (
  if nmod(x_n, 2) = 0
    then let prval pf_mod2 = my_mod2(x_n) in
      loop( MYSUM_un_inc(pf1) | x_n1, x_n, t + x_n)
    end
  else loop( MYSUM_un_same(pf1) | x_n1, x_n, t)
  // end of [if]
) (* end of [else] *)
end // end of [if]
//
in
  loop(pf0 | x_n1 , x_n2, t)
end

(* ****** ****** *)

// BB:
// loop() could recall if prior two terms were even or odd
// but this doesn't really seem worthwhile

(* ****** ****** *)

implement
main0 () =
{
//
val (pf | ans) = mysum(1, 2, 2)
// We should now verify pf is MYSUM_fin

prval pf_final = MYSUM_sat(pf) // Ideally this would be implemented.
val () = println! ("The sum of all the even fibs < ", LIMIT, " equals ", ans)
//
} (* end of [main0] *)

(* ****** ****** *)

(* end of [P2-bbarker.dats] *)
