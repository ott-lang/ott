/**************************************************************************/
/*                                                                        */
/*  Menhir                                                                */
/*                                                                        */
/*  François Pottier, INRIA Paris-Rocquencourt                            */
/*  Yann Régis-Gianas, PPS, Université Paris Diderot                      */
/*                                                                        */
/*  Copyright 2005-2015 Institut National de Recherche en Informatique    */
/*  et en Automatique. All rights reserved. This file is distributed      */
/*  under the terms of the GNU Library General Public License, with the   */
/*  special exception on linking described in file LICENSE.               */
/*                                                                        */
/**************************************************************************/

/* nonempty2 variants of the menhir standard library lists, Peter Sewell, 2017-05 */ 

%%

(* [nonempty2_list(X)] recognizes a list of two or more [X]'s. It produces
   a value of type ['a list] if [X] produces a value of type ['a]. The
   front element of the list is the first element that was parsed. *)

%public nonempty2_list(X):
  x1 = X  x2 = X
    { [ x1 ; x2 ] }
| x = X; xs = nonempty2_list(X)
    { x :: xs }

(* [separated_nonempty2_list(separator, X)] recognizes list of
   two or more [X]'s, separated with [separator]'s. It produces a value of type
   ['a list] if [X] produces a value of type ['a]. The front element
   of the list is the first element that was parsed. *)

%public separated_nonempty2_list(separator, X):
  x1 = X; separator; x2 = X
    { [ x1; x2 ] }
| x = X; separator; xs = separated_nonempty2_list(separator, X)
    { x :: xs }



(* [tuple(X1, .... ,Xn)] recognizes the sequence [X1 X2]. It produces a value of
   type ['a1 * .... * 'an] if each [Xi] produces values of type ['ai]. *)

%public %inline tuple2(X1, X2):
  x1 = X1; x2 = X2
    { (x1, x2) }

%public %inline tuple3(X1, X2, X3):
  x1 = X1; x2 = X2; x3 = X3
    { (x1, x2, x3) }

%public %inline tuple4(X1, X2, X3, X4):
  x1 = X1; x2 = X2; x3 = X3; x4 = X4
    { (x1, x2, x3, x4) }

%public %inline tuple5(X1, X2, X3, X4, X5):
  x1 = X1; x2 = X2; x3 = X3; x4 = X4; x5 = X5
    { (x1, x2, x3, x4, x5, x6) }

%public %inline tuple6(X1, X2, X3, X4, X5, X6):
  x1 = X1; x2 = X2; x3 = X3; x4 = X4; x5 = X5; x6 = X6
    { (x1, x2, x3, x4, x5, x6) }

%public %inline tuple7(X1, X2, X3, X4, X5, X6, X7):
  x1 = X1; x2 = X2; x3 = X3; x4 = X4; x5 = X5; x6 = X6; x7=X7
    { (x1, x2, x3, x4, x5, x6, x7) }


%%



