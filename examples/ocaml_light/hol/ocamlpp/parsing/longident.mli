(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id: longident.mli,v 1.1 2007/09/24 23:04:50 so294 Exp $ *)

(* Long identifiers, used in parsetree. *)

type t =
    Lident of string
  | Ldot of t * string
  | Lapply of t * t

val flatten: t -> string list
val parse: string -> t
