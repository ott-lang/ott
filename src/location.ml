(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2010                                                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

type t = 
    { loc_start : Lexing.position;
      loc_end : Lexing.position }

let loc_of_filename name len  = 
  [ {loc_start =  
     {
      Lexing.pos_fname =name;
      Lexing.pos_lnum = 0;
      Lexing.pos_bol =0;
      Lexing.pos_cnum =0 };
     loc_end =
     {
      Lexing.pos_fname =name;
      Lexing.pos_lnum =0;
      Lexing.pos_bol =0;
      Lexing.pos_cnum =len }
} ]

let pp_position 
    { Lexing.pos_fname = f;
      Lexing.pos_lnum = l;
      Lexing.pos_bol = b;
      Lexing.pos_cnum = c } = 
  "fname=" ^ f ^ "  lnum=" ^ string_of_int l
  ^ "  bol="^string_of_int b^"  cnum=" ^string_of_int c

let pp_position2  
    { Lexing.pos_fname = f;
      Lexing.pos_lnum = l;
      Lexing.pos_bol = b;
      Lexing.pos_cnum = c } = 
  (if f="" then "" else "file=" ^ f ^ "  ")
  ^ "line=" ^ string_of_int l ^ "  char=" ^ string_of_int (c-b)

let pp_t {loc_start=ls;loc_end=le} = 
  if ls.Lexing.pos_fname = le.Lexing.pos_fname 
      && ls.Lexing.pos_lnum = le.Lexing.pos_lnum 
  then 
    (* start and end are in the same file and line *)
    (if ls.Lexing.pos_fname="" then "" else "file " ^ ls.Lexing.pos_fname ^ "  ")
    ^ "line "
    ^ string_of_int ls.Lexing.pos_lnum
    ^ " char "
    ^ string_of_int (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
    ^ " - "
    ^ string_of_int (le.Lexing.pos_cnum - le.Lexing.pos_bol)
  else if ls.Lexing.pos_fname = le.Lexing.pos_fname 
      && ls.Lexing.pos_cnum - ls.Lexing.pos_bol = 0
      && le.Lexing.pos_cnum - le.Lexing.pos_bol = 0 
  then
    (* start and end are in the same file but different lines, at the starts of those lines *)
    (if ls.Lexing.pos_fname="" then "" else "file " ^ ls.Lexing.pos_fname ^ "  ")
    ^ "line "
    ^ string_of_int ls.Lexing.pos_lnum
    ^ " - "
    ^ string_of_int le.Lexing.pos_lnum
  else 
    (* start and end are in the same file but different lines, at some non-start chars *)
    (if ls.Lexing.pos_fname="" then "" else "file " ^ ls.Lexing.pos_fname ^ "  ")
    ^ "line "
    ^ string_of_int ls.Lexing.pos_lnum
    ^ " char "
    ^ string_of_int (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
    ^ " - " 
    ^ "line "
    ^ string_of_int le.Lexing.pos_lnum
    ^ " char "
    ^ string_of_int (le.Lexing.pos_cnum - le.Lexing.pos_bol)


let pp_t2 {loc_start=ls;loc_end=le} = 
  (* start and end are in the same file but different lines, at the starts of those lines *)
  "file " ^ (if ls.Lexing.pos_fname="" then "?" else ls.Lexing.pos_fname) 
  ^ "  "
  ^ "lines "
  ^ string_of_int ls.Lexing.pos_lnum
  ^ " - "
  ^ string_of_int le.Lexing.pos_lnum

let pp_t_source l = "#source "^ String.concat " and " (List.map pp_t2 l)

(* #source file FILENAME1 lines M1 - N1  and ... and FILENAMEk lines Mk - Nk *) 


let dummy_pos = 
  { Lexing.pos_fname = "dummy";
    Lexing.pos_lnum = 0;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = 0 }

let dummy_t =  
  { loc_start=dummy_pos;
    loc_end=dummy_pos }

let pp_loc l = String.concat " " ((List.map pp_t) l)

let pos_plus_offset pos n = {pos with
                             Lexing.pos_bol = pos.Lexing.pos_bol + n;
                             Lexing.pos_cnum = pos.Lexing.pos_cnum + n;}

let loc_of pos n = [ {loc_start=pos; 
                      loc_end= pos_plus_offset pos n} ]

let merge_loc l l' = l @ l'

(* let pos_of_loc l = match l with *)
(* |  {loc_start=pos1;loc_end=pos2} :: _ -> pos1 *)
(* |  [] -> dummy_pos *)

(* *** ATTIC *** *)
    
(* type 'a located = { desc : 'a; loc : t } *)
(* let del {desc=x; loc=l} = x *)
(* let loc {desc=x; loc=l} = l *)
(* let dummy_enloc x = {desc=x;loc=dummy_t} *)

let merge_locs l_first l_last  = 
  let n = List.length l_last in
  try
    [{loc_start = (List.hd l_first).loc_start; 
      loc_end = (List.nth l_last (n -1 )).loc_end } ]
  with _ -> l_first

(* FZ Ugly, but does the job *)
open Lexing

(* should not be invoked on dummy locs *)
let compare_locs file_list
    { loc_start = ls1; loc_end = _ } 
    { loc_start = ls2; loc_end = _ } : int = 
  let compare_files n1 n2 =
    let rec compare_int l =
      match l with
      | [] -> 
          (* should be error *)
          failwith "internal: compare_locs, empty file list.\n" 
      | x::xs -> 
          if String.compare x n1 = 0 
          then -1 
          else 
            if String.compare x n2 = 0 then 1 else compare_int xs
    in 
    if String.compare n1 n2 = 0 then 0 else compare_int file_list in
  if compare_files ls1.pos_fname ls2.pos_fname = -1 then -1
  else if compare_files ls1.pos_fname ls2.pos_fname = 1 then 1
  else compare ls1.pos_lnum ls2.pos_lnum 

let is_dummy_pos l =
  match l with
  | [] -> false
  | ls::_ ->
      String.compare ls.loc_start.pos_fname "dummy" = 0 && ls.loc_start.pos_cnum = 0  

let same_file l1 l2 = 
  match l1,l2 with
  | [],[] | _::_,[] | [],_::_ ->
      (* should be error *)
      failwith "internal: same_file, empty loc list.\n" 
  | x::_,y::_ -> if String.compare x.loc_start.pos_fname y.loc_start.pos_fname = 0 then true else false

let extract_file l = 
  match l with
  | [] ->
      (* should be error *)
      failwith "internal: extract_file, empty loc list.\n" 
  | x::_ -> x.loc_start.pos_fname 
