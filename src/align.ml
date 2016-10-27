(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2006                                                   *)
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

open Types

let split_line (s:string) : string * int * string option =
  try
    let l = String.length s in
    let idx = (String.index s '\n') + 1 in
    let line = String.sub s 0 idx in
    let rest = String.sub s idx (l - idx) in
    (line, idx, Some rest) 
  with Not_found -> (s, (String.length s), None)

let rec insert_spaces n =
  if n = 0 then "" else " "^(insert_spaces (n-1))

let align_line (m:pp_mode) (s:string) (l:int) : string =
  match m with
  | Coq _ ->
      if l > 80 
      then 
        (* rule 1: in a pattern-matching, insert a newline after the pattern *)
        let rgx = Str.regexp "[ \t]*|.*=>" in
        if (Str.string_match rgx s 0)
        then begin
           let pos = (Str.search_forward (Str.regexp "=>") s 0) + 2 in
           let first_line = String.sub s 0 pos in
           let second_line = String.sub s pos (l - pos) in
           first_line ^"\n" ^ (insert_spaces 5) ^ second_line
        end
        else s
      else s
  | _ -> s

let rec align_doc m s =
  match split_line s with
  | (s,l,None) -> align_line m s l
  | (s,l,Some r) -> (align_line m s l) ^ (align_doc m r)

(* FZ rename align_doc into align *)
let align (m:pp_mode) (s:string) : string =
  match m with
  | Coq _ -> (* align_doc m *) s
  | _ -> s
