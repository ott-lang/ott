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

exception Merge of string
exception Abstract_indexvar_non_linear
val merge_metavar :
  int -> Types.metavar * Types.metavar -> Types.bound option * Types.metavar
val merge_nonterm :
  int -> Types.nonterm * Types.nonterm -> Types.bound option * Types.nonterm
val merge_element_list :
  int ->
  Types.element list * Types.element list ->
  Types.bound option * Types.element list
val merge_symterm_element_list :
  int ->
  Types.symterm_element list * Types.symterm_element list ->
  (Types.suffix_item * Types.suffix_item) option * Types.symterm_element list
val merge_suffix_against_index :
  int ->
  Types.suffix * Types.suffix ->
  (Types.suffix_item * Types.suffix_item) option * Types.suffix

val abstract_indexvar_suffix_linear :
  Types.metavarroot -> int -> Types.suffix -> Types.suffix
val abstract_indexvar_element :
  Types.metavarroot -> int -> Types.element -> Types.element
val abstract_indexvar_symterm_element :
  Types.metavarroot -> int -> Types.symterm_element -> Types.symterm_element
