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

val no_rbcatn : bool ref
val pp_list_mono_lemmas : Types.pp_mode -> unit
val pp_list_all_cong_lemma : Types.pp_mode -> unit
val pp_list_simp_lemmas : Types.pp_mode -> Types.syntaxdefn -> unit
val pp_auxfns :
      Types.pp_mode -> 
      Types.syntaxdefn -> 
      (Types.auxfn * Types.auxfn_type) list -> 
      Types.int_funcs_collapsed
val pp_foo_with_dependencies :
    Types.pp_mode ->
    Types.syntaxdefn ->
    (Types.syntaxdefn -> Types.nontermroot -> Types.prod -> bool) ->
    (Types.pp_mode ->
    Types.syntaxdefn ->
    Types.nontermroot list -> Types.rule -> Types.int_func list) ->
    Types.int_funcs
val pp_substs :
    Types.pp_mode -> Types.syntaxdefn -> Types.subst list -> Types.int_funcs_collapsed
val freevar_manifestly_needed :
    Types.freevar -> Types.syntaxdefn -> Types.nontermroot -> Types.prod -> bool
val pp_freevars :
    Types.pp_mode -> Types.syntaxdefn -> Types.freevar list -> Types.int_funcs_collapsed
