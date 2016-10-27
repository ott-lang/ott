(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2007                                                   *)
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

(* 
Parsing symbolic terms (as they appear in typing and operational
rules, ie with metavars and nonterms, as well as object-level vars).
*)

open Types;;

exception ThisCannotHappen;;
exception Parse_error of loc * string;;

(* only used for main.ml test parse - should replace by use of psuedoterminal*)
let ident_string = 
(* "\\([A-Z]\\|[a-z]\\|[_]\\)\\([A-Z]\\|[a-z]\\|[0-9]\\|[_]\\|[-]\\|[']\\)*" *)
  "\\([A-Z]\\|[a-z]\\|[_]\\)\\([A-Z]\\|[a-z]\\|[0-9]\\|[_]\\|[']\\)*" 


(* ************************************************ *)
(* error reporting for term lexing and parsing      *)
(* ************************************************ *)


(* remaining input, for error reporting (imperative!) *)
(* In principle this has poor complexity, as each time we parse a token *)
(* we calculate the length of the remaining input.  For our typical case, *)
(* however, it seems not to be too bad.*)

let debug = false

let p_debug s = if debug then (print_string s;flush stdout) else ()

let initial_input = ref 0
let furthest_pos = ref 0

let lookup_depth = ref 0

let reset_furthest_pos ts = 
  initial_input := List.length ts;
  furthest_pos := 0;
  lookup_depth :=0

let ok ts = 
  if debug then p_debug (Auxl.string_of_char_list ts ^ "\n");
  furthest_pos := max (!furthest_pos) 
      ( !initial_input - List.length ts)

let read_furthest_pos () = !furthest_pos

let error_string s0 s c = 
  s0
  ^
    let c=c+0 in
    if c > String.length s then "(internal overflow in building error string)"
    else
      let s1 = String.sub s 0 c in
      let s2 = String.sub s c (String.length s - c) in
      " (char "^string_of_int c^"): "^s1^"***"^s2^" "
                                                   
let no_parses_error_string s = 
  error_string "no parses" s (read_furthest_pos ()) 

let parse_error2 loc s msg = 
  raise (Parse_error (loc, msg))

(* more considered but currently unused code for building an *)
(* error string around a position in a long string *)
(* let parse_error s msg n1 n2 =  *)
(*   let n_left = min n1 (max 0 (n2+10-79)) in *)
(*   let n_right = min (n_left + 79) (String.length s) in *)
(*   let n_len = n_right - n_left in *)
(*   let s_fragment = String.sub s n_left n_len in *)
(*   let s_annote =  *)
(*     String.make (n1-n_left) ' ' ^  *)
(*     String.make (n2-n1 (\*fixme*\)) '^' in *)
(*   raise (Parse_error  *)
(*            (msg ^ " at character position "^  *)
(*             string_of_int n1^ ".."^string_of_int n2^"\n" ^  *)
(*             s_fragment ^ "\n" ^ *)
(*             s_annote ^ "\n"))  *)


(* ************************************************ *)
(* parser combinators                               *)
(* ************************************************ *)

type ('t, 'v) entry = { mutable ks : ('t list -> 'v -> unit) list;
                        mutable results : ('t list * 'v) list }
let push_k : ('t, 'v) entry -> ('t list -> 'v -> unit) -> unit = 
  fun entry k -> entry.ks <- k::entry.ks

let push_result : ('t, 'v) entry -> ('t list * 'v) -> unit = 
  fun entry result -> entry.results <- result::entry.results

let result_subsumed : ('t, 'v) entry -> ('t list * 'v) -> bool =
  fun entry result -> List.mem result entry.results

module type MEMO_TABLE =
sig
  type ('t, 'v) table
  val make_table : unit -> ('t, 'v) table
  val table_ref : ('t, 'v) table -> 't list -> ('t, 'v) entry
end

module Assoc_table : MEMO_TABLE = 
struct
  type ('t, 'v) table = ('t list * ('t, 'v) entry) list ref

  let make_table : unit -> ('t, 'v) table =
    fun () -> ref []

  let rec table_assoc =
    fun key table ->
    match table with
      [] -> None
    | (x, y)::t -> if key == x then Some y else table_assoc key t
(*    | (x, y)::t -> if key = x then Some y else table_assoc key t *)


  let table_ref : ('t, 'v) table -> 't list -> ('t, 'v) entry = 
    fun table key ->
    match table_assoc key (!table) with
      None ->
        let new_entry = {ks=[]; results=[]} in
          table := (key, new_entry)::!table;
          new_entry
    | Some e -> e
end

module Hash_table : MEMO_TABLE =
struct
  type ('t, 'v) table = ('t list, ('t, 'v) entry) Hashtbl.t

  let make_table : unit -> ('t, 'v) table =
    fun () -> Hashtbl.create 20 

  let rec table_ref : ('t, 'v) table -> 't list -> ('t, 'v) entry = 
    fun table key ->
    try
      Hashtbl.find table key
    with Not_found ->
      let new_entry = {ks=[]; results=[]} in
        Hashtbl.add table key new_entry;
        new_entry
end

open Hash_table

let memo : ('t, 'v) parser -> ('t, 'v) parser =
  fun cps_fn ->
  let table = make_table () in
  fun k ts ->
    match table_ref table ts with
      {ks=[]; results=_} as entry ->
        push_k entry k;
        cps_fn (fun results1 results2 ->
                 if not (result_subsumed entry (results1, results2)) then
                   (push_result entry (results1, results2);
                    List.iter (fun k -> k results1 results2) entry.ks)
                 else
                   ())
               ts
    | entry ->
        push_k entry k;
        List.iter (function (results1, results2) -> k results1 results2)
                  entry.results

let parse_fail : ('t, 'v) parser = fun k ts -> ()

let parse_single : ('t-> 'v list) -> ('t,'v) parser
    = fun f ->
      (*memo*) (
      fun k ts -> match ts with
        [] -> parse_fail k ts  (* fail *)
      | t'::ts' -> ok ts'; (List.iter (fun v -> k ts' v) (f t'))
      )

let parse_satisfy : ('t->bool) -> ('t,'t) parser
    = fun f ->
      (*memo*) (
      fun k ts -> match ts with
        [] -> parse_fail k ts  (* fail *)
      | t'::ts' -> if f t' then (ok ts'; k ts' t') else parse_fail k ts
      )

(* succeeds if either we've reached the end or the next token (which is *)
(* not consumed) satisfies f *)
let parse_satisfy_lookahead : ('t->bool) -> ('t,unit) parser
    = fun f ->
      (*memo*) (
      fun k ts -> match ts with
      | [] -> k ts () (* parse_fail k ts  (* fail *) *)
      | t'::ts' -> if f t' then k ts () else parse_fail k ts
      )

let parse_literal : 't -> ('t,'t) parser
    = fun t -> parse_satisfy ( (=) t)

let parse_satisfy' : ('t->bool) -> ('t,unit) parser
    = fun f ->
      (*memo*) (
      fun k ts -> match ts with
      | [] -> parse_fail k ts (* fail *)
      | t'::ts' -> if f t' then (ok ts'; k ts' ()) else parse_fail k ts'
      )

let parse_satisfy_opt' : ('t->'a option) -> ('t,'a) parser
    = fun f ->
      (*memo*) (
      fun k ts -> match ts with
      | [] -> parse_fail k ts (* fail *)
      | t'::ts' -> (match  f t' with
        | Some x -> (ok ts'; k ts' x )
        | None -> parse_fail k ts)
      )

let parse_nothing : ('t,unit) parser
    = fun k ts -> k ts ()

let parse_choice : ('a,'b) parser list -> ('a,'b) parser
    = fun ps ->
      (*memo*) (
      fun k ts ->
      List.iter (fun p -> p k ts) ps
      )

let parse_list_help :('a,'b) parser -> ('a,'b list) parser -> ('a,'b list) parser
    = fun p1 p2 ->
      (*memo*) (
      fun k ts ->
      p1 (fun ts' res -> p2 (fun ts'' res' -> k ts'' (res::res')) ts') ts
      )

let rec parse_list : ('a,'b) parser list -> ('a,'b list) parser
    = fun ps ->
      match ps with
        [] -> (*memo*) ( fun k ts -> k ts [] )
      | p1::ps -> parse_list_help p1 (parse_list ps)

let parse_pair :('a,'b1) parser -> ('a,'b2) parser -> ('a,'b1*'b2) parser
    = fun p1 p2 ->
      (*memo*) (
      fun k ts ->
      p1 (fun ts' res -> p2 (fun ts'' res' -> k ts'' (res, res')) ts') ts
      )

let parse_map : ('b->'c) -> ('a,'b) parser -> ('a,'c) parser
    = fun f p ->
      (*memo*) (
      fun k ts ->
        p (fun ts' res -> k ts' (f res)) ts
      )

let parse_option_map : ('b->'c option) -> ('a,'b) parser -> ('a,'c) parser
    = fun f p ->
      (*memo*) (
      fun k ts ->
        p (fun ts' res -> match f res with None -> () | Some w -> k ts' w) ts
      )

let parse_lift_singleton : ('a,'b) parser -> ('a,'b list) parser =
    fun p -> parse_map (fun v->[v]) p

let parse_lift_empty : ('a,'b) parser -> ('a,'c list) parser =
    fun p -> parse_map (fun v->[]) p

let parse_optional_prefix_single : ('t->bool)->('t,'a) parser -> ('t,'a) parser
    = fun f p ->
      (*memo*) (
      fun k ts -> match ts with
      | [] -> p k ts
      | t'::ts' -> if f t' then (ok ts'; p k ts') else p k ts
      )
        
let rec parse_star : ('a,'b) parser -> ('a,'b list) parser  
    = fun p ->
      memo (
      fun k ts ->
        k ts [];
        (parse_list_help p (parse_star p)) k ts 
      )

let parse_plus  : ('a,'b) parser -> ('a,'b list) parser  
    = fun p -> 
      parse_map (function (x,xs)->x::xs) (parse_pair p (parse_star p))


(* ************************************************ *)
(* auxilary little parsers                          *)
(* ************************************************ *)

let parse_string : string -> (char,string) parser
    = fun s ->
      parse_map
        (Auxl.string_of_char_list)
        (parse_list
           (List.map
              (function (c:char) -> parse_literal c)
              (Auxl.char_list_of_string s)))

let parse_strings : string list -> (char,string) parser
    = fun ss ->
      parse_choice
        (List.map parse_string ss)

let parse_nonalphanum_after 
    = fun p ->
      parse_map (function (x,y)->x) 
        (parse_pair p 
           (parse_satisfy_lookahead (function c -> not (Auxl.isalphanum c))))

let parse_string_nonalphanum_after s =
  if Auxl.last_char_isalphanum s then
    (parse_nonalphanum_after 
       (parse_string s))
  else
    (parse_string s)

let parse_maybe_fancy_suffix_var indexvars = 
  parse_map (function (s,n)->Si_var (s,n))
    (parse_pair
       (parse_strings indexvars)
       (parse_choice [
          (parse_map (function ()->  0) (parse_nothing));
          (parse_map (function s -> -1) (parse_string "-1"))]))

let parse_suffix_item indexvars = 
  parse_choice
    [
     parse_map (function c -> Si_num (String.make 1 c))
       (parse_satisfy (function c -> c>='0' && c<='9'));
     parse_map (function c -> Si_punct (String.make 1 c))
       (parse_satisfy Auxl.issuffixpunct);
     (parse_maybe_fancy_suffix_var indexvars);
   ] 

let rec agglomerate_Si_nums sis = 
  match sis with
  | [] -> []
  | (Si_num n) :: sis' -> agglomerate_Si_nums' n sis'
  | si :: sis' -> si :: agglomerate_Si_nums sis'
and agglomerate_Si_nums' n sis = 
  match sis with
  | [] -> [Si_num n]
  | (Si_num n') :: sis' -> agglomerate_Si_nums' (n^n') sis'
  | si :: sis' -> (Si_num n) :: si :: agglomerate_Si_nums sis' 

let parse_suffix indexvars =
  parse_map
    agglomerate_Si_nums
    (parse_star (parse_suffix_item indexvars)) 
      
let parse_with_suffix indexvars ss = 
  (parse_nonalphanum_after 
     (parse_pair
        (parse_strings ss)
        (parse_suffix indexvars)))

let parse_without_suffix ss = 
  (parse_nonalphanum_after 
     (parse_strings ss))

let parse_AZ = 
  (parse_nonalphanum_after 
     (parse_plus
        (parse_satisfy (function c -> c>='A' && c<= 'Z'))))

let parse_az = 
  (parse_nonalphanum_after 
     (parse_plus 
        (parse_satisfy (function c -> c>='a' && c<= 'z'))))

let parse_numeral = 
  (parse_nonalphanum_after 
     (parse_map Auxl.string_of_char_list
        (parse_plus 
           (parse_satisfy (function c -> c>='0' && c<= '9')))))

let parse_alphanum0 =
  (parse_nonalphanum_after
     (parse_map (function (c,cs) -> Auxl.string_of_char_list (c::cs))
        (parse_pair
           (parse_satisfy (function c -> c>='a' && c<= 'z'))
           (parse_star
              (parse_satisfy (function c -> 
                (c>='A' && c<= 'Z') || (c>='a' && c<= 'z') || (c>='0' && c<= '9') || c='\'' || c='_'))))))

let parse_alphanum =
  (parse_nonalphanum_after
     (parse_map (function (c,cs) -> Auxl.string_of_char_list (c::cs))
        (parse_pair
           (parse_satisfy (function c -> (c>='A' && c<= 'Z') || (c>='a' && c<= 'z')))
           (parse_star
              (parse_satisfy (function c -> 
                (c>='A' && c<= 'Z') || (c>='a' && c<= 'z') || (c>='0' && c<= '9') || c='\'' || c='_'))))))

let parse_Alphanum =
  (parse_nonalphanum_after
     (parse_map (function (c,cs) -> Auxl.string_of_char_list (c::cs))
        (parse_pair
           (parse_satisfy (function c -> c>='A' && c<= 'Z'))
           (parse_star
              (parse_satisfy (function c -> 
                (c>='A' && c<= 'Z') || (c>='a' && c<= 'z') || (c>='0' && c<= '9') || c='\'' || c='_'))))))

let concrete_parsers = 
  [ "alphanum0", parse_alphanum0 ;
    "alphanum", parse_alphanum ;
    "Alphanum", parse_Alphanum ;
    "numeral", parse_numeral ;
  ] 
(*   [ "[A-Z]+", parse_AZ ; *)
(*     "[a-z]+", parse_az ; *)
(*   ]  *)
    
let parse_dots_with_length_constraint length_constraint =
  let f ds = parse_map (function s -> String.length s - 2)
      (parse_choice
         (List.map (parse_string) ds)) in 
  match length_constraint with
  | None | Some 0 -> f ["..";"...";"...."]
  | Some 1 -> f ["...";"...."]
  | Some 2 -> f ["...."]
  | _ -> Auxl.error "internal: parse_dots with length_constraint > 2"

let parse_dots_without_length_constraint =
  let f ds = parse_map (function s -> String.length s - 2)
      (parse_choice
         (List.map (parse_string) ds)) in 
  f ["..";"...";"...."]

let parse_pre_whitespace 
   = fun p ->
      parse_map (function (_,x)->x)
        (parse_pair
           (parse_star
              (parse_satisfy Auxl.iswhitespace))
           (p))
        
let parse_lu_lowerbound = 
   (parse_choice [
   (parse_string_nonalphanum_after "0") ;
   (parse_string_nonalphanum_after "1") ]) 
   
let parse_lu_upperbound all_indexvar_synonyms 
   = (parse_maybe_fancy_suffix_var all_indexvar_synonyms)


(* ************************************************ *)
(* auxilary little parsers for grammar_typecheck    *)
(* ************************************************ *)

let one_parse p s = 
  (* try *)
    let cs = Auxl.char_list_of_string s in
    let ts = 
      let results = ref [] in 
      p (fun r1 r2 -> match r1 with [] -> results := r2::!results | _ -> ()) cs;
      !results in
    (match ts with
    | [t] -> OP_Some t
    | [] -> OP_None
    | ts -> OP_Many ts
    )
(*   with *)
(*     Parse_error s' -> None *)

let make_ident_lexer : metavarroot list -> metavarroot list -> nontermroot list 
  -> (string -> Lexing.position -> mytoken optionprime )
      = fun mvrs_nonindex mvrs_index ntrs_all ->
        let p = 
          parse_choice 
            [
             (parse_map (function  mvr -> Tok_metavar(dummy_loc,(mvr,[])))
                (parse_without_suffix mvrs_index));
             (parse_map (function  mvr,suff -> Tok_metavar(dummy_loc,(mvr,suff)))
                (parse_with_suffix mvrs_index mvrs_nonindex));
             (parse_map (function  ntr,suff -> Tok_nonterm(dummy_loc,(ntr,suff)))
                (parse_with_suffix mvrs_index ntrs_all));
             ] in
        fun s pos ->
          one_parse p s

let make_ident_lexer_of_syntaxdefn : syntaxdefn
  -> (string -> Lexing.position -> mytoken optionprime ) =
    function xd ->
      make_ident_lexer 
        (Auxl.all_nonindex_mvrs_defined_by_syntaxdefn xd) 
        (Auxl.all_index_mvrs_defined_by_syntaxdefn xd) 
        (Auxl.all_ntrs_defined_by_syntaxdefn xd) 
(*        (Auxl.terminals_of_syntaxdefn xd)  *)
      
let cd_env_of_syntaxdefn xd     =
  { ident_lexer = make_ident_lexer_of_syntaxdefn xd;
    primary_mvr_of_mvr = Auxl.primary_mvr_of_mvr xd;
    primary_ntr_of_ntr = Auxl.primary_ntr_of_ntr xd;
    all_indexvar_synonyms = Auxl.all_indexvar_synonyms xd
  }

          

(* ************************************************ *)
(* parser itself                                    *)
(* ************************************************ *)

(*
let make_parser : syntaxdefn -> old_made_parser = function xd -> 

(* Given a syntaxdefn we need to construct a collection of
mutually-recursive parsers, one for each rule. We do so by
indirecting via the rule names. Sadly, it seems we have to do so
imperatively.*)

(* scheme: at each point where we see an actual token, we allow *)
(* preceeding whitespace. The parsers should only be called on strings *)
(* satisfying the precondition that they have no trailing *)
(* whitespace. This scheme makes it easy to ensure that we don't get *)
(* ambiguity arising from alternative parsing of whitespace. *)

  let parsers_ref = ref ([]:parsers) in
  
  let lookup ntr = Auxl.debug ("lookup "^ntr); 
    p_debug ("lookup "^ntr^"  "); 
    lookup_depth := 1 + !lookup_depth; 
    if (!lookup_depth) >= 10000 then (print_string ("term_parser cycle suspected: depth "^string_of_int !lookup_depth^", "^ntr^"\n");flush stdout); 
    try List.assoc ntr (!parsers_ref) 
    with
      Not_found -> raise (Parse_error (dummy_loc, "Rule name `"^ntr^"' not found")) in

  let mvr_synonyms = Auxl.mvr_synonyms xd in
  let ntr_synonyms = Auxl.ntr_synonyms xd in
  let all_indexvar_synonyms = Auxl.all_indexvar_synonyms xd in
  let terminals = Auxl.terminals_of_syntaxdefn xd in

  let is_tm s = List.mem s terminals in

  let is_nt_or_mv_or_tm = 
    let ident_lexer = make_ident_lexer_of_syntaxdefn xd in
    fun s -> 
      ((is_tm s)
     ||
       match ident_lexer s Location.dummy_pos with
       | OP_Some _ | OP_Many _ -> true
       | OP_None -> false) in
  
  let lex_regexp_of_mvr : metavarroot -> string option (*Str.regexp*) = 
    let assoc = 
      List.map 
	(function mvd -> (mvd.mvd_name, 
			  try 
                            match (List.assoc "lex" mvd.mvd_rep) with
			    | Hom_string s::[] -> Some s 
			    | _ -> failwith "malformed lex specification" 
			  with Not_found -> None)) 
        xd.xd_mds in
    function mvrp -> List.assoc mvrp assoc in


  (* parsing elements *)
  
  let rec parse_element : bool -> nontermroot option -> element -> (char,symterm_element list) parser  
      = fun concrete parse_element_context e -> 
        match e with
        | Lang_nonterm (ntrp,nt) ->    
            let p' : (char,symterm) parser = 
                if concrete then 
                  (fun i ts -> (lookup (Auxl.fake_concrete_ntr_of_ntr ntrp) i ts)) 
                else 
                  (fun i ts -> (lookup ntrp) i ts) in
            let p'' :(char,symterm_element list) parser = 
                parse_map (fun st -> [ Ste_st(dummy_loc,st) ]) p' in
            p''
        | Lang_metavar (mvrp,mv) ->  
            if concrete then 
              let parse_concrete_thing = 
                try 
                  (match (lex_regexp_of_mvr mvrp) with
                  | None -> []
                  | Some r -> 
                      [parse_map 
                         (function var -> [Ste_var(dummy_loc,mvrp,var)])
                         (parse_option_map 
                            (function var -> 
                              if is_tm var
                              then None 
                              else Some var)
                            (List.assoc r concrete_parsers))])
                with
                  Not_found -> [] in
              (parse_pre_whitespace
                 (parse_choice parse_concrete_thing))
            else
              parse_pre_whitespace
                (parse_choice 
                   (
                    (match (lex_regexp_of_mvr mvrp) with
                    | None -> []
                    | Some r -> 
                        (try [
                          parse_map 
                            (function var -> [Ste_var(dummy_loc,mvrp,var)])
                            (parse_option_map 
                               (function var -> 
                                 if is_nt_or_mv_or_tm var
                                 then None 
                                 else Some var)
                               (List.assoc r concrete_parsers))
                        ] with
                          Not_found -> []))
                    @
                      [
                       let mvd=Auxl.mvd_of_mvr xd mvrp in
                       if mvd.mvd_indexvar then
                         (parse_map (function  mvr -> [Ste_metavar(dummy_loc,mvrp,(mvr,[]))])
                            (parse_without_suffix (List.map fst mvd.mvd_names)))
                       else
                         (parse_map (function  mvr,suff -> [Ste_metavar(dummy_loc,mvrp,(mvr,suff))])
                            (parse_with_suffix all_indexvar_synonyms (List.map fst mvd.mvd_names)))
                     ]) )
        | Lang_terminal t' -> 
            parse_pre_whitespace
              (parse_map (function s -> [])
                 (parse_string_nonalphanum_after t'))
              
        | Lang_list elb -> 
            
            let length_constraint = 
              (match elb.elb_boundo with
              | Some(Bound_dotform bd) -> Some bd.bd_length
              | Some(Bound_comp_lu bclu) -> Some bclu.bclu_length
              | _ -> None) in

            let p_es0 :(char,symterm_element list list)parser
                = parse_list (List.map (parse_element concrete parse_element_context) elb.elb_es) in
            let p_es :(char,symterm_element list)parser    
                = parse_map (List.concat) p_es0 in
                
            let p_tmopt : (char, unit) parser = match elb.elb_tmo with
            | None -> parse_nothing 
            | Some tm' -> 
                parse_pre_whitespace
                  (parse_map (function _ -> ())
                     (parse_string_nonalphanum_after tm')) in
                
            let p_dots : (char,int) parser = 
                parse_pre_whitespace
(*                  (parse_dots_without_length_constraint) in  *)
                   (parse_dots_with_length_constraint length_constraint) in  
            
            (* should calc a reasonable position *)
            let loc = dummy_loc in 

            (* a Bound_dotform form eg e1:t1,..,en:tn *)
            let p_dotform0 :(char,symterm_element list * (unit * (int * (unit * symterm_element list)))) parser 
                = parse_pair 
                  p_es 
                  (parse_pair 
                     p_tmopt 
                     (parse_pair 
                        p_dots 
                        (parse_pair p_tmopt p_es))) in
            let p_dotform :(char,symterm_list_item) parser 
                = parse_option_map (function
                    (es1,((),(n',((),es2)))) -> 
                      try
                        let (bo'',es'') = 
                          Merge.merge_symterm_element_list 0 (es1,es2) in
                        match bo'' with
                        | None ->
                            None  (* no index changed - so ill-formed *)
                        | Some (si1,si2) ->
                            let b = Bound_dotform {
                              bd_lower = si1;
                              bd_upper = si2;
                              bd_length = n';} in
                            let stlb = { stl_bound = b;
                                         stl_elements = es'';
                                         stl_loc = loc} in
                            Some (Stli_listform stlb)
                      with
                        Merge.Merge s -> None) 
                  p_dotform0 in

            (* auxiliaries for list comprehension forms *) 
            let parse_listform_token s = 
              parse_pre_whitespace
                (parse_map (function s->()) (parse_string s)) in
            
            let parse_indexvar = 
              parse_pre_whitespace
                (parse_without_suffix all_indexvar_synonyms) in
            
            (* a Bound_comp form, eg </ ei:ti // i /> *)
            let p_comp0 :(char,unit*(symterm_element list * (unit * (string * unit))))parser 
                = 
                (parse_pair 
                   (parse_listform_token Grammar_pp.pp_COMP_LEFT)
                   (parse_pair 
                      p_es
                      (parse_pair 
                         (parse_listform_token Grammar_pp.pp_COMP_MIDDLE)
                         (parse_pair
                            parse_indexvar
                            (parse_listform_token Grammar_pp.pp_COMP_RIGHT))))) in
            let p_comp :(char,symterm_list_item) parser 
                = parse_option_map (function
                    ((),(es,((),(ivr,())))) -> 
                      let es'' = 
                        List.map (Merge.abstract_indexvar_symterm_element ivr 0) es in
                      let b = Bound_comp {bc_variable=ivr} in
                      let stlb = { stl_bound = b;
                                   stl_elements = es'';
                                   stl_loc = loc} in
                      Some (Stli_listform stlb))
                  p_comp0 in

            (* a Bound_comp_u form, eg </ ei:ti // i IN n /> *)
            let p_comp_u0 :(char,unit*(symterm_element list * (unit * (string * (unit*(string*unit))))))parser 
                = 
                (parse_pair 
                   (parse_listform_token Grammar_pp.pp_COMP_LEFT)
                   (parse_pair 
                      p_es
                      (parse_pair 
                         (parse_listform_token Grammar_pp.pp_COMP_MIDDLE)
                         (parse_pair
                            parse_indexvar 
                            (parse_pair
                               (parse_listform_token Grammar_pp.pp_COMP_IN)
                               (parse_pair
                                  parse_indexvar
                                  (parse_listform_token Grammar_pp.pp_COMP_RIGHT))))))) in
            let p_comp_u :(char,symterm_list_item) parser 
                = parse_option_map (function
                    ((),(es,((),(ivr,((),(ivr',())))))) -> 
                      let es'' = 
                        List.map (Merge.abstract_indexvar_symterm_element ivr 0) es in
                      let b = Bound_comp_u {bcu_variable=ivr;bcu_upper=Si_var (ivr',0)} in
                      let stlb = { stl_bound = b;
                                   stl_elements = es'';
                                   stl_loc = loc} in
                      Some (Stli_listform stlb))
                  p_comp_u0 in

            (* a Bound_comp_lu form, eg </ ei:ti // i IN 1..n /> *)
            let p_comp_lu0 :(char,unit*(symterm_element list * (unit * (string * (unit*(string*(int*(suffix_item*unit))))))))parser
                =
                (parse_pair
                   (parse_listform_token Grammar_pp.pp_COMP_LEFT)
                   (parse_pair
                      p_es
                      (parse_pair
                         (parse_listform_token Grammar_pp.pp_COMP_MIDDLE)
                         (parse_pair
                            parse_indexvar
                            (parse_pair
                               (parse_listform_token Grammar_pp.pp_COMP_IN)
                               (parse_pair
                                  (parse_pre_whitespace parse_lu_lowerbound)
                                  (parse_pair
                                     p_dots
                                     (parse_pair
                                        (parse_pre_whitespace (parse_lu_upperbound all_indexvar_synonyms))
                                        (parse_listform_token Grammar_pp.pp_COMP_RIGHT))))))))) in
            let p_comp_lu :(char,symterm_list_item) parser
                = parse_option_map (function
                    ((),(es,((),(ivr,((),(lower,(dotlength,(si',())))))))) ->
                      let es'' =
                        List.map (Merge.abstract_indexvar_symterm_element ivr 0) es in
                      let b = Bound_comp_lu {bclu_variable=ivr;
                                             bclu_lower=Si_num lower;
                                             bclu_upper=si';
                                             bclu_length=dotlength} in
                      let stlb = { stl_bound = b;
                                   stl_elements = es'';
                                   stl_loc = loc} in
                      Some (Stli_listform stlb))
                  p_comp_lu0 in

            (* exactly one list form, either Bound_dotform, Bound_comp, etc *)
            let p_listform :(char, symterm_list_item) parser
                = (parse_choice [p_dotform;p_comp;p_comp_u;p_comp_lu]) in
            let p_listform' :(char, symterm_element list) parser
                = parse_map
                  (function stli -> [Ste_list(loc,[stli])]) 
                  p_listform in

            (* a concrete list entry, eg e:t  *)
            let p_concrete_entry :(char,symterm_list_item) parser
                = parse_map
                  (function es -> Stli_single (loc,es))
                  p_es in

            (* either a list form or a concrete list entry *)
            let p_listform_or_concrete_entry
                = parse_choice [p_listform;p_concrete_entry] in

            let enforce_length_constraint = 
              (function stlis ->
                if 
                  (match length_constraint with
                  | Some lc -> 
                      Auxl.min_length_of_stlis stlis >= lc
                  | None -> true )
                then
                  Some ([Ste_list (loc, stlis)])
                else
                  None) in

            let p_multiple =
              parse_option_map enforce_length_constraint
                (parse_choice 
                   [
                    (parse_map (function ()->[]) parse_nothing);
                    (parse_map (function x->[x]) p_listform_or_concrete_entry);
                    (parse_map (function (x,uys) -> x :: List.map snd uys)
                       (parse_pair
                          (p_listform_or_concrete_entry)
                          (parse_plus
                             (parse_pair
                                p_tmopt
                                p_listform_or_concrete_entry))));
                  ] )  in

            let p_multiple_for_self_loop =
              parse_option_map enforce_length_constraint
                (parse_choice 
                   [
                    (* (parse_map (function ()->[]) parse_nothing); *)
                    (parse_map (function x->[x]) p_listform (*_or_concrete_entry*));
                    (parse_map (function (x,uys) -> x :: List.map snd uys)
                       (parse_pair
                          (p_listform_or_concrete_entry)
                          (parse_plus
                             (parse_pair
                                p_tmopt
                                p_listform_or_concrete_entry))));
                  ] )  in

            let p_multiple_concrete =
              parse_option_map enforce_length_constraint
                (parse_choice 
                   [
                    (parse_map (function ()->[]) parse_nothing);
                    (parse_map (function x->[x]) p_concrete_entry);
                    (parse_map (function (x,uys) -> x :: List.map snd uys)
                       (parse_pair
                          (p_concrete_entry)
                          (parse_plus
                             (parse_pair
                                p_tmopt
                                p_concrete_entry))));
                  ] )  in

            let p_multiple_concrete_for_self_loop =
              parse_option_map enforce_length_constraint
                (parse_choice 
                   [
                    (* this restriction is a bit bizarre *)
                    (* (parse_map (function ()->[]) parse_nothing); *)
                    (* (parse_map (function x->[x]) p_concrete_entry); *)
                    (parse_map (function (x,uys) -> x :: List.map snd uys)
                       (parse_pair
                          (p_concrete_entry)
                          (parse_plus
                             (parse_pair
                                p_tmopt
                                p_concrete_entry))));
                  ] )  in

            let self_loop = 
              match parse_element_context with 
              | None -> false
              | Some ntr -> (match elb.elb_es with
                | [Lang_nonterm(ntr',nt')] -> ntr=ntr'
                | _ -> false) in

            let p_all :(char,symterm_element list) parser
                = match concrete,self_loop with
                | false,false -> p_multiple
                | false,true -> p_multiple_for_self_loop
                | true,false -> p_multiple_concrete
                | true,true -> p_multiple_concrete_for_self_loop
            in

            p_all
                
        | (Lang_option _ | Lang_sugaroption _ ) -> parse_fail  
        (* todo other stuff... *)
      in

  (* parsing a single production *)

  let make_production_parser : bool -> nontermroot -> prod -> (char,symterm) parser
      = fun concrete ntr p -> 
        Auxl.debug ("parse_production ["^ntr^"] "^p.prod_name^"\n");

        let leftassoc = List.mem_assoc "leftassoc" p.prod_homs in
        let rightassoc = List.mem_assoc "rightassoc" p.prod_homs in

        let parse_element_context = match p.prod_es with [e] -> Some ntr | _ -> None in

        let p' :(char,symterm_element list list)parser
            = parse_list 
              (List.map (parse_element concrete parse_element_context) 
                 p.prod_es) in
        let p'' :(char,symterm_element list)parser    
            = parse_map (List.concat) p' in
        let p''' :(char,symterm) parser               
            = parse_map 
              (fun stes -> 
                St_node ( dummy_loc, 
                          { st_rule_ntr_name = ntr;
                            st_prod_name = p.prod_name;
                            st_es = stes;
                            st_loc = dummy_loc}) )
              p'' in
(*         let p_annot : (char,unit) parser  *)
(*             = parse_choice *)
(*               [ parse_single (function  *)
(*                   | Tok_terminal(l,t)  *)
(*                     when t=Auxl.psuedo_terminal_of_prod_name p.prod_name  *)
(*                     -> [ () ]  *)
(*                   | _ -> []); *)
(*                 parse_nothing *)
(*               ] in *)
(*         parse_map (function ((),x)->x) (parse_pair p_annot p''') in *)
        
        if concrete then p'''
        else 
          parse_choice
            [
             (parse_map (function (_,x)->x)
                (parse_pair
                   (parse_pre_whitespace
                      (parse_string (Auxl.psuedo_terminal_of_prod_name p.prod_name )))
                   p'''));
             p'''] in

  
  (* parsers for the symbolic nonterms associated with a rule *)

  let parsers_for_symbolic_nonterm : nontermroot -> (char,symterm) parser list
        = function ntrp ->
          Auxl.debug ("foo: "^ntrp^"\n");
          [(parse_map (function  ntr,suff -> St_nonterm(dummy_loc,ntrp,(ntr,suff)))
             (parse_pre_whitespace
                (parse_with_suffix all_indexvar_synonyms (ntr_synonyms ntrp))))] in



  (* parsers for the symbolic nonterms for proper subrules of a rule *)

  let parsers_for_symbolic_nonterm_sub : nontermroot -> (char,symterm) parser list
        = function ntrp->
          List.map
            (function ntrpl ->
              (parse_map (function  ntr,suff -> St_nontermsub(dummy_loc,ntrpl,Auxl.promote_ntr xd ntrp,(ntr,suff)))
                 (parse_pre_whitespace
                    (parse_with_suffix all_indexvar_synonyms (ntr_synonyms ntrpl)))))
            (Auxl.ntr_proper_subs xd ntrp) in


  (* build a parser from a rule, paired with its rule name  *)
  
  let make_rule_parser : bool -> rule -> (nontermroot * (char,symterm) parser)
      = fun concrete r -> 
        (* allow either a proper subterm *)
        let ps1=(List.map(make_production_parser concrete r.rule_ntr_name) 
                   (*(if concrete then (List.filter (fun p -> not p.prod_meta) r.rule_ps)
                   else r.rule_ps)*) r.rule_ps) in
        (* or a symbolic nonterminal *)
        let ps2 = parsers_for_symbolic_nonterm r.rule_ntr_name in 
        (* or a symbolic nonterminal of a proper subgrammar*)
        let ps3 = parsers_for_symbolic_nonterm_sub r.rule_ntr_name in  
        (* or a concrete subterm *)
        let ps4 = 
          if r.rule_meta then []
          else
            [(parse_map snd
                (parse_pair
                   (parse_pre_whitespace
                      (parse_string Auxl.parse_as_concrete ))
(*                    (fun i ts -> failwith (Auxl.parse_as_concrete^" not supported")) *)

(* parse_fail *)

                    (fun i ts -> (lookup (Auxl.fake_concrete_ntr_of_ntr r.rule_ntr_name) i ts))                    

(*                    (let concrete=true in *)
(*                    (parse_choice *)
(*                       (List.map(make_production_parser concrete r.rule_ntr_name)  *)
(*                          (if concrete then (List.filter (fun p -> not p.prod_meta) r.rule_ps) *)
(*                          else r.rule_ps)))) *)



                ))] in
        if concrete then 
          (Auxl.fake_concrete_ntr_of_ntr r.rule_ntr_name,memo (parse_choice ps1)) 
        else 
          (r.rule_ntr_name,memo (parse_choice (ps1 @ ps2 @ ps3 @ ps4))) in


  (* build all the parsers for a syntaxdefn *)
  
  let make_syntaxdefn_parsers : syntaxdefn -> (nontermroot * (char,symterm) parser) list 
      = fun xd -> 
        List.map (make_rule_parser false) xd.xd_rs 
        @ List.map (make_rule_parser true) (List.filter (fun r -> not r.rule_meta) xd.xd_rs) in
  
  (* tie the recursive knot *)
  
  let init_parsers : syntaxdefn -> unit 
      = fun xd ->
        parsers_ref := make_syntaxdefn_parsers xd
        (* ; print_string (String.concat "\n" (List.map fst (!parsers_ref)));exit 0 *)
            
  in 
  
  (init_parsers xd; lookup)
*)


(*----------------------------------------------------------------------------*)
(** {2 Parser transformations} *)
(*----------------------------------------------------------------------------*)

type parser_transform = symterm list -> symterm list

(** Default argument to [just_one_parse]:
  For user_syntax, give metavar parses precedence over everything else,
  otherwise picky-multiple-parses does the wrong thing e.g. if we have a metavar
  x and a term x in a fancy formula.
 *)
let user_syntax_transform : parser_transform =
  let is_user_syntax_metavar st =  
    (match st with 
    | St_node(_,stnb) when stnb.st_rule_ntr_name="user_syntax" -> 
        (match stnb.st_es with 
        | [Ste_metavar(_,_,_)] -> true 
        | _ -> false)
    | _ -> false) in
  fun sts ->
    match List.filter is_user_syntax_metavar sts with
    | [] -> sts
    | sts -> sts

(** Transformer that ignores definitions other than [prod_name] *)
let defn_transform prod_name : parser_transform =
  let is_defn_formula st =  
    (match st with 
    | St_node(_,stnb) when stnb.st_prod_name="formula_judgement" -> 
        (match stnb.st_es with 
        | [Ste_st(_,St_node(_,stnb'))] ->
            (match stnb'.st_es with
            | [Ste_st(_,St_node(_,stnb''))] -> stnb''.st_prod_name = prod_name 
            | _ -> false)
        | _ -> false)
    | _ -> false) in
  List.filter is_defn_formula
 
let default_transform : parser_transform = user_syntax_transform

(*----------------------------------------------------------------------------*)
(** {2 Drivers for the parser} *)
(*----------------------------------------------------------------------------*)

let strip_trailing_whitespace s = 
  let l = String.length s in
  let last_non_whitespace = 
    let rec f i = 
      if i < 0 then -1
      else if Auxl.iswhitespace s.[i] then f (i-1)
      else i in 
    f (l-1) in
  String.sub s 0 (1+last_non_whitespace)

(* parse a token list to give all the possible parses *)
(*
let parse : ( nontermroot -> (char,symterm) parser ) -> nontermroot -> char list -> (symterm * char list) list
    = fun lookup ntr cs ->
      reset_furthest_pos cs;
      let results = ref [] in
        (lookup ntr) (fun r1 r2 -> results := (r2, r1)::!results) cs;
        !results
*)

(** parse a token list to give all the possible complete parses, i.e. those
with no remaining tokens *)

let parse_complete (lookup : made_parser) (ntr: nontermroot) (concrete: bool)
  (s: string) : symterm list =
  furthest_pos := 0;
  lookup ntr concrete (strip_trailing_whitespace s)

(* To avoid one common source of multiple parses, if there are
multiple parses and the global option is_picky is set to false, we
check if all the parsed symterms pp to identical strings for all the
current target modes.  If it is the case, just one parses not complain
about multiple parses *)

let just_one_parse ?(transform : symterm list -> symterm list = user_syntax_transform)
      (xd: syntaxdefn) (lookup: made_parser) 
      (ntr: nontermroot) (concrete: bool) (l: loc) (s: string): symterm =
  let sts = parse_complete lookup ntr concrete s in
  let sts = transform sts in
  match sts with
    [st] -> st
  | [] -> 
      let error_str = no_parses_error_string s in
      Format.printf "\nno parses of \"%s\" at %s:\n%s\n" s (Location.pp_loc l) error_str;
      St_uninterpreted (l, error_str)
  | hs::ts ->
      if 
        match !Global_option.is_picky with
        | (true,_) -> false
        | (false,pp_list) ->
            List.for_all (fun pp_mode ->
              let s = Grammar_pp.pp_symterm pp_mode xd [] de_empty hs in
              List.for_all (fun st -> s = (Grammar_pp.pp_symterm pp_mode xd [] de_empty st)) ts)
              pp_list
      then hs
      else begin
        Format.printf "\nmultiple parses of \"%s\" at %s:\n" s  (Location.pp_loc l);
        List.iter 
          (fun st -> 
            Format.printf "%s\n or plain:%s\n"
              (Grammar_pp.pp_symterm pp_ascii_opts_default xd [] de_empty st)
              (Grammar_pp.pp_plain_symterm st))  
          sts;
        St_uninterpreted(l, "multiple parses")
      end

(*----------------------------------------------------------------------------*)
(** {2 Make parser} *)
(*----------------------------------------------------------------------------*)

module Ntp = New_term_parser ;;

let make_parser xd : made_parser =
  let module Gram = 
    struct
      module GramTypes = Ntp.GramTypes;;
      let (grammar, follow_restrictions, priorities, starts, mknt) = 
        Ntp.build_grammar xd;;
      let permit_cyclic = true;;
      let debug = false;;
    end
  in
  let module Pt = Parse_table.Make (Gram) in
  let module Pt2 = 
    struct 
      include Pt
      exception Reject_parse = New_term_parser.Reject_parse;;
      exception Reject_all_parses = New_term_parser.Reject_all_parses;;
      let debug = false
    end 
  in
  let module P = Glr.Make (Pt2) in

  let new_parser ntr concrete s =
    let index = ref 0 in
    let len = String.length s in
    let get_next () =
      if !index >= len then
        Ntp.Gtp.Terminal.eof
      else
        let c = String.get s !index in
          incr index;
          incr furthest_pos;
          c
    in
    let start = Gram.mknt (Ntp.Nt.Orig_nt (ntr, concrete)) in
      (try ignore (Pt.NTmap.find start Pt.start_table)
       with Not_found ->
         parse_error2 [] () ("Attempt to parse from non-existent nonterminal: " ^ Gram.GramTypes.Nonterminal.to_string start));
      let pt = P.parse start get_next in
        match pt with
            None -> []
          | Some tree -> 
              let res = P.process_parse_tree tree in
                List.map (fun (Ntp.Gtp.Res_st s) -> s) res
  in
  new_parser;;

(*----------------------------------------------------------------------------*)
(** {2 Test harness} *)
(*----------------------------------------------------------------------------*)

let test_parse (m: pp_mode) (xd: syntaxdefn) (ntr: nontermroot)
     (concrete: bool) (s: string): unit = 
  print_string ("Test of:  \""^s^"\"\n"); 
  let lookup = make_parser xd in
  print_string ("Parsing:\n");flush stdout;
  let sts = parse_complete lookup ntr concrete s in
  match sts with 
  | [] -> print_string (no_parses_error_string s ^"\n")
  | _ ->  print_string (
        (String.concat "\n" (List.map (Grammar_pp.pp_symterm m xd [] de_empty) sts)^"\n")
       ^ (String.concat "\n" (List.map (Grammar_pp.pp_plain_symterm) sts)^"\n"))

