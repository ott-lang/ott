(**************************************************************************)
(*                               parse_table                              *)
(*                                                                        *)
(*        Scott Owens, Computer Laboratory, University of Cambridge       *)
(*                                                                        *)
(*  Copyright 2007                                                        *)
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

(* This is a GLR parser based on the reduction worklist algorithm of Scott
 * McPeak (Univ. California Berkeley, tech. report 2-1214, 2002), but building
 * the parse tree structure described in the first chapter of Jan Rekers' PhD
 * thesis ("Parser Generation for Interactive Environments", University of
 * Amsterdam, 1992).  It incorporates the priority and single character follow
 * restriction schemes from the third chapter of Eelco Visser PhD thesis
 * ("Syntax Definition for Language Prototyping", University of Amsterdam,
 * 1997).
 *
 * It does not do the extra parse tree sharing from chapter 1.5 of Rekers, and
 * it does not do the multi-character follow restriction or reject productions
 * from Visser.  It is LR(0) based, and not SLR(1) or LALR based. *)

(* Todo : Investigate some of the performance improvements from the Elkhound
 * tech. report. *)

module OrderedInt = 
struct
  type t = int
  let compare i1 i2 = i1 - i2
end

module OrderedIntPair = 
struct
  type t = int * int
  let compare (i1, j1) (i2, j2) =
    let res = i1 - i2 in
      if res = 0 then
        j1 - j2
      else
        res
end

module IntMap = Map.Make (OrderedInt)
module IntPairMap = Map.Make (OrderedIntPair)
 
module type IntMapKeySig =
sig
  type t
  val get_int : t -> int
end;;

module type IIntMapSig = 
sig
  type key
  type 'a t
  val empty : int -> 'a t
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val iter : (key -> 'a -> unit) -> 'a t -> unit
end;;

(*
module ImperativeIntMap (K : IntMapKeySig) : IIntMapSig with type key = K.t = 
  struct
    type 'a e = None | Some of K.t * 'a
    type 'a t = ('a e array * int list ref);;
    type key = K.t

    let empty size = (Array.make size None, ref []);;

    let mem k (m, _) = 
      match m.(K.get_int k) with
          None -> false
        | _ -> true;;

    let add k x ((m, keys) as t) = 
      let i = K.get_int k in
        begin
          match m.(i) with
              None -> keys := i::!keys; 
            | Some _ -> ()
        end;
        m.(i) <- Some (k, x);
        t;;

    let find k (m, keys) =
      match m.(K.get_int k) with
          None -> raise Not_found
        | Some (k, v) -> v;;


    let fold f (m, keys) res =
      List.fold_left 
        (fun res k -> 
           match m.(k) with
               None -> assert false
             | Some (k, v) -> f k v res)
        res
        !keys;;

    let iter f (m, keys) =
      List.iter
        (fun k -> 
           match m.(k) with
               None -> assert false
             | Some (k, v) -> f k v)
        !keys;;
end;;
 *)

module ImperativeIntMap (K : IntMapKeySig) : IIntMapSig with type key = K.t = 
  struct
    module H = Hashtbl.Make (struct type t = K.t;; let equal k1 k2 = K.get_int k1 = K.get_int k2;; let hash k = Hashtbl.hash (K.get_int k);; end);;
    type 'a t = 'a H.t;;
    type key = K.t;;

    let empty size = H.create 50

    let mem k t = H.mem t k

    let add k x t = 
      H.remove t k;
      H.add t k x;
      t;;

    let find k t = H.find t k

    let fold f t res = H.fold f t res

    let iter f t = H.iter f t;;
end;;

module type TermType =
sig
  include Set.OrderedType
  val eof : t
  val is_eof : t -> bool
  val to_string : t -> string
  val to_int : t -> int
end;;

module type NontermType =
sig
  include Set.OrderedType
  val to_string : t -> string
end;;


module type GRAM_TYPES_PARAMS = 
sig
  module Nonterminal : NontermType
  module Terminal : TermType
  type result
  val signal_error : string -> unit
end;; 

module type GRAM_TYPES = 
sig
  include GRAM_TYPES_PARAMS

  type grammar_symbol =
      NT of Nonterminal.t
    | T of Terminal.t
  type production = 
      {prod_left : Nonterminal.t; 
       prod_right : grammar_symbol list;
       prod_action : result list -> result;
       reject : bool;
       transparent : bool;
       index : int}
  type follow =
      Multi of (Terminal.t list -> bool)
    | Single of (Terminal.t -> bool)
  type grammar = production list
  type priority = 
      Greater of int * int
    | Left of int * int
    | Right of int * int
    | Nonassoc of int * int
end;;

module MakeTypes (Gtp : GRAM_TYPES_PARAMS) : GRAM_TYPES 
with module Nonterminal = Gtp.Nonterminal and
module Terminal = Gtp.Terminal and
type result = Gtp.result 
                =
struct
  include Gtp

  type grammar_symbol =
      NT of Nonterminal.t
    | T of Terminal.t
  type production = 
      {prod_left : Nonterminal.t; 
       prod_right : grammar_symbol list;
       prod_action : result list -> result;
       reject : bool;
       transparent : bool;
       index : int}
  type follow =
      Multi of (Terminal.t list -> bool)
    | Single of (Terminal.t -> bool)
  (* Each production in grammar must have a distinct index*)
  type grammar = production list
  type priority = 
      Greater of int * int
    | Left of int * int
    | Right of int * int
    | Nonassoc of int * int
end;;

module type GRAM = 
sig 
  module GramTypes : GRAM_TYPES
  open GramTypes

  val grammar : grammar
  val follow_restrictions : (Nonterminal.t * follow) list
  val starts : Nonterminal.t list
  val priorities : priority list
  val permit_cyclic : bool
  val debug : bool
end;;

module type S =
sig
  module Nonterminal : NontermType
  module Terminal : TermType
  module NTmap : Map.S with type key = Nonterminal.t
  module Tmap : Map.S with type key = Terminal.t
  type result
  type state = int
  type reduce_record = 
      {reduce_left : Nonterminal.t; 
       reduce_action : result list -> result;
       reduce_reject : bool;
       reduce_index : state;
       reduce_length : int;
       reduce_transparent : bool;
       reduce_label : string}
  type action_entry = {shift : state option; 
                       reduce : reduce_record list;
                       accept : Nonterminal.t list}
  val action_table : action_entry array Tmap.t
  val eof_table : action_entry array
  val goto_table : (state, state) Hashtbl.t array
  val start_table : state NTmap.t
  val nt_ordering : int NTmap.t
  val priority : (bool*bool*bool*bool) IntPairMap.t
end;;

module Make (Gram : GRAM) : S with 
module Nonterminal = Gram.GramTypes.Nonterminal and
module Terminal = Gram.GramTypes.Terminal and
type result = Gram.GramTypes.result =
struct
  open Gram
  open GramTypes

  module Nonterminal = Nonterminal
  module Terminal = Terminal
  type result = GramTypes.result
  type state = int
  type reduce_record = 
      {reduce_left : Nonterminal.t; 
       reduce_action : result list -> result;
       reduce_reject : bool;
       reduce_index : state;
       reduce_length : int;
       reduce_transparent : bool;
       reduce_label : string}
  type action_entry = {shift : state option; 
                       reduce : reduce_record list;
                       accept : Nonterminal.t list}

  module G = Graph.Pack.Digraph

  let rec nonterms_to_string (ntrs : Nonterminal.t list) : string = 
    match ntrs with
      [] -> ""
    | [ntr] -> Nonterminal.to_string ntr
    | [ntr1; ntr2] ->
        Nonterminal.to_string ntr1 ^ " and " ^ Nonterminal.to_string ntr2
    | ntr::ntrs -> Nonterminal.to_string ntr ^ ", " ^ nonterms_to_string ntrs;;

  let gram_sym_to_string gs = 
    match gs with
      NT nt -> Nonterminal.to_string nt
    | T t -> Terminal.to_string t;;

  let rec gram_syms_to_string (gs : grammar_symbol list) : string =
    match gs with
      [] -> ""
    | [gs] -> gram_sym_to_string gs
    | gs::rest -> gram_sym_to_string gs ^ " " ^ gram_syms_to_string rest;;

  module OrderedProd =
  struct
    type t = production
    let compare p1 p2 = p1.index - p2.index
  end

  module NTset = Set.Make (Nonterminal)
  module NTmap = Map.Make (Nonterminal)
  module Tset = Set.Make (Terminal)
  module Tmap = Map.Make (Terminal)

  module ProdSet = Set.Make (OrderedProd)
  module ProdMap = Map.Make (OrderedProd)
  module IProdMap = ImperativeIntMap (struct type t = production;; let get_int p = p.index end);; 

  let int_map_to_array m max_key default =
    let res = Array.make max_key (default ()) in
      for i = 0 to Array.length res - 1 do
        res.(i) <- default ()
      done;
      IntMap.iter (fun k v -> Array.set res k v) m;
      res;;

  let t_map_to_array m max_key default =
    let res = Array.make max_key (default ()) in
      for i = 0 to Array.length res - 1 do
        res.(i) <- default ()
      done;
      Tmap.iter (fun k v -> Array.set res (Terminal.to_int k) v) m;
      res;;


  (* The before_dot part of an item is kept in reverse order *)
  type item = 
      {before_dot : grammar_symbol list;
       before_dot_length : int;
       after_dot : grammar_symbol list;
       initial : bool;
       prod : production}

  let compare_item i1 i2 =
    let c0 = i1.prod.index - i2.prod.index in
      if c0 = 0 then
        begin
          let c1 = i1.before_dot_length - i2.before_dot_length in
            if c1 = 0 then
              Obj.magic i1.initial - Obj.magic i2.initial (* WAS compare i1.initial i2.initial *)
            else
              c1
        end
      else
        c0;;

  module OrderedItem = 
  struct
    type t = item
    let compare x y = compare_item x y
  end;;

  module ItemSet = Set.Make (OrderedItem)
  module ItemMap = Map.Make (OrderedItem)

  let rec get_rhs_syms (gsl : grammar_symbol list) : (Tset.t * NTset.t) = 
    match gsl with
        [] -> (Tset.empty, NTset.empty)
      | (x :: gsl) -> 
          let (ts, nts) = get_rhs_syms gsl in
            match x with
                NT nt -> (ts, NTset.add nt nts)
              | T t -> (Tset.add t ts, nts);;

  let rec get_all_rhs_syms (g : grammar) : (Tset.t * NTset.t) =
    match g with
      [] -> (Tset.empty, NTset.empty)
    | (p :: g) -> 
      let (ts, nts) = get_all_rhs_syms g in
      let (ts_, nts_) = get_rhs_syms p.prod_right in
        (Tset.union ts_ ts, NTset.union nts_ nts);;

  let rec get_lhs_nts (g : grammar) : NTset.t = 
    match g with
      [] -> NTset.empty
    | (p :: g) -> NTset.add p.prod_left (get_lhs_nts g);;

  (* Figure out the largest production index for when we need to make up new
   * productions later on. *)
  let prod_count = ref 0;;

  List.iter 
    (fun prod -> prod_count := max !prod_count prod.index)
    grammar;;


  let ((all_nts : NTset.t), (defed_nts : NTset.t), (all_ts : Tset.t)) =
    let (used_ts, used_nts) = get_all_rhs_syms grammar in
    let defed_nts = get_lhs_nts grammar in
      (*
    (if not (NTset.subset used_nts defed_nts) then
       signal_error ("The following non-terminals are used but not defined: " ^
                     nonterms_to_string 
                       (NTset.elements (NTset.diff used_nts defed_nts))));
       *)
    (NTset.union defed_nts used_nts, defed_nts, used_ts);;

  (* Group the productions by their nonterminals *)
  let (prod_map : production list NTmap.t) =
    let add_to_nt_map m p =
      NTmap.add p.prod_left (p::NTmap.find p.prod_left m) m
    in
      List.fold_left 
        add_to_nt_map 
        (NTset.fold (fun nt m -> NTmap.add nt [] m) all_nts NTmap.empty)
        grammar;; 

  let gs_to_nt (gs : grammar_symbol) : Nonterminal.t =
    match gs with (NT nt) -> nt | (T _) -> assert false;;

  (* Get the productions that have no terminals on the rhs *)
  let (term_free_prods : (Nonterminal.t * NTset.t) list) =
    let has_no_term gs = match gs with (NT _) -> true | (T _) -> false in
    List.fold_left 
      (fun l p -> 
         if List.for_all has_no_term p.prod_right then
            (p.prod_left,
             List.fold_left (fun s gs -> NTset.add (gs_to_nt gs) s) 
                            NTset.empty
                            p.prod_right)::
            l 
         else
            l)
      []
      grammar;;

  (* The nonterminals that can derive empty strings *)
  let (nullable : NTset.t) =
    let rec find_nulls (prods : (Nonterminal.t * NTset.t) list) : NTset.t =
      match prods with
        [] -> NTset.empty
      | (nt, s)::rest ->
          if NTset.is_empty s then
            NTset.add nt (find_nulls rest)
          else
            (find_nulls rest)
    in
    let rec apply_nulls (prods : (Nonterminal.t * NTset.t) list)
          (nulls : NTset.t)
          : (Nonterminal.t * NTset.t) list =
      match prods with
          [] -> []
        | (nt, s)::rest ->
            if NTset.mem nt nulls then
              apply_nulls rest nulls
            else
              (nt, NTset.diff s nulls)::apply_nulls rest nulls
    in
    let rec iter_nulls prods nulls =  
      let new_nulls = find_nulls prods in
        if NTset.is_empty new_nulls then
          nulls
        else
          iter_nulls 
            (apply_nulls prods new_nulls) 
            (NTset.union new_nulls nulls)
    in
      iter_nulls term_free_prods NTset.empty;;

  (* Assign unique indices to the nonterminals *)
  let (nt_to_int, int_to_nt) =
    let rec compute_mapping count nts =
      match nts with
          [] -> (NTmap.empty, IntMap.empty)
        | (nt::rest) ->
            let (nt2i, i2nt) = compute_mapping (count+1) rest in
              (NTmap.add nt count nt2i, IntMap.add count nt i2nt)
    in
      compute_mapping 0 (NTset.elements all_nts);;

  (* The GLR parser can handle cyclic grammars, which give rise to parse trees
   * with cycles in them, but you may want to rule them out anyway with
   * permit_cyclic.  *)
  let nt_ordering : int NTmap.t =
    let gr = G.create() in
    let nt_to_vertex =
      NTset.fold (fun nt m -> 
                    let v = G.V.create (NTmap.find nt nt_to_int) in
                    G.add_vertex gr v;
                    NTmap.add nt v m)
                 all_nts NTmap.empty
    in
    let add_edges (from : Nonterminal.t) (tos : Nonterminal.t list) =
      List.iter (fun ntr ->
                   (if (not permit_cyclic) && 
                       (Nonterminal.compare from ntr = 0) then
                      signal_error ("non-terminal " ^ 
                                    Nonterminal.to_string from ^ 
                                    " can derive itself without consuming input."));
                   G.add_edge gr (NTmap.find from nt_to_vertex)
                                 (NTmap.find ntr nt_to_vertex))
                tos
    in 
    let add_edges_for_prod (l, r) : unit = 
      let (nulls, others) = 
        List.partition (fun nt -> NTset.mem nt nullable) 
                       (NTset.elements r) in
      match others with
        [] -> add_edges l nulls
      | [other] -> add_edges l others
      | _ -> ()
    in
    List.iter add_edges_for_prod term_free_prods;
    let (scc_vertex_sets : G.V.t list array) = G.Components.scc_array gr in
    let count = ref 0 in
    let add (nt_idx : G.V.t) (map : int NTmap.t) =
      NTmap.add (IntMap.find (G.V.label nt_idx) int_to_nt) !count map
    in
      Array.fold_right
        (fun (comp : G.V.t list) (map : int NTmap.t) ->
           let res = 
             match comp with
                 [] -> map
               | [v] -> add v map
               | vs -> 
                   if not permit_cyclic then
                     begin
                       signal_error (
                         "There is a non-productive cycle among the following non-terminals: " ^
                         nonterms_to_string 
                           (List.map 
                              (fun v -> IntMap.find (G.V.label v) int_to_nt)
                              vs));
                       assert false
                     end
                   else
                     List.fold_right add vs map
           in
             incr count;
             res)
        scc_vertex_sets
        NTmap.empty;;

  (* For each nonterminal, which terminals cannot follow it *)
  let (single_follow_restrs : (Terminal.t -> bool) list NTmap.t) =
    List.fold_left
      (fun m (nt, f_rest) ->
         match f_rest with
             Single f ->
               begin
                 try
                   NTmap.add nt (f :: NTmap.find nt m) m
                 with Not_found ->
                   NTmap.add nt [f] m
               end
           |  Multi _ ->
               signal_error 
                 "Multi-terminal follow restrictions are currently unsupported.";
               m)
      NTmap.empty
      follow_restrictions;;


  let add_prior_rec ipm k g l r n =
    try 
      let (g1,l1,r1,n1) = IntPairMap.find k ipm in
        IntPairMap.add k (g||g1,l||l1,r||r1,n||n1) ipm
    with Not_found ->
      IntPairMap.add k (g,l,r,n) ipm;;

  let (priority : (bool*bool*bool*bool) IntPairMap.t) =
    List.fold_left
      (fun ipm ->
         function
             Greater (i1, i2) -> 
               add_prior_rec ipm (i1, i2) true false false false
           | Left (i1, i2) ->
               add_prior_rec ipm (i2, i1) false true false false
           | Right (i1, i2) ->
               add_prior_rec ipm (i2, i1) false false true false
           | Nonassoc (i1, i2) ->
               add_prior_rec ipm (i2, i1) false false false true)
      IntPairMap.empty
      priorities;;

  (* Priority conflicts, assuming that the grammar symbol following the dot 
   * is the nonterminal for p *)
  let conflict (i : item) (p : production) : bool = 
    if IntPairMap.mem (i.prod.index, p.index) priority then
      begin
        let (g,l,r,n) = IntPairMap.find (i.prod.index, p.index) priority in
          g || 
          ((r || n) && 
           i.before_dot = [] && 
           not (List.tl i.after_dot = [])) ||
          ((l || n) && 
           List.tl i.after_dot = [] &&
           not (i.before_dot = []))
      end
    else
      false

  let prod_to_item (p : production) : item =
    {before_dot = [];
     before_dot_length = 0;
     after_dot = p.prod_right;
     initial = false;
     prod = p};;

  module Gcycle =
  struct
    type t = production list * production list NTmap.t
    module V =
    struct
      type t = production
      let compare p1 p2 = p1.index - p2.index
      let equal p1 p2 = p1.index = p2.index
      let hash p = p.index
    end
    let sucs g v =
      match v.prod_right with
          NT nt :: _ ->
            let i = prod_to_item v in
              List.filter
                (fun prod -> not (conflict i prod))
                (NTmap.find nt g)
        | _ -> []
    let iter_succ f g v =
      List.iter f (sucs (snd g) v)
    let iter_vertex f g = List.iter f (fst g) 
  end;;
  module C = Graph.Components.Make(Gcycle);;

  let closure_cache = ref ItemMap.empty;;

  let closure_scc = C.scc_array (grammar, prod_map);;
  for i = 0 to Array.length closure_scc - 1 do
    let children_set = 
      List.fold_left 
        (fun is p ->
           List.fold_left
             (fun is p ->
                try
                  ItemSet.union 
                    (ItemMap.find (prod_to_item p) !closure_cache)
                    is
                with Not_found -> is)
             is
             (Gcycle.sucs prod_map p))
        ItemSet.empty
        closure_scc.(i)
    in
    let items = List.map prod_to_item closure_scc.(i) in
    let new_is = 
      List.fold_left
        (fun is i -> ItemSet.add i is)
        children_set
        items
    in
      List.iter 
        (fun i ->
           closure_cache := ItemMap.add i new_is !closure_cache)
        items
  done;;

  let closure_helper (nt : Nonterminal.t) (i : item) =
    let (children_closure : ItemSet.t) =
      List.fold_left 
        (fun (is : ItemSet.t) (p : production) ->
           if not (conflict i p) then
             ItemSet.union 
               (ItemMap.find (prod_to_item p) !closure_cache)
               is
           else
             is)
        ItemSet.empty
        (NTmap.find nt prod_map)
    in
    let closure = ItemSet.add i children_closure in
      closure_cache := ItemMap.add i closure !closure_cache;
      closure;;

  let closure (is : ItemSet.t) : ItemSet.t = 
    ItemSet.fold
      (fun item result -> 
         match item.after_dot with
             NT nt :: _ -> 
               begin
                 try 
                   ItemSet.union (ItemMap.find item !closure_cache) result
                 with Not_found ->
                   ItemSet.union (closure_helper nt item) result
               end
           | _ -> ItemSet.add item result)
      is
      ItemSet.empty;;




  (*
  let move_dot (i : item) ((nt_items : ItemSet.t NTmap.t), 
                           (t_items : ItemSet.t Tmap.t))
        : (ItemSet.t NTmap.t * ItemSet.t Tmap.t) =
    let add_to_t_map m k v = 
      try Tmap.add k (ItemSet.add v (Tmap.find k m)) m
      with Not_found -> Tmap.add k (ItemSet.singleton v) m
    in
    let add_to_nt_map m k v = 
      try NTmap.add k (ItemSet.add v (NTmap.find k m)) m
      with Not_found -> NTmap.add k (ItemSet.singleton v) m
    in
      match i.after_dot with
          [] -> (nt_items, t_items)
        | (gs::tl) -> 
            let new_item = 
              {i with before_dot = gs::i.before_dot; 
                      before_dot_length = i.before_dot_length + 1;
                      after_dot = tl}
            in
              match gs with
                  T t -> (nt_items, add_to_t_map t_items t new_item)
                | NT nt -> (add_to_nt_map nt_items nt new_item, t_items);; 
   *)

  (* Moving the dot over nonterminals by each individual production
   * of that nonterminal significantly slows down automaton generation. *)
  let move_dot (i : item) ((prod_items : ItemSet.t ProdMap.t), 
                           (t_items : ItemSet.t Tmap.t))
        : (ItemSet.t ProdMap.t * ItemSet.t Tmap.t) =
    let add_to_t_map m k v = 
      try Tmap.add k (ItemSet.add v (Tmap.find k m)) m
      with Not_found -> Tmap.add k (ItemSet.singleton v) m
    in
    let add_to_prod_map m k v = 
      if ProdMap.mem k m then
        ProdMap.add k (ItemSet.add v (ProdMap.find k m)) m
      else
        ProdMap.add k (ItemSet.singleton v) m
    in
      match i.after_dot with
          [] -> (prod_items, t_items)
        | (gs::tl) -> 
            let new_item = 
              {i with before_dot = gs::i.before_dot; 
                      before_dot_length = i.before_dot_length + 1;
                      after_dot = tl}
            in
              match gs with
                  T t -> (prod_items, add_to_t_map t_items t new_item)
                | NT nt -> 
                    let new_prod_items =
                      List.fold_left 
                        (fun m p -> 
                           if conflict i p then
                             m
                           else
                             add_to_prod_map m p new_item)
                        prod_items
                        (NTmap.find nt prod_map)
                    in
                      (new_prod_items, t_items);; 

  let goto_all (is : ItemSet.t) : (ItemSet.t ProdMap.t * ItemSet.t Tmap.t) =
    ItemSet.fold move_dot is (ProdMap.empty (*!prod_count*), Tmap.empty);; 

  module ItemList = 
  struct
    type t = item list
    let rec compare l1 l2 =
      match (l1, l2) with
          ([], []) -> 0
        | (x::y, []) -> 1
        | ([], x::y) -> -1
        | (x1::y1, x2::y2) -> 
            let c = compare_item x1 x2 in
              if c = 0 then
                compare y1 y2
              else
                c
  end;;

  module ItemSetMap = Map.Make (ItemSet)
  module ItemListMap = Map.Make (ItemList)


  type action_table = action_entry Tmap.t IntMap.t 
  type eof_table = action_entry IntMap.t
  type goto_table = state IntMap.t IntMap.t

  let empty_action_entry = {shift = None; reduce = []; accept = []};;

  let add_reduce_action (act : reduce_record) (t : Terminal.t) 
        (tm : action_entry Tmap.t) 
        : action_entry Tmap.t =
    try 
      let ae = Tmap.find t tm in
        Tmap.add t {ae with reduce = act::ae.reduce} tm
    with Not_found -> Tmap.add t {empty_action_entry with reduce = [act]} tm;;

  let add_reductions (is : ItemSet.t) (terms : Tset.t) (also_eof : bool)
        (act : action_entry Tmap.t) 
        : (action_entry Tmap.t * action_entry) =
    ItemSet.fold 
      (fun i (res, eofs) -> 
         if i.after_dot = [] && not i.initial then
           let p = i.prod in
           let red = {reduce_left = p.prod_left;
                      reduce_action = p.prod_action;
                      reduce_reject = p.reject;
                      reduce_index = p.index;
                      reduce_length = List.length p.prod_right;
                      reduce_transparent = p.transparent;
                      reduce_label = if debug then gram_syms_to_string p.prod_right else ""}
           in
           let restrictions = 
             try NTmap.find i.prod.prod_left single_follow_restrs
             with Not_found -> [] in
           (Tset.fold 
              (fun t tm -> 
                 if List.exists (fun p -> p t) restrictions then tm
                 else add_reduce_action red t tm)
              terms res,
            if also_eof then
              {eofs with reduce = red::eofs.reduce}
            else
              eofs)
         else if i.after_dot = [] then
           (res, {eofs with accept=i.prod.prod_left::eofs.accept})
         else
           (res, eofs))
      is
      (act,empty_action_entry);;

  let goto_state (add : 'a -> int -> 'b -> 'b) (across : 'a) 
        (items : ItemSet.t) 
        ((to_do : (ItemSet.t * int) list), (seen : int ItemSetMap.t), 
         (next : int), (res : 'b))
        : ((ItemSet.t * int) list * int ItemSetMap.t * int * 'b) =
    let (new_todo, idx, new_seen, new_next) = 
      try 
        let idx = ItemSetMap.find items seen in
          ((items, idx)::to_do, idx, seen, next)
      with Not_found -> 
        ((items, next)::to_do, next, ItemSetMap.add items next seen, next+1)
    in
      (new_todo, new_seen, new_next, add across idx res);;

  let rec build_table (to_do : (ItemSet.t * int) list) (seen : int ItemSetMap.t)
        (next : int)
        (act : action_table) (goto : goto_table) (eof : eof_table)
        : (int ItemSetMap.t * action_table * goto_table * eof_table * int) =
    match to_do with
        [] -> (seen, act, goto, eof, next)
      | ((is, idx)::to_do) ->
            if IntMap.mem idx act then
              build_table to_do seen next act goto eof
            else
              let closed_is = closure is in
              let (across_nt, across_t) = goto_all closed_is in
              let (new_todo1, new_seen1, new_next1, goto_table_entry) =
                ProdMap.fold 
                  (fun p v -> (goto_state IntMap.add) p.index v)
                  across_nt
                  (to_do, seen, next, IntMap.empty)
              in
              let (new_todo2, new_seen2, new_next2, action_shifts) =
                Tmap.fold 
                  (goto_state 
                     (fun a b c ->
                        Tmap.add 
                          a {empty_action_entry with shift = Some b} c)) 
                  across_t
                  (new_todo1, new_seen1, new_next1, Tmap.empty)
              in
              let (act_entry, eof_entry) = 
                add_reductions closed_is all_ts true action_shifts 
              in
                build_table 
                  new_todo2 new_seen2 new_next2
                  (IntMap.add idx act_entry act) 
                  (IntMap.add idx goto_table_entry goto)
                  (IntMap.add idx eof_entry eof);;

  let build_start_states (nts : Nonterminal.t list) 
           : ((ItemSet.t * int) list * int ItemSetMap.t * int * int NTmap.t) =
    List.fold_right
      (fun nt (to_do, seen, next, starts) ->
         let i = ItemSet.singleton
                   {before_dot = []; 
                    before_dot_length = 0;
                    after_dot = [NT nt];
                    initial = true;
                    prod = {prod_left = nt;
                            prod_right = [NT nt];
                            prod_action = (fun [r] -> r);
                            reject = false;
                            transparent = false;
                            index = !prod_count}} in
           prod_count := !prod_count + 1;
           ((i, next)::to_do, ItemSetMap.add i next seen,
            next + 1, 
            NTmap.add nt next starts))
      nts
      ([], ItemSetMap.empty, 0, NTmap.empty);;

  let transpose_action_table (num_states : int)
        (at : action_entry Tmap.t IntMap.t)
        : action_entry array Tmap.t =
    let result = ref Tmap.empty in
    let add_entry term from_state to_state =
      try 
        let a = Tmap.find term !result in
          a.(from_state) <- to_state
      with Not_found ->
        let a = Array.make num_states empty_action_entry in
          a.(from_state) <- to_state;
          result := Tmap.add term a !result
    in
      IntMap.iter
      (fun from_state tmap ->
         Tmap.iter
           (fun term to_state -> add_entry term from_state to_state)
           tmap)
        at;
      !result;;

  let transpose_goto_table (num_prods : int) (num_states : int)
        (gt : state IntMap.t IntMap.t)
        : (state, state) Hashtbl.t array =
    let result = Array.make num_prods (Hashtbl.create 0) in
      for i = 0 to num_prods - 1 do
        result.(i) <- Hashtbl.create 10
      done;
      IntMap.iter
      (fun from_state pmap ->
         IntMap.iter
           (fun index to_state -> 
              Hashtbl.add result.(index) from_state to_state)
           pmap)
        gt;
      result;;


  let ((action_table : action_entry array Tmap.t),
       (eof_table : action_entry array), 
       (goto_table : (state, state) Hashtbl.t array), 
       (start_table : state NTmap.t), 
       item_set_mapping) = 
    let (to_do, seen, next, start_table) = build_start_states starts in
    let (seen, at, gt, et, num_states) = 
      build_table to_do seen next IntMap.empty IntMap.empty IntMap.empty
    in
      (transpose_action_table num_states at, 
       int_map_to_array et num_states (fun () -> empty_action_entry), 
       transpose_goto_table !prod_count num_states gt,
       start_table,
      if debug then
        seen
      else
        ItemSetMap.empty);;

  let print_nullables () =
    print_string (nonterms_to_string (NTset.elements nullable) ^ "\n");;

  let print_prod p = 
    print_string (Nonterminal.to_string p.prod_left ^ " ::= " ^
                  gram_syms_to_string p.prod_right ^ "\n");;

  let print_grammar g =
    List.iter print_prod g;;

  let print_item i = 
    print_string ("  " ^ Nonterminal.to_string i.prod.prod_left ^ " = " ^ 
                  gram_syms_to_string (List.rev i.before_dot) ^ " . " ^
                  gram_syms_to_string i.after_dot);
    if i.initial then
      print_string "   INIT\n"
    else
      print_string "\n";;

  let print_action_entry (a : action_entry) = 
    begin
      match a.shift with
          None -> ()
        | Some s -> 
            print_string "    Shift ";
            print_int s;
            print_string "\n"
    end;
    List.iter
      (function rr ->
        print_string ("    Reduce " ^ Nonterminal.to_string rr.reduce_left);
        print_string "   ";
        print_int rr.reduce_length;
        print_string "\n")
      a.reduce;
    List.iter
      (fun nt ->
         print_string ("    Accept " ^ Nonterminal.to_string nt ^ "\n"))
      a.accept;;

  let print_actions num =
    Tmap.iter 
      (fun term acts ->
         print_string ("  " ^ Terminal.to_string term ^ ":\n");
         print_action_entry acts.(num))
      action_table;;

  let print_eof num =
    print_string "  EOF:\n";
    print_action_entry (Array.get eof_table num);;

  let print_goto num = 
    Hashtbl.iter
    (fun nt gt -> print_string ("  " ^ string_of_int nt ^ ": Goto "
    ^ string_of_int gt ^ "\n"))
    (Array.get goto_table num);;

  let print_state s num =
    print_int num;
    print_string ":\n";
    ItemSet.iter print_item (closure s);
    print_string "\n";
    print_actions num;
    print_eof num;
    print_goto num;
    print_string "\n\n";;

  let print_lr0 () = ItemSetMap.iter print_state item_set_mapping;;

  if debug then
  begin
    print_string "grammar:\n";
    print_grammar grammar;
    print_string "nullable:\n";
    print_nullables ();
    (*
    print_string "\nLR(0):\n";
    print_lr0 ();
     *)
    print_string "\n"
  end;;
end
