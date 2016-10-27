(**************************************************************************)
(*                               glr                                      *)
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
 * tech. report.*)  

module IntMap = Parse_table.IntMap
module IntPairMap = Parse_table.IntPairMap

module type S =
sig
  module Nonterminal : Set.OrderedType
  module Terminal : Set.OrderedType

  type result
  type parse_tree

  val parse : Nonterminal.t -> (unit -> Terminal.t) -> parse_tree option
  val process_parse_tree : parse_tree -> result list
end;;

module type IN =
sig
  include Parse_table.S
  val debug : bool
  exception Reject_parse
  exception Reject_all_parses
end;;

module Make (Pt : IN) : S with
module Nonterminal = Pt.Nonterminal and
module Terminal = Pt.Terminal and
type result = Pt.result =
struct

  open Pt

  module Nonterminal = Pt.Nonterminal
  module Terminal = Pt.Terminal
  type result = Pt.result

  module NTset = Set.Make (Nonterminal)

  let rec find f l =
    match l with
      [] -> None
    | (x::y) -> if f x then Some x else find f y;;

  type rule_node = 
      {rule_nt : reduce_record;
       outgoing : term_or_sym_node list;
       rn_index : int}
  and symbol_node = 
      {mutable possibilities : rule_node list;
       mutable rejected : bool;
       span : int;
       sn_index : int;
       (* The following fields are for doing the depth-first traversal *)
       mutable started : bool;
       mutable finished : bool;
       mutable answers : (result * int list * NTset.t) list;
       mutable debug : string}
  and term_or_sym_node = 
      TermNode of Terminal.t
    | SymNode of symbol_node

  type link = 
      {next_stack : stack_node; 
       tree : term_or_sym_node;
       mutable link_reject : bool}
  and stack_node =
      {state : int; 
       mutable children : link list}

  let print_states s =
    List.iter (fun s -> print_int s; print_string " ") s;;

  let termsym_to_span =
    function
        TermNode _ -> 1
      | SymNode s -> s.span;;

  (* Follow all paths in the stack of length len and apply f to the path.
   * Filter out paths that do not satisfy the link predicate. *)
  let rec iter_paths (link : term_or_sym_node -> bool) (seen_link : bool)
        (len : int) (p : stack_node) 
        (f : stack_node -> int -> term_or_sym_node list -> unit) 
        (kids : term_or_sym_node list) (span : int)
        : unit =
    if len = 0 && seen_link then
      f p span kids
    else if len = 0 then
      ()
    else
      List.iter 
        (fun {next_stack=p'; tree = l} ->
           iter_paths link (seen_link || link l) (len - 1) p' f (l::kids)
             (span + termsym_to_span l)) 
        p.children;;

  let get_rulenode (prod : reduce_record) (kids : term_or_sym_node list) idx 
        : rule_node =
    {rule_nt = prod; outgoing = kids; rn_index = idx}

  let add_rulenode (l : link) (rulenode : rule_node) : unit =
    match l.tree with
      SymNode s -> 
        s.possibilities <- rulenode::s.possibilities;
        if rulenode.rule_nt.reduce_reject then
          begin
            l.link_reject <- true;
            s.rejected <- true
          end
    | _ -> assert false;;

  let get_symbolnode (rulenode : rule_node) (span : int) idx : symbol_node =
    {possibilities = [rulenode]; span = span;
     rejected = rulenode.rule_nt.reduce_reject;
     sn_index = idx; started = false; finished = false; answers = []; debug = ""}

  let empty_action = {shift = None; reduce = []; accept = []};;

  let get_actions (ct : Terminal.t) =
    if Terminal.is_eof ct then
      (fun p -> eof_table.(p.state))
    else 
      try 
        let a = Tmap.find ct action_table in
        (fun p -> a.(p.state))
      with Not_found -> fun p -> empty_action;;


  let addLink (leftSib : stack_node) (rightSib : stack_node)
        (semanticValue : term_or_sym_node) (reject : bool)
        : unit = 
     rightSib.children <- {next_stack=leftSib; 
                           tree=semanticValue; 
                           link_reject=reject} :: rightSib.children;;

  let doShifts (prevTops : stack_node IntMap.t) c action_map (pos : int)
        : stack_node IntMap.t =
    IntMap.fold 
      (fun state current topmost -> 
         match (action_map current).shift with
             None -> topmost
           | Some dest ->
               try 
                 let rightSib = IntMap.find dest topmost in
                   addLink current rightSib c false;
                   topmost
               with Not_found ->
                 let rightSib = {state = dest; children = []} in
                   addLink current rightSib c false;
                   IntMap.add dest rightSib topmost)
      prevTops
      IntMap.empty;;


  module HeapItem = 
  struct
    type t = term_or_sym_node list * int * reduce_record * (state, state) Hashtbl.t * stack_node
    let compare (p1, span1, prod1, _, sn1) (p2, span2, prod2, _, sn2) =
      if span1 > span2 then
        -1
      else if span1 < span2 then
        1
      else
        compare 
          (NTmap.find prod2.reduce_left nt_ordering)
          (NTmap.find prod1.reduce_left nt_ordering)
  end
(*
  module H = Graph.Heap.Imperative (HeapItem);;
 *)

  module H = 
  struct
    exception EmptyHeap
    let create x = ref []
    let add q e = q := e :: !q
    let is_empty q = !q = []
    let pop_maximum q = 
      match !q with
          [] -> raise EmptyHeap
        | x::y ->  
            q := y;
            x
  end;;

  let increment i =
    let r = !i in
      incr i;
      r

  let doReductions (counter : int ref) (topmost : stack_node IntMap.t) 
        action_map (pos : int) : stack_node IntMap.t =
    let pathQueue = H.create 4 in
    let topmost = ref topmost in
    let enqueue_state (link : symbol_node option) _ (current : stack_node)
          : unit =
      let (pred, start) =
        match link with
            None -> ((fun _ -> false), true)
          | Some l -> ((function 
                            TermNode _ -> false
                          | SymNode l' -> l == l'),
                       false)
      in
      List.iter 
        (function rr ->
          iter_paths pred start rr.reduce_length current 
            (fun leftSib span p -> 
               H.add pathQueue (p, span, rr, goto_table.(rr.reduce_index), leftSib)) [] 0)
        (action_map current).reduce
    in
    let enqueueLimitedReductions (link : symbol_node) : unit =
      IntMap.iter (enqueue_state (Some link)) !topmost
    in
    let reduceViaPath ((p : term_or_sym_node list), 
                       (span : int),
                       (rr : reduce_record),
                       (trans : (state, state) Hashtbl.t), 
                       (leftSib : stack_node))
          : unit =
      let rulenode = get_rulenode rr p (increment counter) in
      let newSemanticValue = get_symbolnode rulenode span (increment counter) in
      let new_state = Hashtbl.find trans (leftSib.state) in
        try 
          let rightSib = IntMap.find new_state !topmost in
            match find (fun {next_stack=n} -> leftSib == n) rightSib.children with
               Some link -> 
                 add_rulenode link rulenode
             | None -> 
                 addLink leftSib rightSib (SymNode newSemanticValue) 
                   rr.reduce_reject;
                 enqueueLimitedReductions newSemanticValue
        with Not_found ->
          let rightSib = {state = new_state; children = []} in
            addLink leftSib rightSib (SymNode newSemanticValue) rr.reduce_reject;
            topmost := IntMap.add new_state rightSib !topmost;
            enqueue_state None new_state rightSib
    in
      IntMap.iter (enqueue_state None) !topmost;
      while not (H.is_empty pathQueue)
      do
        reduceViaPath (H.pop_maximum pathQueue)
      done;
      !topmost;;

  let rec per_char (counter : int ref) (pos : int) 
        (next_terminal : unit -> Terminal.t) (topmost : stack_node IntMap.t) 
        : stack_node IntMap.t =
    let c = next_terminal () in
    let action_map = get_actions c in
    let topmost = doReductions counter topmost action_map pos in
      if debug then
        begin
          print_string "Reducing to: ";
          IntMap.iter (fun st {children=c} -> 
                         print_int st; 
                         print_string "("; 
                         print_int (List.length c); 
                         print_string ") ")
            topmost;
          print_string "\n";
          flush stdout
        end;
      if Terminal.is_eof c then
        topmost
      else begin
            let topmost = doShifts topmost (TermNode c) action_map pos in
              if debug then
                begin
                  print_string (Terminal.to_string c); 
                  print_string (": ");
                  IntMap.iter (fun st {children=c} -> 
                                 print_int st; 
                                 print_string "("; 
                                 print_int (List.length c); 
                                 print_string ") ")
                    topmost;
                  print_string "\n";
                  flush stdout;
                end;
              if not (IntMap.is_empty topmost) then
                per_char counter (pos + 1) next_terminal topmost
              else
                topmost
      end;;

  type parse_tree = symbol_node

  let parse (start : Nonterminal.t) (next_terminal : unit -> Terminal.t) 
        : parse_tree option =
    if debug then 
      begin
        print_string "start_state: ";
        print_int (NTmap.find start start_table); print_string "\n"
      end;
    let start_state = NTmap.find start start_table in
    let topmost = 
      per_char (ref 0) 0 next_terminal
        (IntMap.add start_state {state = start_state; children = []} 
           IntMap.empty)
    in
    let accepting_stacks = 
      List.filter
        (fun st ->
           List.exists 
             (fun nt -> Nonterminal.compare start nt = 0)
             (get_actions Terminal.eof st).accept)
        (IntMap.fold (fun _ a b -> a::b) topmost [])
    in
      match accepting_stacks with
          [] -> None
        | [{children = [{tree=SymNode sn}]}] -> 
            Some sn
        | _ -> assert false;;

(*
  if Sys.file_exists "parse_trees.dot" then
    Sys.remove "parse_trees.dot";;
 *)

  let get_sym_nodes (head : symbol_node) : symbol_node list = 
    let sym_nodes = ref [] in
    let rec get (sn : symbol_node) : unit =
      if sn.started then
        ()
      else
        begin
          sn.started <- true;
          sym_nodes := sn :: !sym_nodes;
          List.iter 
            (fun rn -> 
               List.iter 
                 (function 
                      TermNode _ -> ()
                    | SymNode sn -> get sn)
                 rn.outgoing)
            sn.possibilities
        end
    in
      get head;
      List.iter 
        (fun sn -> sn.started <- false) 
        !sym_nodes;
      !sym_nodes

  let print_parse_tree all_sns = 

    let out = open_out_gen (if Sys.file_exists "parse_trees.dot" then
                              [Open_append]
                            else 
                              [Open_creat; Open_append]) 0o644
                "parse_trees.dot" in

    let rec print_rule_node (rn : rule_node) : unit =
      Printf.fprintf out "rn%s[shape=box,label=\"%s%s\"]\n" 
        (string_of_int rn.rn_index)
        (rn.rule_nt.reduce_label)
        (if rn.rule_nt.reduce_transparent then " (transp) " else "");

      List.iter 
        (function 
             TermNode t -> 
               (*
               output_string out ("t" ^ string_of_int idx ^ 
                                  "[label=\"" ^ Terminal.to_string t ^ "\"]\n");
               output_string out ("rn" ^ string_of_int rn.rn_index ^ " -> " ^
                                  "t" ^ string_of_int idx ^ "\n")
                *)
               ()
           | SymNode sn -> 
               Printf.fprintf out "rn%s -> sn%s\n" (string_of_int rn.rn_index)
                                  (string_of_int sn.sn_index))
        rn.outgoing

    and print_symbol_node (sn : symbol_node) : unit =
      output_string out ("sn" ^ string_of_int sn.sn_index ^ "[color=" ^ 
                         (if sn.rejected then
                            "green"
                          else
                            "blue") ^
                         ",label=\"" ^ 
                         begin
                           match sn.possibilities with
                               [] -> ""
                             | x::y ->
                                 Nonterminal.to_string x.rule_nt.reduce_left 
                         end ^
                         sn.debug ^
                         "\"]\n");
          List.iter
            (fun rn -> 
               output_string out ("sn" ^ string_of_int sn.sn_index ^ " -> " ^
                                  "rn" ^ string_of_int rn.rn_index ^ 
                                  "[color=blue]\n"))
            sn.possibilities;
          List.iter print_rule_node sn.possibilities;

    in
      output_string out "digraph {\n";
      List.iter print_symbol_node all_sns;
      output_string out "}\n";
      flush out;
      close_out out;

  module G = struct
    type t = symbol_node list
    module V = struct
      type t = symbol_node
      let compare x y = Pervasives.compare x.sn_index y.sn_index
      let hash x = x.sn_index
      let equal x y = x.sn_index = y.sn_index
    end
    let iter_vertex f sns = List.iter f sns
    let iter_succ f _ sn =
      List.iter 
        (fun rn -> 
           List.iter (function TermNode _ -> () | SymNode sn -> f sn) rn.outgoing)
        sn.possibilities
  end

  module Scc = Graph.Components.Make(G)

  type injection_map = No_inj | All_inj | One_inj of int;;

  let get_inj (y : term_or_sym_node list) : injection_map = 
    let rec get_inj (count : int) : term_or_sym_node list -> injection_map = 
      function 
          [] -> All_inj
        | TermNode _ :: l -> No_inj
        | SymNode s :: l ->
            let eps = (s.span = 0) in
              match get_inj (count + 1) l with
                  No_inj -> No_inj
                | All_inj ->
                    if eps then
                      All_inj
                    else
                      One_inj count
                | One_inj x ->
                    if eps then
                      One_inj x
                    else
                      No_inj
    in
      get_inj 0 y

  let epsilon_map (nodes : term_or_sym_node list) : bool array =
    Array.of_list
      (List.map
         (function
              TermNode _ -> false
            | SymNode s -> s.span = 0)
         nodes);;

  let check_conflicts (eps_map : bool array) (ancestor_idx : int)
        (position : int)  (children : int list)
        : bool =
    let tmp = ref true in
    let left_eps = 
      for i = 0 to position - 1 do
        tmp := !tmp && eps_map.(i)
      done;
      !tmp
    in
    let tmp = ref true in
    let right_eps =
      for i = position + 1 to Array.length eps_map - 1 do
        tmp := !tmp && eps_map.(i)
      done;
      !tmp
    in
      List.for_all
        (fun child ->
           try
             let (g,l,r,n) = IntPairMap.find (ancestor_idx, child) priority in
               not (g ||
                    ((r || n) && not right_eps && left_eps) ||
                    ((l || n) && not left_eps && right_eps))
           with Not_found -> true)
        children;;

  let process_parse_tree pt = 

    let rec process_rule_node (rn : rule_node) : (result * int list * NTset.t) list =
      let idx = rn.rule_nt.reduce_index in
        List.fold_right
          (fun (rl,injection_children,loop) res -> 
             if NTset.mem rn.rule_nt.reduce_left loop then
               res
             else
               try
                 (rn.rule_nt.reduce_action rl, 
                  idx::injection_children,
                  NTset.add rn.rule_nt.reduce_left loop)::res
               with Reject_parse ->
                 res)
          (process_t_or_s_nodes idx rn.outgoing rn.rule_nt.reduce_transparent)
          []

    and process_t_or_s_nodes (conflict_idx : int)
          (nodes : term_or_sym_node list) (transp : bool)
          : (result list * int list * NTset.t) list =
      let eps_map = epsilon_map nodes in
      let (combine_f,combine_nt) =
        match get_inj nodes with
            No_inj -> 
              ((fun _ _ _ -> []),
               (fun _ _ _ -> NTset.empty))
          | All_inj -> 
              ((fun _ fr_idxs ridxs -> fr_idxs@ridxs),
               (fun _ x y -> NTset.union x y))
          | One_inj n ->
              ((fun i fr_idxs ridxs -> if i = n then fr_idxs else ridxs),
               (fun i x y -> if i = n then x else y))
      in
      let combine_f = if not transp then combine_f else (fun _ x y -> x @ y) in
      let rec process i =
        function
            [] -> [([], [],NTset.empty)]
          | TermNode _ :: rest -> 
              process (i + 1) rest
          | SymNode sn :: rest ->
              let first_results = 
                List.filter
                  (fun (r, conflicts, _) ->
                     check_conflicts eps_map conflict_idx i conflicts)
                  (process_sym_node sn)
              in
              let rest_results = process (i + 1) rest in
                List.flatten
                  (List.map 
                     (fun (f_res,f_idx,f_nts) -> 
                        List.map 
                          (fun (r_res,r_idx,r_nts) -> 
                             (f_res::r_res,
                              combine_f i f_idx r_idx,
                              combine_nt i f_nts r_nts))
                          rest_results)
                     first_results)
      in
        process 0 nodes

    and process_sym_node sn =
      if sn.finished then 
        sn.answers
      else if sn.started then
        []
      else if sn.rejected then
        begin
          sn.finished <- true;
          sn.answers <- [];
          []
        end
      else
        let ans = 
          try
            sn.started <- true;
            List.flatten (List.map process_rule_node sn.possibilities)
          with Reject_all_parses ->
            []
        in
          sn.finished <- true;
          sn.answers <- ans;
          ans
    in

    let process_component (comp : symbol_node list) : unit =
      match comp with
        | [] -> assert false
        | sns ->
            let answers = 
              List.map 
                (fun sn ->
                   let res = process_sym_node sn in
                     List.iter (fun sn -> 
                                  sn.started <- false; 
                                  sn.finished <- false;
                                  sn.answers <- []) sns;
                     res)
                sns
            in
              List.iter2
                (fun sn a -> 
                   sn.answers <- a;
                   sn.debug <- "(" ^ string_of_int (List.length a) ^ ")";
                   sn.finished <- true)
                sns
                answers
    in

    let all_sn = get_sym_nodes pt in
    (* print_parse_tree all_sn; *)
    let (scc : symbol_node list array) = Scc.scc_array all_sn in
      for i = 0 to Array.length scc - 1 do
        process_component scc.(i)
      done;
      List.map (fun (x,_,_) -> x) pt.answers

end
