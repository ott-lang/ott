(*
  Experimental code to pretty print Cowbar [1] generator code to freely generate expressions from the Ott grammar

  [1] https://github.com/stedolan/crowbar

  TODO - For metavars with Ocaml types specified; can we pp a generic gen function?
    Go through special cases in sail.ott and see if we should/can extend cgen to handle them
    Add documentation

   Distinguish between different dot forms - use list or list1 from crowbar

   Fault if zero branches in choose
 *)
open Types


let pp_cgen_preamble fd sd =
  output_string fd "(* Generated from Ott *)\n";
  List.iter (fun (_,hname,espec) ->
      Printf.eprintf "hname = %s\n" hname;
      if hname = "cgen" then
        List.iter (fun (Embed_string (_,s)) -> output_string fd s) espec
      else
        ()) sd.xd_embed

let cgen_hom p = Auxl.hom_spec_for_hom_name "cgen" p.prod_homs
            
let rec pp_element_list es = List.concat (List.map pp_element  es)

and pp_element (ele : element ) :  (string*string) list = match ele with
  | Lang_nonterm (x,y) -> [ ( "(unlazy " ^  x ^ "_gen)" ,Grammar_pp.pp_plain_nonterm y)]
  | Lang_metavar (x,y) -> [ ( "(unlazy " ^  x ^ "_gen)" ,Grammar_pp.pp_plain_metavar y)]
  | Lang_list elb -> pp_list_form elb                                     
  | _ -> []
                                         
and pp_list_form (elb : element_list_body) : (string*string) list =

  let rec mk_pairs xs = match xs with
      x::xs -> (match pp_element x with
                  [] -> mk_pairs xs
                | s -> let s = String.concat " " (List.map fst s) in
                       match xs with
                        | [] -> s
                        | _ -> "pair " ^ s ^ " " ^ (mk_pairs xs) ^ "")
    | _ -> ""
  in
  [ ("list1 ( " ^ (mk_pairs elb.elb_es) ^ ")" , "xx") ]

let pp_ctor p = String.capitalize_ascii (p.prod_name)
            
let pp_prod_gen_aux fd p =   match (pp_element_list p.prod_es) with
  | [] -> output_string fd ("   const " ^ (pp_ctor p) ^ ";\n" )
  | ntmvs ->
     output_string fd "   map [ ";
     output_string fd (String.concat "; " (List.map fst ntmvs));
     output_string fd "] (fun ";
     output_string fd (String.concat " "  (List.map snd ntmvs));
     output_string fd  (" -> " ^ (pp_ctor p) ^ " ( ");
     output_string fd (String.concat ", " (List.map snd ntmvs));
     output_string fd "));\n"

let pp_prod_gen fd p = match (cgen_hom p) with
  | None -> pp_prod_gen_aux fd p
  | Some hs ->  (List.iter (fun h -> match h with
                                                           | Hom_string s -> output_string fd s
                                                           | _ -> () ) hs);
            output_string fd "\n"

let pp_skip_prod p = match (cgen_hom p) with
  | None -> p.prod_meta || p.prod_sugar
  | Some _ -> false
                   
let pp_rule_gen fd fun_prefix r =
  let fname = (r.rule_ntr_name) ^ "_gen" in
  let prods = List.filter (fun p -> not (pp_skip_prod p)) r.rule_ps in 
  output_string fd ( fun_prefix  ^ fname ^ " = lazy (choose [ \n");
  List.iter (pp_prod_gen fd) prods;
  output_string fd "])\n"

let init_list n ~f =
  let rec init_list' i n f =
    if i >= n then []
    else (f i) :: (init_list' (i+1) n f)
  in init_list' 0 n f
  
                
let pp_cgen_generators fd sd =
  let rlist = List.filter (fun r -> not (r.rule_judgement || r.rule_semi_meta || r.rule_meta || r.rule_phantom)) sd.xd_rs in 
  List.iter  (fun (pr,r) ->  pp_rule_gen fd pr r)
             (List.combine ("let rec " :: (init_list (List.length rlist - 1) (fun _ -> " and "))) rlist)

let pp_cgen_lazy_pat fd sd = List.iter
             (fun r -> if r.rule_judgement || r.rule_semi_meta || r.rule_meta || r.rule_phantom then
                         ()
                       else
                         output_string fd ("let lazy " ^ r.rule_ntr_name ^ "_gen = " ^ r.rule_ntr_name ^ "_gen\n"))
             sd.xd_rs

             
let generate_cgen (sd : syntaxdefn )  (filename : string ) : unit = 
  let fd = open_out filename in
  pp_cgen_preamble fd sd;
  pp_cgen_generators fd sd;
  pp_cgen_lazy_pat fd sd;
  close_out fd


            
                     
