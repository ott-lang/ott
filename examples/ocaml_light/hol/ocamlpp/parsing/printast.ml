(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*             Damien Doligez, projet Para, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id: printast.ml,v 1.4 2008/02/07 17:09:50 so294 Exp $ *)

open Asttypes;;
open Format;;
open Lexing;;
open Location;;
open Parsetree;;

let fmt_constr f x = 
  match x with
    | "Invalid_argument" -> fprintf f "C_invalidargument"
    | "Not_found" -> fprintf f "C_notfound"
    | "Assert_failure" -> fprintf f "C_assertfailure"
    | "Match_failure" -> fprintf f "C_matchfailure"
    | "Division_by_zero" -> fprintf f "C_div_by_0"
    | "None" -> fprintf f "C_none"
    | "Some" -> fprintf f "C_some"
    | _ -> fprintf f "(C_name (CN_id \"%s\"))" x

let fmt_position f l = ()
(*
  if l.pos_fname = "" && l.pos_lnum = 1
  then fprintf f "%d" l.pos_cnum
  else if l.pos_lnum = -1
  then fprintf f "%s[%d]" l.pos_fname l.pos_cnum
  else fprintf f "%s[%d,%d+%d]" l.pos_fname l.pos_lnum l.pos_bol
               (l.pos_cnum - l.pos_bol)
 *)
;;

let fmt_location f loc = ()
  (*
  fprintf f "(%a..%a)" fmt_position loc.loc_start fmt_position loc.loc_end;
  if loc.loc_ghost then fprintf f " ghost";
   *)
;;

let rec fmt_longident_aux f x =
  match x with
  | Longident.Lident (s) -> fprintf f "%s" s;
  | Longident.Ldot (y, s) -> fprintf f "%a.%s" fmt_longident_aux y s;
  | Longident.Lapply (y, z) ->
      fprintf f "%a(%a)" fmt_longident_aux y fmt_longident_aux z;
;;

let fmt_longident f x = fprintf f "\"%a\"" fmt_longident_aux x;;

let fmt_constant f x =
  match x with
  | Const_int (i) -> 
      if i < 0 then
        fprintf f "(CONST_int ($- %dw))" ~-i
      else
        fprintf f "(CONST_int %dw)" i;
  | Const_char (c) -> fprintf f "(CONST_char %02x)" (Char.code c);
  | Const_string (s) -> fprintf f "(CONST_string %S)" s;
  | Const_float (s) -> fprintf f "(CONST_float %s)" s;
  | Const_int32 (i) -> fprintf f "(CONST_int32 %ld)" i;
  | Const_int64 (i) -> fprintf f "(CONST_int64 %Ld)" i;
  | Const_nativeint (i) -> fprintf f "(CONST_nativeint %nd)" i;
;;

let fmt_mutable_flag f x =
  match x with
  | Immutable -> fprintf f "Immutable";
  | Mutable -> fprintf f "Mutable";
;;

let fmt_virtual_flag f x =
  match x with
  | Virtual -> fprintf f "Virtual";
  | Concrete -> fprintf f "Concrete";
;;

let fmt_rec_flag f x =
  match x with
  | Nonrecursive -> fprintf f "Nonrec";
  | Recursive -> fprintf f "Rec";
  | Default -> fprintf f "Default";
;;

let fmt_direction_flag f x =
  match x with
  | Upto -> fprintf f "FD_upto";
  | Downto -> fprintf f "FD_downto";
;;

let fmt_private_flag f x =
  match x with
  | Public -> fprintf f "Public";
  | Private -> fprintf f "Private";
;;

let line i f s (*...*) =
  fprintf f "%s" (String.make (2*i) ' ');
  fprintf f s (*...*)
;;

let list i f ppf l =
  match l with
  | [] -> line i ppf "[]\n";
  | h::t ->
     line i ppf "(\n";
     List.iter (fun x -> f (i+1) ppf x; line (i+1) ppf "::\n") l;
     line i ppf "[])\n";
;;

let option i f ppf x =
  match x with
  | None -> line i ppf "None\n";
  | Some x ->
      line i ppf "Some\n";
      f (i+1) ppf x;
;;

let longident i ppf li = line i ppf "%a\n" fmt_longident li;;
let string i ppf s = line i ppf "\"%s\"\n" s;;
let bool i ppf x = line i ppf "%s\n" (string_of_bool x);;
let label i ppf x = line i ppf "label=\"%s\"\n" x;;

let rec core_type i ppf x =
  let i = i+1 in
  match x.ptyp_desc with
  | Ptyp_any -> line i ppf "TE_any\n";
  | Ptyp_var (s) -> line i ppf "(TE_var (TV_ident \"%s\"))\n" s;
  | Ptyp_arrow (l, ct1, ct2) ->
      line i ppf "(TE_arrow\n";
      core_type i ppf ct1;
      core_type i ppf ct2;
      line i ppf ")\n";
  | Ptyp_tuple l ->
      line i ppf "(TE_tuple [\n";
      list i core_type ppf l;
      line i ppf "])\n";
  | Ptyp_constr (li, l) ->
      line i ppf "(TE_constr \n";
      list (i+1) core_type ppf l;
      line (i+1) ppf "(TC_name (TCN_id %a))\n" fmt_longident li;
      line i ppf ")\n";
  | Ptyp_variant (l, closed, low) ->
      (*
      line i ppf "Ptyp_variant closed=%s\n" (string_of_bool closed);
      list i label_x_bool_x_core_type_list ppf l;
      option i (fun i -> list i string) ppf low
       *)
      assert false;
  | Ptyp_object (l) ->
      (*
      line i ppf "Ptyp_object\n";
      list i core_field_type ppf l;
       *)
      assert false;
  | Ptyp_class (li, l, low) ->
      (*
      line i ppf "Ptyp_class %a\n" fmt_longident li;
      list i core_type ppf l;
      list i string ppf low
       *)
      assert false;
  | Ptyp_alias (ct, s) ->
      (*
      line i ppf "Ptyp_alias \"%s\"\n" s;
      core_type i ppf ct;
       *)
      assert false;
  | Ptyp_poly (sl, ct) ->
      (match sl with 
           [] -> core_type i ppf ct
         | _ -> assert false);
      (*line i ppf "Ptyp_poly%a\n"
        (fun ppf -> List.iter (fun x -> fprintf ppf " '%s" x)) sl;
      core_type i ppf ct;
       *)

      (*
and core_field_type i ppf x =
  line i ppf "core_field_type %a\n" fmt_location x.pfield_loc;
  let i = i+1 in
  match x.pfield_desc with
  | Pfield (s, ct) ->
      line i ppf "Pfield \"%s\"\n" s;
      core_type i ppf ct;
  | Pfield_var -> line i ppf "Pfield_var\n";
       *)

and pattern i ppf x =
  let i = i+1 in
  match x.ppat_desc with
  | Ppat_any -> line i ppf "P_any\n";
  | Ppat_var (s) -> line i ppf "(P_var (VN_id \"%s\"))\n" s;
  | Ppat_alias (p, s) ->
      line i ppf "(P_alias\n";
      pattern i ppf p;
      line (i + 1) ppf "(VN_id \"%s\"))\n" s;
  | Ppat_constant (c) -> line i ppf "(P_constant %a)\n" fmt_constant c;
  | Ppat_tuple (l) ->
      line i ppf "(P_tuple\n";
      list (i+1) pattern ppf l;
      line i ppf ")\n";
  | Ppat_construct (li, po, b) ->
       (match (li,po) with
           (Longident.Lident "false", None) ->
             line i ppf "(P_constant CONST_false)\n"
         | (Longident.Lident "true", None) ->
             line i ppf "(P_constant CONST_true)\n"
         | (Longident.Lident "[]", None) -> 
             line i ppf "(P_constant CONST_nil)\n"
         | (Longident.Lident "()", None) -> 
             line i ppf "(P_constant CONST_unit)\n"
         | (Longident.Lident c, None) -> 
             line i ppf "(P_constant (CONST_constr %a))\n" fmt_constr c
         | (Longident.Lident "::", Some {ppat_desc=Ppat_tuple [e1; e2]}) ->
             line i ppf "(P_cons\n";
             pattern (i+1) ppf e1;
             pattern (i+1) ppf e2;
             line i ppf ")\n";
         | (Longident.Lident c, Some {ppat_desc=Ppat_any}) ->
             line i ppf "(P_construct_any %a)\n" fmt_constr c;
         | (Longident.Lident c, Some arg) ->
             line i ppf "(P_construct %a\n" fmt_constr c;
             (match arg.ppat_desc with
                  Ppat_tuple exps -> list (i + 1) pattern ppf exps
                | _ -> list (i + 1) pattern ppf [arg]);
             line i ppf ")\n";
         | _ -> assert false)
  | Ppat_variant (l, po) ->
      (*
      line i ppf "Ppat_variant \"%s\"\n" l;
      option i pattern ppf po;
       *)
      assert false;
  | Ppat_record (l) ->
      line i ppf "(P_record\n";
      list (i+1) longident_x_pattern ppf l;
      line i ppf ")\n";
  | Ppat_array (l) ->
      (*
      line i ppf "Ppat_array\n";
      list i pattern ppf l;
       *)
      assert false;
  | Ppat_or (p1, p2) ->
      line i ppf "(P_or\n";
      pattern i ppf p1;
      pattern i ppf p2;
      line i ppf ")\n";
  | Ppat_constraint (p, ct) ->
      line i ppf "(P_typed\n";
      pattern i ppf p;
      core_type i ppf ct;
      line i ppf ")\n";
  | Ppat_type li ->
      (*
      line i ppf "PPat_type";
      longident i ppf li
       *)
      assert false

and expression i ppf x =
  let i = i+1 in
  match x.pexp_desc with
  | Pexp_ident (li) -> line i ppf "(Expr_ident (VN_id %a))\n" fmt_longident li;
  | Pexp_constant (c) -> line i ppf "(Expr_constant %a)\n" fmt_constant c;
  | Pexp_let (rf, l, e) ->
      (match rf with
           Nonrecursive -> 
             (match l with
                  [x] ->
                    line i ppf "(Expr_let\n";
                    line i ppf "(LB_simple\n";
                    pattern_x_expression_def i ppf x;
                    line i ppf ")\n";
                    expression i ppf e;
                    line i ppf ")\n";
                | _ -> assert false)
         | Recursive ->
             line i ppf "(Expr_letrec (LRBs_inj\n";
             list (i+1) pattern_x_expression_rec_def ppf l;
             line i ppf ")\n";
             expression i ppf e;
             line i ppf ")\n";
         | Default -> assert false)
  | Pexp_function (p, eo, l) ->
      (match (p, eo) with
           ("", None) -> 
             line i ppf "(Expr_function (PM_pm\n";
             list i pattern_x_expression_case ppf l;
             line i ppf "))\n";
         | _ -> assert false)
  | Pexp_apply ({pexp_desc=Pexp_ident (Longident.Lident "&&")}, 
                ["",e1; "",e2]) ->
      line i ppf "(Expr_and\n";
      expression (i+1) ppf e1;
      expression (i+1) ppf e2;
      line i ppf ")\n";
  | Pexp_apply ({pexp_desc=Pexp_ident (Longident.Lident "||")}, 
                ["",e1; "",e2]) ->
      line i ppf "(Expr_or\n";
      expression (i+1) ppf e1;
      expression (i+1) ppf e2;
      line i ppf ")\n";
  | Pexp_apply (e, l) ->
      (match l with
           [] -> assert false;
         | [l_x_e] -> 
             line i ppf "(Expr_apply\n";
             expression i ppf e;
             label_x_expression i ppf l_x_e;
             line i ppf ")\n";
         | (h::t) -> 
             expression i ppf 
               {pexp_desc=Pexp_apply ({pexp_desc=Pexp_apply (e, [h]); 
                                       pexp_loc = none},
                                      t);
                        pexp_loc= none});
  | Pexp_match (e, l) ->
      line i ppf "(Expr_match\n";
      expression i ppf e;
      line (i+1) ppf "(PM_pm\n";
      list (i+2) pattern_x_expression_case ppf l;
      line i ppf "))\n";
  | Pexp_try (e, l) ->
      line i ppf "(Expr_try\n";
      expression i ppf e;
      line (i+1) ppf "(PM_pm\n";
      list (i+2) pattern_x_expression_case ppf l;
      line i ppf "))\n";
  | Pexp_tuple (l) ->
      line i ppf "(Expr_tuple\n";
      list i expression ppf l;
      line i ppf ")\n";
  | Pexp_construct (li, eo, b) ->
      (match (li,eo) with
           (Longident.Lident "false", None) ->
             line i ppf "(Expr_constant CONST_false)\n"
         | (Longident.Lident "true", None) ->
             line i ppf "(Expr_constant CONST_true)\n"
         | (Longident.Lident "[]", None) -> 
             line i ppf "(Expr_constant CONST_nil)\n"
         | (Longident.Lident "()", None) -> 
             line i ppf "(Expr_constant CONST_unit)\n"
         | (Longident.Lident c, None) -> 
             line i ppf "(Expr_constant (CONST_constr %a))\n" fmt_constr c
         | (Longident.Lident "::", Some {pexp_desc=Pexp_tuple [e1; e2]}) ->
             line i ppf "(Expr_cons\n";
             expression (i+1) ppf e1;
             expression (i+1) ppf e2;
             line i ppf ")\n";
         | (Longident.Lident c, Some arg) ->
             line i ppf "(Expr_construct %a" fmt_constr c;
             (match arg.pexp_desc with
                  Pexp_tuple exps -> list (i + 1) expression ppf exps
                | _ -> list (i + 1) expression ppf [arg]);
             line i ppf ")\n";
         | _ -> assert false)
  | Pexp_variant (l, eo) ->
      (*
      line i ppf "Pexp_variant \"%s\"\n" l;
      option i expression ppf eo;
       *)
      assert false;
  | Pexp_record (l, eo) ->
      (match eo with
           Some e -> 
             line i ppf "(Expr_override\n";
             expression i ppf e;
             list (i+1) longident_x_expression ppf l;
             line i ppf ")\n";
         | None -> 
             line i ppf "(Expr_record\n";
             list (i+1) longident_x_expression ppf l;
             line i ppf ")\n";)
  | Pexp_field (e, li) ->
      line i ppf "(Expr_field\n";
      expression i ppf e;
      line (i+1) ppf "(F_name (FN_id %a))\n" fmt_longident li;
      line i ppf ")\n";
  | Pexp_setfield (e1, li, e2) ->
      (*
      line i ppf "Pexp_setfield\n";
      expression i ppf e1;
      longident i ppf li;
      expression i ppf e2;
       *)
      assert false;
  | Pexp_array (l) ->
      (*
      line i ppf "Pexp_array\n";
      list i expression ppf l;
       *)
      assert false;
  | Pexp_ifthenelse (e1, e2, eo) ->
      line i ppf "(Expr_ifthenelse\n";
      expression i ppf e1;
      expression i ppf e2;
      (match eo with
           None -> line i ppf "(Expr_constant CONST_unit)\n";
         | Some e -> expression i ppf e);
      line i ppf ")\n";
  | Pexp_sequence (e1, e2) ->
      line i ppf "(Expr_sequence\n";
      expression i ppf e1;
      expression i ppf e2;
      line i ppf ")\n";
  | Pexp_while (e1, e2) ->
      line i ppf "(Expr_while\n";
      expression i ppf e1;
      expression i ppf e2;
      line i ppf ")\n";
  | Pexp_for (s, e1, e2, df, e3) ->
      line i ppf "(Expr_for (VN_id \"%s\")\n" s;
      expression i ppf e1;
      line i ppf "%a\n" fmt_direction_flag df;
      expression i ppf e2;
      expression i ppf e3;
      line i ppf ")\n";
  | Pexp_constraint (e, cto1, cto2) ->
      line i ppf "(Expr_typed\n";
      expression i ppf e;
      (match (cto1, cto2) with
           (Some t, None) -> core_type i ppf t
         | _ -> assert false);
      line i ppf ")\n";
  | Pexp_when (e1, e2) ->
      (*
      line i ppf "Pexp_when\n";
      expression i ppf e1;
      expression i ppf e2;
       *)
      assert false;
  | Pexp_send (e, s) ->
      (*
      line i ppf "Pexp_send \"%s\"\n" s;
      expression i ppf e;
       *)
      assert false;
  | Pexp_new (li) -> (*line i ppf "Pexp_new %a\n" fmt_longident li;*)
      assert false;
  | Pexp_setinstvar (s, e) ->
      (*
      line i ppf "Pexp_setinstvar \"%s\"\n" s;
      expression i ppf e;
       *)
      assert false;
  | Pexp_override (l) ->
      (*
      line i ppf "Pexp_override\n";
      list i string_x_expression ppf l;
       *)
      assert false;
  | Pexp_letmodule (s, me, e) ->
      (*
      line i ppf "Pexp_letmodule \"%s\"\n" s;
      module_expr i ppf me;
      expression i ppf e;
       *)
      assert false;
  | Pexp_assert (e) ->
      line i ppf "(Expr_assert";
      expression i ppf e;
      line i ppf ")\n"
  | Pexp_assertfalse ->
      line i ppf "(Expr_assert (Expr_constant CONST_false))\n";
  | Pexp_lazy (e) ->
      (*
      line i ppf "Pexp_lazy";
      expression i ppf e;
       *)
      assert false
  | Pexp_poly (e, cto) ->
      (*
      line i ppf "Pexp_poly\n";
      expression i ppf e;
      option i core_type ppf cto;
       *)
      assert false;
  | Pexp_object s ->
      (*
      line i ppf "Pexp_object";
      class_structure i ppf s
       *)
      assert false;

and value_description i ppf x =
  line i ppf "value_description\n";
  core_type (i+1) ppf x.pval_type;
  list (i+1) string ppf x.pval_prim;

and type_declaration i ppf x =
  assert (x.ptype_cstrs = []);
  match x.ptype_manifest with
      None -> 
        line i ppf "(TI_def\n";
        type_kind (i+1) ppf x.ptype_kind;
        line i ppf ")\n";
    | _ -> assert false

and type_kind i ppf x =
  match x with
  | Ptype_abstract ->
      (*
      line i ppf "Ptype_abstract\n"
       *)
      assert false;
  | Ptype_variant (l, priv) ->
      line i ppf "(TR_variant\n";
      list (i+1) string_x_core_type_list_x_location ppf l;
      line i ppf ")\n";
  | Ptype_record (l, priv) ->
      line i ppf "Ptype_record %a\n" fmt_private_flag priv;
      list (i+1) string_x_mutable_flag_x_core_type_x_location ppf l;
  | Ptype_private ->
      (*
      line i ppf "Ptype_private\n"
       *)
      assert false;

and exception_declaration i ppf x = list i core_type ppf x

and class_type i ppf x =
  line i ppf "class_type %a\n" fmt_location x.pcty_loc;
  let i = i+1 in
  match x.pcty_desc with
  | Pcty_constr (li, l) ->
      line i ppf "Pcty_constr %a\n" fmt_longident li;
      list i core_type ppf l;
  | Pcty_signature (cs) ->
      line i ppf "Pcty_signature\n";
      class_signature i ppf cs;
  | Pcty_fun (l, co, cl) ->
      line i ppf "Pcty_fun \"%s\"\n" l;
      core_type i ppf co;
      class_type i ppf cl;

and class_signature i ppf (ct, l) =
  line i ppf "class_signature\n";
  core_type (i+1) ppf ct;
  list (i+1) class_type_field ppf l;

and class_type_field i ppf x =
  match x with
  | Pctf_inher (ct) ->
      line i ppf "Pctf_inher\n";
      class_type i ppf ct;
  | Pctf_val (s, mf, vf, ct, loc) ->
      line i ppf
        "Pctf_val \"%s\" %a %a %a\n" s
        fmt_mutable_flag mf fmt_virtual_flag vf fmt_location loc;
      core_type (i+1) ppf ct;
  | Pctf_virt (s, pf, ct, loc) ->
      line i ppf
        "Pctf_virt \"%s\" %a %a\n" s fmt_private_flag pf fmt_location loc;
      core_type (i+1) ppf ct;
  | Pctf_meth (s, pf, ct, loc) ->
      line i ppf
        "Pctf_meth \"%s\" %a %a\n" s fmt_private_flag pf fmt_location loc;
      core_type (i+1) ppf ct;
  | Pctf_cstr (ct1, ct2, loc) ->
      line i ppf "Pctf_cstr %a\n" fmt_location loc;
      core_type i ppf ct1;
      core_type i ppf ct2;

and class_description i ppf x =
  line i ppf "class_description %a\n" fmt_location x.pci_loc;
  let i = i+1 in
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.pci_virt;
  line i ppf "pci_params =\n";
  string_list_x_location (i+1) ppf x.pci_params;
  line i ppf "pci_name = \"%s\"\n" x.pci_name;
  line i ppf "pci_expr =\n";
  class_type (i+1) ppf x.pci_expr;

and class_type_declaration i ppf x =
  line i ppf "class_type_declaration %a\n" fmt_location x.pci_loc;
  let i = i+1 in
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.pci_virt;
  line i ppf "pci_params =\n";
  string_list_x_location (i+1) ppf x.pci_params;
  line i ppf "pci_name = \"%s\"\n" x.pci_name;
  line i ppf "pci_expr =\n";
  class_type (i+1) ppf x.pci_expr;

and class_expr i ppf x =
  line i ppf "class_expr %a\n" fmt_location x.pcl_loc;
  let i = i+1 in
  match x.pcl_desc with
  | Pcl_constr (li, l) ->
      line i ppf "Pcl_constr %a\n" fmt_longident li;
      list i core_type ppf l;
  | Pcl_structure (cs) ->
      line i ppf "Pcl_structure\n";
      class_structure i ppf cs;
  | Pcl_fun (l, eo, p, e) ->
      line i ppf "Pcl_fun\n";
      label i ppf l;
      option i expression ppf eo;
      pattern i ppf p;
      class_expr i ppf e;
  | Pcl_apply (ce, l) ->
      line i ppf "Pcl_apply\n";
      class_expr i ppf ce;
      list i label_x_expression ppf l;
  | Pcl_let (rf, l, ce) ->
      line i ppf "Pcl_let %a\n" fmt_rec_flag rf;
      list i pattern_x_expression_def ppf l;
      class_expr i ppf ce;
  | Pcl_constraint (ce, ct) ->
      line i ppf "Pcl_constraint\n";
      class_expr i ppf ce;
      class_type i ppf ct;

and class_structure i ppf (p, l) =
  line i ppf "class_structure\n";
  pattern (i+1) ppf p;
  list (i+1) class_field ppf l;

and class_field i ppf x =
  match x with
  | Pcf_inher (ce, so) ->
      line i ppf "Pcf_inher\n";
      class_expr (i+1) ppf ce;
      option (i+1) string ppf so;
  | Pcf_valvirt (s, mf, ct, loc) ->
      line i ppf
        "Pcf_valvirt \"%s\" %a %a\n" s fmt_mutable_flag mf fmt_location loc;
      core_type (i+1) ppf ct;
  | Pcf_val (s, mf, e, loc) ->
      line i ppf
        "Pcf_val \"%s\" %a %a\n" s fmt_mutable_flag mf fmt_location loc;
      expression (i+1) ppf e;
  | Pcf_virt (s, pf, ct, loc) ->
      line i ppf
        "Pcf_virt \"%s\" %a %a\n" s fmt_private_flag pf fmt_location loc;
      core_type (i+1) ppf ct;
  | Pcf_meth (s, pf, e, loc) ->
      line i ppf
        "Pcf_meth \"%s\" %a %a\n" s fmt_private_flag pf fmt_location loc;
      expression (i+1) ppf e;
  | Pcf_cstr (ct1, ct2, loc) ->
      line i ppf "Pcf_cstr %a\n" fmt_location loc;
      core_type (i+1) ppf ct1;
      core_type (i+1) ppf ct2;
  | Pcf_let (rf, l, loc) ->
      line i ppf "Pcf_let %a %a\n" fmt_rec_flag rf fmt_location loc;
      list (i+1) pattern_x_expression_def ppf l;
  | Pcf_init (e) ->
      line i ppf "Pcf_init\n";
      expression (i+1) ppf e;

and class_declaration i ppf x =
  line i ppf "class_declaration %a\n" fmt_location x.pci_loc;
  let i = i+1 in
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.pci_virt;
  line i ppf "pci_params =\n";
  string_list_x_location (i+1) ppf x.pci_params;
  line i ppf "pci_name = \"%s\"\n" x.pci_name;
  line i ppf "pci_expr =\n";
  class_expr (i+1) ppf x.pci_expr;

and module_type i ppf x =
  line i ppf "module_type %a\n" fmt_location x.pmty_loc;
  let i = i+1 in
  match x.pmty_desc with
  | Pmty_ident (li) -> line i ppf "Pmty_ident %a\n" fmt_longident li;
  | Pmty_signature (s) ->
      line i ppf "Pmty_signature\n";
      signature i ppf s;
  | Pmty_functor (s, mt1, mt2) ->
      line i ppf "Pmty_functor \"%s\"\n" s;
      module_type i ppf mt1;
      module_type i ppf mt2;
  | Pmty_with (mt, l) ->
      line i ppf "Pmty_with\n";
      module_type i ppf mt;
      list i longident_x_with_constraint ppf l;

and signature i ppf x = list i signature_item ppf x

and signature_item i ppf x =
  line i ppf "signature_item %a\n" fmt_location x.psig_loc;
  let i = i+1 in
  match x.psig_desc with
  | Psig_value (s, vd) ->
      line i ppf "Psig_value \"%s\"\n" s;
      value_description i ppf vd;
  | Psig_type (l) ->
      line i ppf "Psig_type\n";
      list i string_x_type_declaration ppf l;
  | Psig_exception (s, ed) ->
      line i ppf "Psig_exception \"%s\"\n" s;
      exception_declaration i ppf ed;
  | Psig_module (s, mt) ->
      line i ppf "Psig_module \"%s\"\n" s;
      module_type i ppf mt;
  | Psig_recmodule decls ->
      line i ppf "Psig_recmodule\n";
      list i string_x_module_type ppf decls;
  | Psig_modtype (s, md) ->
      line i ppf "Psig_modtype \"%s\"\n" s;
      modtype_declaration i ppf md;
  | Psig_open (li) -> line i ppf "Psig_open %a\n" fmt_longident li;
  | Psig_include (mt) ->
      line i ppf "Psig_include\n";
      module_type i ppf mt;
  | Psig_class (l) ->
      line i ppf "Psig_class\n";
      list i class_description ppf l;
  | Psig_class_type (l) ->
      line i ppf "Psig_class_type\n";
      list i class_type_declaration ppf l;

and modtype_declaration i ppf x =
  match x with
  | Pmodtype_abstract -> line i ppf "Pmodtype_abstract\n";
  | Pmodtype_manifest (mt) ->
      line i ppf "Pmodtype_manifest\n";
      module_type (i+1) ppf mt;

and with_constraint i ppf x =
  match x with
  | Pwith_type (td) ->
      line i ppf "Pwith_type\n";
      type_declaration (i+1) ppf td;
  | Pwith_module (li) -> line i ppf "Pwith_module %a\n" fmt_longident li;

and module_expr i ppf x =
  line i ppf "module_expr %a\n" fmt_location x.pmod_loc;
  let i = i+1 in
  match x.pmod_desc with
  | Pmod_ident (li) -> line i ppf "Pmod_ident %a\n" fmt_longident li;
  | Pmod_structure (s) ->
      line i ppf "Pmod_structure\n";
      structure i ppf s;
  | Pmod_functor (s, mt, me) ->
      line i ppf "Pmod_functor \"%s\"\n" s;
      module_type i ppf mt;
      module_expr i ppf me;
  | Pmod_apply (me1, me2) ->
      line i ppf "Pmod_apply\n";
      module_expr i ppf me1;
      module_expr i ppf me2;
  | Pmod_constraint (me, mt) ->
      line i ppf "Pmod_constraint\n";
      module_expr i ppf me;
      module_type i ppf mt;

and structure i ppf x = list i structure_item ppf x

and structure_item i ppf x =
  let i = i+1 in
  match x.pstr_desc with
  | Pstr_eval (e) ->
      expression i ppf e;
  | Pstr_value (rf, l) ->
      (match rf with
           Nonrecursive -> 
             (match l with
                  [x] ->
                    line i ppf "(D_let\n";
                    line (i+1) ppf "(LB_simple\n";
                    pattern_x_expression_def i ppf x;
                    line i ppf "))\n";
                | _ -> assert false)
         | Recursive ->
             line i ppf "(D_letrec (LRBs_inj\n";
             list (i+1) pattern_x_expression_rec_def ppf l;
             line i ppf "))\n";
         | Default -> assert false)
  | Pstr_primitive (s, vd) ->
      (*
      line i ppf "Pstr_primitive \"%s\"\n" s;
      value_description i ppf vd;
       *)
      assert false;
  | Pstr_type (l) ->
      line i ppf "(D_type (TDF_tdf\n";
      list i string_x_type_declaration ppf l;
      line i ppf "))\n";
  | Pstr_exception (s, ed) ->
      line i ppf "Pstr_exception \"%s\"\n" s;
      exception_declaration i ppf ed;
  | Pstr_exn_rebind (s, li) ->
      (*
      line i ppf "Pstr_exn_rebind \"%s\" %a\n" s fmt_longident li;
       *)
      assert false;
  | Pstr_module (s, me) ->
      (*
      line i ppf "Pstr_module \"%s\"\n" s;
      module_expr i ppf me;
       *)
      assert false;
  | Pstr_recmodule bindings ->
      (*
      line i ppf "Pstr_recmodule\n";
      list i string_x_modtype_x_module ppf bindings;
       *)
      assert false;
  | Pstr_modtype (s, mt) ->
      (*
      line i ppf "Pstr_modtype \"%s\"\n" s;
      module_type i ppf mt;
       *)
      assert false;
  | Pstr_open (li) -> (*line i ppf "Pstr_open %a\n" fmt_longident li;*)
      assert false;
  | Pstr_class (l) ->
      (*
      line i ppf "Pstr_class\n";
      list i class_declaration ppf l;
       *)
      assert false;
  | Pstr_class_type (l) ->
      (*
      line i ppf "Pstr_class_type\n";
      list i class_type_declaration ppf l;
       *)
      assert false;
  | Pstr_include me ->
      (*
      line i ppf "Pstr_include";
      module_expr i ppf me
       *)
      assert false;

and tpo i ppf s = 
  line i ppf "(TP_var (TV_ident \"%s\"))" s;

and string_x_type_declaration i ppf (s, td) =
  line i ppf "(TD_td (TPS_nary\n";
  list i tpo ppf td.ptype_params;
  line i ppf ")\n";
  line (i+1) ppf "(TCN_id \"%s\")\n" s;
  type_declaration (i+1) ppf td;
  line i ppf ")\n";

and string_x_module_type i ppf (s, mty) =
  string i ppf s;
  module_type (i+1) ppf mty;

and string_x_modtype_x_module i ppf (s, mty, modl) =
  string i ppf s;
  module_type (i+1) ppf mty;
  module_expr (i+1) ppf modl;

and longident_x_with_constraint i ppf (li, wc) =
  line i ppf "%a\n" fmt_longident li;
  with_constraint (i+1) ppf wc;

and core_type_x_core_type_x_location i ppf (ct1, ct2, l) =
  line i ppf "<constraint> %a\n" fmt_location l;
  core_type (i+1) ppf ct1;
  core_type (i+1) ppf ct2;

and string_x_core_type_list_x_location i ppf (s, l, loc) =
  match l with 
      [] -> 
        line i ppf "(CD_nullary (CN_id \"%s\"))\n" s;
    | _ -> 
        line i ppf "(CD_nary (CN_id \"%s\")\n" s;
        list (i+1) core_type ppf l;
        line i ppf ")\n";

and string_x_mutable_flag_x_core_type_x_location i ppf (s, mf, ct, loc) =
  line i ppf "\"%s\" %a %a\n" s fmt_mutable_flag mf fmt_location loc;
  core_type (i+1) ppf ct;

and string_list_x_location i ppf (l, loc) =
  line i ppf "<params> %a\n" fmt_location loc;
  list (i+1) string ppf l;

and longident_x_pattern i ppf (li, p) =
  line i ppf "(F_name (FN_id %a), \n" fmt_longident li;
  pattern i ppf p;
  line i ppf ")";

and pattern_x_expression_case i ppf (p, e) =
  line i ppf "(PE_inj \n";
  pattern (i+1) ppf  p;
  expression (i+1) ppf e;
  line i ppf ")\n"

and pattern_x_expression_def i ppf (p, e) =
  pattern (i+1) ppf p;
  expression (i+1) ppf e;

and pattern_x_expression_rec_def i ppf (p, e) =
  match (p.ppat_desc, e.pexp_desc) with
      (Ppat_var v, Pexp_function ("", None, l)) ->
        line i ppf "(LRB_simple\n";
        line (i+1) ppf "(VN_id \"%s\")\n" v;
        line (i+1) ppf "(PM_pm\n";
        list (i+1) pattern_x_expression_case ppf l;
        line (i+1) ppf ")\n";
        line i ppf ")\n";
    | _ -> assert false;

and string_x_expression i ppf (s, e) =
  line i ppf "<override> \"%s\"\n" s;
  expression (i+1) ppf e;

and longident_x_expression i ppf (li, e) =
  line i ppf "(F_name (FN_id %a), \n" fmt_longident li;
  expression i ppf e;
  line i ppf ")\n";

and label_x_expression i ppf (l,e) =
  assert (l = "");
  expression (i+1) ppf e;

and label_x_bool_x_core_type_list i ppf x =
  match x with
    Rtag (l, b, ctl) ->
      line i ppf "Rtag \"%s\" %s\n" l (string_of_bool b);
      list (i+1) core_type ppf ctl
  | Rinherit (ct) ->
      line i ppf "Rinherit\n";
      core_type (i+1) ppf ct
;;

let rec toplevel_phrase i ppf x =
  match x with
  | Ptop_def (s) ->
      line i ppf "Ptop_def\n";
      structure (i+1) ppf s;
  | Ptop_dir (s, da) ->
      line i ppf "Ptop_dir \"%s\"\n" s;
      directive_argument i ppf da;

and directive_argument i ppf x =
  match x with
  | Pdir_none -> line i ppf "Pdir_none\n"
  | Pdir_string (s) -> line i ppf "Pdir_string \"%s\"\n" s;
  | Pdir_int (i) -> line i ppf "Pdir_int %d\n" i;
  | Pdir_ident (li) -> line i ppf "Pdir_ident %a\n" fmt_longident li;
  | Pdir_bool (b) -> line i ppf "Pdir_bool %s\n" (string_of_bool b);
;;

let interface ppf x = list 0 signature_item ppf x;;

let implementation ppf x = 
match x with
    (* special handling for a single expression *)
    [{pstr_desc=Pstr_eval e}] -> expression 0 ppf e
  | _ -> list 0 structure_item ppf x;;

let top_phrase ppf x = toplevel_phrase 0 ppf x;;
