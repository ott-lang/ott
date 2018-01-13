(* Has the following bugs:
* Some uses of constructors as values must be eta-expanded by hand to 
*   curry them.
* There is a pattern that binds v63 twice.
*
* The real type for floats might be an equality type, which harms the pattern
* matcher.
* *)


load "wordsLib";
load "ottTheory";
load "ottLib";
load "caml_typedefTheory";
load "utilTheory";
load "shiftTheory";
load "basicTheory";
load "defs_red_funTheory";

quietdec:=true;
open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory reduction_funTheory matching_funTheory
open defs_red_funTheory;
quietdec:=false;


val list_to_defs_def = Define
`(list_to_defs [] = Ds_nil) /\
 (list_to_defs (x::y) = Ds_cons x (list_to_defs y))`;

val _ =
 let open EmitML combinSyntax
 in emitML (".")
     ("ott",
      MLSIG "type num = numML.num"   ::
      MLSIG "type capitalized_ident = string" ::
      MLSTRUCT "type capitalized_ident = string" ::
      OPEN ["num", "list", "string"] ::
      map DEFN [list_minus_def,list_assoc_def,clause_name_def,REMOVE_1_def,
                PERM_EVAL])
 end;

val _ = disable_tyabbrev_printing "labelled_arrow";

val _ = type_pp.pp_num_types := false;
val _ = type_pp.pp_array_types := false;

val _ =
 let open EmitML combinSyntax
 in emitML (".")
     ("caml_typedef",
      MLSIG "type string = stringML.string"   ::
      MLSIG "type num = numML.num"   ::
      MLSIG "type index = num" ::
      MLSIG "type ident = string" ::
      MLSIG "type string_literal = string"  ::
      MLSIG "type infix_symbol = string" ::
      MLSIG "type prefix_symbol = string" ::
      MLSIG "type lowercase_ident = string" ::
      MLSIG "type capitalized_ident = string" ::
      MLSIG "type integer_literal = int" ::
      MLSIG "type float_literal = unit" ::
      MLSIG "type char_literal = char" ::
      MLSIG "type location = num" ::
      MLSIG "type idx = num" ::
      MLSIG "type word31 = unit wordsML.bit1 wordsML.bit1 wordsML.bit1 wordsML.bit1 wordsML.word" ::
      MLSIG "type intn = word31" ::
      MLSIG "type kind = num" ::
(*
      MLSIG "type names = name list" ::
      MLSIG "type Tsigma = (typevar * typexpr) list" ::
*)

      MLSTRUCT "type string = stringML.string"   ::
      MLSTRUCT "type num = numML.num"   ::
      MLSTRUCT "type index = num" ::
      MLSTRUCT "type ident = string" ::
      MLSTRUCT "type string_literal = string"  ::
      MLSTRUCT "type infix_symbol = string" ::
      MLSTRUCT "type prefix_symbol = string" ::
      MLSTRUCT "type lowercase_ident = string" ::
      MLSTRUCT "type capitalized_ident = string" ::
      MLSTRUCT "type integer_literal = int" :: 
      MLSTRUCT "type float_literal = unit" ::
      MLSTRUCT "type char_literal = char" ::
      MLSTRUCT "type location = num" ::
      MLSTRUCT "type idx = num" ::
      MLSTRUCT "type word31 = unit wordsML.bit1 wordsML.bit1 wordsML.bit1 wordsML.bit1 wordsML.word" ::
      MLSTRUCT "type intn = word31" ::
      MLSTRUCT "type kind = num" ::

      OPEN ["num", "list", "string", "option"] ::
      DATATYPE `typeconstr_name = TCN_id of lowercase_ident` ::
      DATATYPE `typeconstr = 
           TC_name of typeconstr_name
         | TC_int
         | TC_char
         | TC_string
         | TC_float
         | TC_bool
         | TC_unit
         | TC_exn
         | TC_list
         | TC_option
         | TC_ref`   :: 
      DATATYPE `typevar = TV_ident of ident` ::
      DATATYPE `constr_name = CN_id of capitalized_ident` ::
      DATATYPE `typexpr = 
           TE_var of typevar
         | TE_idxvar of idx => idx
         | TE_any
         | TE_arrow of typexpr => typexpr
         | TE_tuple of typexpr list
         | TE_constr of typexpr list => typeconstr` ::
      MLSIG "type Tsigma = (typevar * typexpr) list" ::
      MLSTRUCT "type Tsigma = (typevar * typexpr) list" ::
      DATATYPE `field_name = FN_id of lowercase_ident` ::
      DATATYPE `infix_op = 
           IO_symbol of infix_symbol
         | IO_star
         | IO_equal
         | IO_colonequal` ::
      DATATYPE `constr_decl = 
           CD_nullary of constr_name
         | CD_nary of constr_name => typexpr list` ::
      DATATYPE `field_decl = FD_immutable of field_name => typexpr` ::
      DATATYPE `operator_name = 
           ON_symbol of prefix_symbol
         | ON_infix of infix_op` ::
      DATATYPE `constr = 
           C_name of constr_name
         | C_invalidargument
         | C_notfound
         | C_assertfailure
         | C_matchfailure
         | C_div_by_0
         | C_none
         | C_some`  :: 
      DATATYPE `type_equation = TE_te of typexpr` ::
      DATATYPE `type_representation = 
           TR_variant of constr_decl list
         | TR_record of field_decl list` ::
      DATATYPE `type_param = TP_var of typevar` ::
      DATATYPE `value_name = 
           VN_id of lowercase_ident
         | VN_op of operator_name` ::
      DATATYPE `field = F_name of field_name` ::
      DATATYPE `constant = 
           CONST_int of intn
         | CONST_float of float_literal
         | CONST_char of char_literal
         | CONST_string of string_literal
         | CONST_constr of constr
         | CONST_false
         | CONST_true
         | CONST_nil
         | CONST_unit` ::
      DATATYPE `type_information = 
           TI_eq of type_equation
         | TI_def of type_representation` ::
      DATATYPE `type_params_opt = TPS_nary of type_param list` ::
      DATATYPE `pattern = 
           P_var of value_name
         | P_any
         | P_constant of constant
         | P_alias of pattern => value_name
         | P_typed of pattern => typexpr
         | P_or of pattern => pattern
         | P_construct of constr => pattern list
         | P_construct_any of constr
         | P_tuple of pattern list
         | P_record of (field#pattern) list
         | P_cons of pattern => pattern` ::
        DATATYPE `unary_prim = 
           Uprim_raise
         | Uprim_not
         | Uprim_minus
         | Uprim_ref
         | Uprim_deref` ::
        DATATYPE `binary_prim = 
           Bprim_equal
         | Bprim_plus
         | Bprim_minus
         | Bprim_times
         | Bprim_div
         | Bprim_assign` ::
        DATATYPE `for_dirn = 
           FD_upto
         | FD_downto` ::
        DATATYPE `typedef = 
                   TD_td of type_params_opt => typeconstr_name => type_information` ::

        DATATYPE `letrec_binding = LRB_simple of value_name => pattern_matching;
                  letrec_bindings = LRBs_inj of letrec_binding list;
                  let_binding = LB_simple of pattern => expr;
                  pat_exp = PE_inj of pattern => expr;
                  pattern_matching = PM_pm of pat_exp list;
                  expr = 
           Expr_uprim of unary_prim
         | Expr_bprim of binary_prim
         | Expr_ident of value_name
         | Expr_constant of constant
         | Expr_typed of expr => typexpr
         | Expr_tuple of expr list
         | Expr_construct of constr => expr list
         | Expr_cons of expr => expr
         | Expr_record of (field#expr) list
         | Expr_override of expr => (field#expr) list
         | Expr_apply of expr => expr
         | Expr_and of expr => expr
         | Expr_or of expr => expr
         | Expr_field of expr => field
         | Expr_ifthenelse of expr => expr => expr
         | Expr_while of expr => expr
         | Expr_for of value_name => expr => for_dirn => expr => expr
         | Expr_sequence of expr => expr
         | Expr_match of expr => pattern_matching
         | Expr_function of pattern_matching
         | Expr_try of expr => pattern_matching
         | Expr_let of let_binding => expr
         | Expr_letrec of letrec_bindings => expr
         | Expr_assert of expr
         | Expr_location of location` ::
        DATATYPE `type_definition = TDF_tdf of typedef list` ::
        DATATYPE `exception_definition = ED_def of constr_decl` ::
        DATATYPE `definition = 
           D_let of let_binding
         | D_letrec of letrec_bindings
         | D_type of type_definition
         | D_exception of exception_definition` ::
        DATATYPE `typescheme = TS_forall of typexpr` ::
        DATATYPE `typexprs = typexprs_inj of typexpr list` ::
        DATATYPE `trans_label = 
           Lab_nil
         | Lab_alloc of expr => location
         | Lab_deref of location => expr
         | Lab_assign of location => expr` ::
        DATATYPE `definitions = 
           Ds_nil
         | Ds_cons of definition => definitions` ::
        DATATYPE `name = 
           name_tv
         | name_vn of value_name
         | name_cn of constr_name
         | name_tcn of typeconstr_name
         | name_fn of field_name
         | name_l of location` ::
        DATATYPE `environment_binding = 
           EB_tv
         | EB_vn of value_name => typescheme
         | EB_cc of constr_name => typeconstr
         | EB_pc of constr_name => type_params_opt => typexprs => typeconstr
         | EB_fn of field_name => type_params_opt => typeconstr_name => typexpr
         | EB_td of typeconstr_name => kind
         | EB_tr of typeconstr_name => kind => field_name list
         | EB_ta of type_params_opt => typeconstr_name => typexpr
         | EB_l of location => typexpr` ::
         
        MLSIG "type environment = environment_binding list" ::
        MLSTRUCT "type environment = environment_binding list" ::
        DATATYPE `program = 
           Prog_defs of definitions
         | Prog_raise of expr` ::
        DATATYPE `substs_x = substs_x_xs of (value_name#expr) list` ::
        DATATYPE `value_path = VP_name of value_name` ::

        MLSIG "type store = (location * expr) list" ::
        MLSTRUCT "type store = (location * expr) list" ::

      map DEFN
      [is_binary_prim_app_value_of_expr_def,
       is_definition_value_of_definition_def,
       caml_typedefTheory.is_value_of_expr_def,
       is_non_expansive_of_expr_def,
       is_src_typexpr_of_typexpr_def,
       is_definitions_value_of_definitions_def,
       is_trans_label_of_trans_label_def,
       aux_constr_names_constr_decl_of_constr_decl_def,
       aux_constr_names_type_representation_of_type_representation_def,
       aux_constr_names_type_information_of_type_information_def,
       aux_field_names_field_decl_of_field_decl_def,
       aux_xs_pattern_of_pattern_def,
       aux_xs_letrec_binding_of_letrec_binding_def,
       aux_constr_names_typedef_of_typedef_def,
       aux_field_names_type_representation_of_type_representation_def,
       aux_type_names_typedef_of_typedef_def,
       aux_typevars_type_param_of_type_param_def, 
       aux_xs_let_binding_of_let_binding_def,
       aux_xs_letrec_bindings_of_letrec_bindings_def,
       aux_constr_names_type_definition_of_type_definition_def,
       aux_field_names_type_information_of_type_information_def,
       aux_type_names_type_definition_of_type_definition_def,
       aux_typevars_type_params_opt_of_type_params_opt_def,
       aux_xs_definition_of_definition_def,
       ftv_typexpr_def,
       ftv_constr_decl_def, 
       ftv_field_decl_def,
       ftv_type_equation_def,
       ftv_type_representation_def,
       ftv_type_information_def,
       ftv_pattern_def,
       ftv_typedef_def,
       ftv_letrec_binding_def,
       ftv_type_definition_def,
       ftv_exception_definition_def,
       fv_letrec_binding_def,
       fl_letrec_binding_def,
       ftv_definition_def,
       fv_definition_def,
       fl_definition_def,
       ftv_definitions_def,
       ftv_typescheme_def,
       ftv_typexprs_def,
       fv_definitions_def,
       fl_definitions_def,
       ftv_substs_x_def,
       ftv_program_def,
       ftv_environment_binding_def,
       ftv_trans_label_def,
       fv_substs_x_def,
       fv_program_def,
       fv_trans_label_def,
fl_substs_x_def,
fl_program_def,
fl_trans_label_def,
substs_typevar_typexpr_def,
substs_typevar_constr_decl_def,
substs_typevar_field_decl_def,
substs_typevar_type_equation_def,
substs_typevar_type_representation_def,
substs_typevar_type_information_def,
substs_typevar_pattern_def,
substs_typevar_typedef_def,
substs_typevar_letrec_binding_def,
substs_typevar_type_definition_def,
substs_typevar_exception_definition_def,
substs_value_name_letrec_binding_def,
subst_value_name_letrec_binding_def,
substs_typevar_definition_def,
substs_value_name_definition_def,
subst_value_name_definition_def,
substs_typevar_definitions_def,
substs_typevar_typescheme_def,
substs_typevar_typexprs_def,
substs_value_name_definitions_def,
subst_value_name_definitions_def,
substs_typevar_program_def,
substs_typevar_environment_binding_def,
substs_typevar_trans_label_def,
substs_value_name_substs_x_def,
substs_value_name_program_def,
substs_value_name_trans_label_def,
subst_value_name_substs_x_def,
subst_value_name_program_def,
subst_value_name_trans_label_def,
substs_typevar_substs_x_def,
shiftt_def,
shifttes_def,
shiftts_def,
shiftEB_def,
num_tv_def,
shiftE_def,
shiftTsig_def,
definitions_snoc_def,
remv_tyvar_typexpr_def,
remv_tyvar_pattern_def,
remv_tyvar_letrec_binding_def,
basicTheory.field_to_fn_def,
basicTheory.funval_def,
basicTheory.recfun_def,
basicTheory.lrbs_to_lrblist_def,
list_to_defs_def])
end;

val sigs = 
["type expr = caml_typedefML.expr;",
 "type kind = caml_typedefML.kind;",
 "type unary_prim = caml_typedefML.unary_prim;",
 "type binary_prim = caml_typedefML.binary_prim;",
 "type word31 = caml_typedefML.word31;",
 "type intn = caml_typedefML.intn;",
 "type constant = caml_typedefML.constant;",
 "type field = caml_typedefML.field;",
 "type value_name = caml_typedefML.value_name;",
 "type for_dirn = caml_typedefML.for_dirn;",
 "type pattern_matching = caml_typedefML.pattern_matching;",
 "type pattern = caml_typedefML.pattern;",
 "type letrec_bindings = caml_typedefML.letrec_bindings;",
 "type definitions = caml_typedefML.definitions;",
 "type program = caml_typedefML.program;",
 "type store = caml_typedefML.store;"];

val _ =
 let open EmitML combinSyntax
 in emitML (".")
     ("matching_fun",
      map MLSIG sigs @
      OPEN ["num", "list", "string", "option", "caml_typedef"] ::
      map DEFN [pat_match_def])
 end;

val _ =
 let open EmitML combinSyntax
 in emitML (".")
     ("reduction_fun",
      map MLSIG sigs @
      OPEN ["num", "list", "string", "option", "caml_typedef"] ::
      DATATYPE `result = Stuck
        | Step of 'a
        | StepAlloc of (expr -> 'a) => expr
        | StepLookup of (expr -> 'a) => location 
        | StepAssign of 'a => location => expr` ::
      map (DEFN o wordsLib.WORDS_EMIT_RULE)
               [is_raise_def,
                result_map_def,
                eval_uprim_def,
                b_int_primop_def,
                is_const_constr_def,
                non_funval_equal_def,
                eval_bprim_def,
                do_1override_def,
                eval_override_def,
                eval_apply_def,
                eval_field_def,
                eval_ite_def,
                eval_while_def,
                eval_for_def,
                eval_match_def,
                eval_try_def,
                eval_let_def,
                eval_letrec_def,
                eval_assert_def,
                red_def])
 end;

val _ =
 let open EmitML combinSyntax
 in emitML (".")
     ("defs_red_fun",
      map MLSIG sigs @
      MLSIG "type 'a result = 'a reduction_funML.result;" ::
      OPEN ["num", "list", "string", "option", "caml_typedef", "reduction_fun"] ::
      map DEFN [defns_red_def,
                store_assign_def,
                top_red_def,
                max_alloc_def])
 end;


use "tests.sml";


