structure reduction_funML :> reduction_funML =
struct
  nonfix red_list red_2 red_1 red eval_assert eval_letrec eval_let
         eval_try eval_match eval_for eval_while eval_ite eval_field
         eval_apply eval_override do_1override eval_bprim
         non_funval_equal is_const_constr b_int_primop eval_uprim
         result_map is_raise result_size StepAssign StepLookup StepAlloc
         Step Stuck * / div mod + - ^ @ <> > < >= <= := o before;
  
  open numML listML stringML optionML caml_typedefML;
  datatype 'a result
       = Stuck
       | Step of 'a
       | StepAlloc of (expr -> 'a) * expr
       | StepLookup of (expr -> 'a) * kind
       | StepAssign of 'a * kind * expr
  fun result_size f Stuck = ZERO
    | result_size f (Step(a)) = + ONE (f a)
    | result_size f (StepAlloc(a0,a1)) = + ONE (expr_size a1)
    | result_size f (StepLookup(a0,a1)) = + ONE a1
    | result_size f (StepAssign(a0,a1,a2)) =
        + ONE (+ (f a0) (+ a1 (expr_size a2)))
    
  fun is_raise (Expr_apply(expr1,expr2)) =
        (expr1 = Expr_uprim(Uprim_raise)) andalso is_value_of_expr expr2
    | is_raise (Expr_location(v44)) = false
    | is_raise (Expr_assert(v43)) = false
    | is_raise (Expr_letrec(v41,v42)) = false
    | is_raise (Expr_let(v39,v40)) = false
    | is_raise (Expr_try(v37,v38)) = false
    | is_raise (Expr_function(v36)) = false
    | is_raise (Expr_match(v34,v35)) = false
    | is_raise (Expr_sequence(v32,v33)) = false
    | is_raise (Expr_for(v27,v28,v29,v30,v31)) = false
    | is_raise (Expr_while(v25,v26)) = false
    | is_raise (Expr_ifthenelse(v22,v23,v24)) = false
    | is_raise (Expr_field(v20,v21)) = false
    | is_raise (Expr_or(v18,v19)) = false
    | is_raise (Expr_and(v16,v17)) = false
    | is_raise (Expr_override(v12,v13)) = false
    | is_raise (Expr_record(v11)) = false
    | is_raise (Expr_cons(v9,v10)) = false
    | is_raise (Expr_construct(v7,v8)) = false
    | is_raise (Expr_tuple(v6)) = false
    | is_raise (Expr_typed(v4,v5)) = false
    | is_raise (Expr_constant(v3)) = false
    | is_raise (Expr_ident(v2)) = false
    | is_raise (Expr_bprim(v1)) = false
    | is_raise (Expr_uprim(v)) = false
    
  fun result_map f Stuck = Stuck
    | result_map f (Step(expr)) = Step(f expr)
    | result_map f (StepAlloc(get_result,alloc_expr)) =
        StepAlloc(fn l => f (get_result l),alloc_expr)
    | result_map f (StepLookup(get_result,lookup_lab)) =
        StepLookup(fn e => f (get_result e),lookup_lab)
    | result_map f (StepAssign(result_expr,assign_lab,assign_expr)) =
        StepAssign(f result_expr,assign_lab,assign_expr)
    
  fun eval_uprim Uprim_not v =
        (if v = Expr_constant(CONST_true)
           then Step(Expr_constant(CONST_false))
           else if v = Expr_constant(CONST_false)
                  then Step(Expr_constant(CONST_true)) else Stuck)
    | eval_uprim Uprim_minus v =
        (case v
         of Expr_uprim(v45) => Stuck
          | Expr_bprim(v46) => Stuck
          | Expr_ident(v47) => Stuck
          | Expr_constant(CONST_int(n)) =>
               Step(Expr_constant(CONST_int(wordsML.word_sub
                                              (wordsML.n2w_itself
                                                 (ZERO,(fcpML.ITSELF (numML.fromDecString"31"))))
                                              n)))
          | Expr_constant(CONST_float(v96)) => Stuck
          | Expr_constant(CONST_char(v97)) => Stuck
          | Expr_constant(CONST_string(v98)) => Stuck
          | Expr_constant(CONST_constr(v99)) => Stuck
          | Expr_constant(CONST_false) => Stuck
          | Expr_constant(CONST_true) => Stuck
          | Expr_constant(CONST_nil) => Stuck
          | Expr_constant(CONST_unit) => Stuck
          | Expr_typed(v49,v50) => Stuck
          | Expr_tuple(v51) => Stuck
          | Expr_construct(v52,v53) => Stuck
          | Expr_cons(v54,v55) => Stuck
          | Expr_record(v56) => Stuck
          | Expr_override(v57,v58) => Stuck
          | Expr_apply(v59,v60) => Stuck
          | Expr_and(v61,v62) => Stuck
          | Expr_or(v63,v64) => Stuck
          | Expr_field(v65,v66) => Stuck
          | Expr_ifthenelse(v67,v68,v69) => Stuck
          | Expr_while(v70,v71) => Stuck
          | Expr_for(v72,v73,v74,v75,v76) => Stuck
          | Expr_sequence(v77,v78) => Stuck
          | Expr_match(v79,v80) => Stuck
          | Expr_function(v81) => Stuck
          | Expr_try(v82,v83) => Stuck
          | Expr_let(v84,v85) => Stuck
          | Expr_letrec(v86,v87) => Stuck
          | Expr_assert(v88) => Stuck
          | Expr_location(v89) => Stuck)
    | eval_uprim Uprim_ref v = StepAlloc(fn e => e,v)
    | eval_uprim Uprim_deref v =
        (case v
         of Expr_uprim(v45) => Stuck
          | Expr_bprim(v46) => Stuck
          | Expr_ident(v47) => Stuck
          | Expr_constant(v48) => Stuck
          | Expr_typed(v49,v50) => Stuck
          | Expr_tuple(v51) => Stuck
          | Expr_construct(v52,v53) => Stuck
          | Expr_cons(v54,v55) => Stuck
          | Expr_record(v56) => Stuck
          | Expr_override(v57,v58) => Stuck
          | Expr_apply(v59,v60) => Stuck
          | Expr_and(v61,v62) => Stuck
          | Expr_or(v63,v64) => Stuck
          | Expr_field(v65,v66) => Stuck
          | Expr_ifthenelse(v67,v68,v69) => Stuck
          | Expr_while(v70,v71) => Stuck
          | Expr_for(v72,v73,v74,v75,v76) => Stuck
          | Expr_sequence(v77,v78) => Stuck
          | Expr_match(v79,v80) => Stuck
          | Expr_function(v81) => Stuck
          | Expr_try(v82,v83) => Stuck
          | Expr_let(v84,v85) => Stuck
          | Expr_letrec(v86,v87) => Stuck
          | Expr_assert(v88) => Stuck
          | Expr_location(l) => StepLookup(fn e => e,l))
    | eval_uprim Uprim_raise v = Stuck
    
  fun b_int_primop oper v1 v2 =
        case v1
         of Expr_uprim(v46) => Stuck
          | Expr_bprim(v47) => Stuck
          | Expr_ident(v48) => Stuck
          | Expr_constant(CONST_int(n1)) =>
               (case v2
                of Expr_uprim(v45) => Stuck
                 | Expr_bprim(v46) => Stuck
                 | Expr_ident(v47) => Stuck
                 | Expr_constant(CONST_int(n2)) =>
                      Step(Expr_constant(CONST_int(oper n1 n2)))
                 | Expr_constant(CONST_float(v96)) => Stuck
                 | Expr_constant(CONST_char(v97)) => Stuck
                 | Expr_constant(CONST_string(v98)) => Stuck
                 | Expr_constant(CONST_constr(v99)) => Stuck
                 | Expr_constant(CONST_false) => Stuck
                 | Expr_constant(CONST_true) => Stuck
                 | Expr_constant(CONST_nil) => Stuck
                 | Expr_constant(CONST_unit) => Stuck
                 | Expr_typed(v49,v50) => Stuck
                 | Expr_tuple(v51) => Stuck
                 | Expr_construct(v52,v53) => Stuck
                 | Expr_cons(v54,v55) => Stuck
                 | Expr_record(v56) => Stuck
                 | Expr_override(v57,v58) => Stuck
                 | Expr_apply(v59,v60) => Stuck
                 | Expr_and(v61,v62) => Stuck
                 | Expr_or(v63,v64) => Stuck
                 | Expr_field(v65,v66) => Stuck
                 | Expr_ifthenelse(v67,v68,v69) => Stuck
                 | Expr_while(v70,v71) => Stuck
                 | Expr_for(v72,v73,v74,v75,v76) => Stuck
                 | Expr_sequence(v77,v78) => Stuck
                 | Expr_match(v79,v80) => Stuck
                 | Expr_function(v81) => Stuck
                 | Expr_try(v82,v83) => Stuck
                 | Expr_let(v84,v85) => Stuck
                 | Expr_letrec(v86,v87) => Stuck
                 | Expr_assert(v88) => Stuck
                 | Expr_location(v89) => Stuck)
          | Expr_constant(CONST_float(v97)) => Stuck
          | Expr_constant(CONST_char(v98)) => Stuck
          | Expr_constant(CONST_string(v99)) => Stuck
          | Expr_constant(CONST_constr(v100)) => Stuck
          | Expr_constant(CONST_false) => Stuck
          | Expr_constant(CONST_true) => Stuck
          | Expr_constant(CONST_nil) => Stuck
          | Expr_constant(CONST_unit) => Stuck
          | Expr_typed(v50,v51) => Stuck
          | Expr_tuple(v52) => Stuck
          | Expr_construct(v53,v54) => Stuck
          | Expr_cons(v55,v56) => Stuck
          | Expr_record(v57) => Stuck
          | Expr_override(v58,v59) => Stuck
          | Expr_apply(v60,v61) => Stuck
          | Expr_and(v62,v63) => Stuck
          | Expr_or(v64,v65) => Stuck
          | Expr_field(v66,v67) => Stuck
          | Expr_ifthenelse(v68,v69,v70) => Stuck
          | Expr_while(v71,v72) => Stuck
          | Expr_for(v73,v74,v75,v76,v77) => Stuck
          | Expr_sequence(v78,v79) => Stuck
          | Expr_match(v80,v81) => Stuck
          | Expr_function(v82) => Stuck
          | Expr_try(v83,v84) => Stuck
          | Expr_let(v85,v86) => Stuck
          | Expr_letrec(v87,v88) => Stuck
          | Expr_assert(v89) => Stuck
          | Expr_location(v90) => Stuck
    
  fun is_const_constr (CONST_constr(v0)) = true
    | is_const_constr CONST_unit = false
    | is_const_constr CONST_nil = false
    | is_const_constr CONST_true = false
    | is_const_constr CONST_false = false
    | is_const_constr (CONST_string(v4)) = false
    | is_const_constr (CONST_char(v3)) = false
    | is_const_constr (CONST_float(v2)) = false
    | is_const_constr (CONST_int(v)) = false
    
  fun non_funval_equal (Expr_constant(c)) (Expr_constant(c')) =
        (if c = c' then Step(Expr_constant(CONST_true))
           else Step(Expr_constant(CONST_false)))
    | non_funval_equal (Expr_location(l)) (Expr_location(l')) =
        Step(Expr_apply(Expr_apply(Expr_bprim(Bprim_equal),
                        Expr_apply(Expr_uprim(Uprim_deref),
                        Expr_location(l))),
             Expr_apply(Expr_uprim(Uprim_deref),Expr_location(l'))))
    | non_funval_equal (Expr_cons(v1,v2)) (Expr_cons(v1',v2')) =
        Step(Expr_and(Expr_apply(Expr_apply(Expr_bprim(Bprim_equal),v1),
                      v1'),
             Expr_apply(Expr_apply(Expr_bprim(Bprim_equal),v2),v2')))
    | non_funval_equal (Expr_cons(v1,v2)) (Expr_constant(const)) =
        (if const = CONST_nil then Step(Expr_constant(CONST_false))
           else Stuck)
    | non_funval_equal (Expr_constant(const)) (Expr_cons(v1',v2')) =
        (if const = CONST_nil then Step(Expr_constant(CONST_false))
           else Stuck)
    | non_funval_equal (Expr_tuple(vs)) (Expr_tuple(vs')) =
        (if not (>= (LENGTH vs) TWO) orelse not (LENGTH vs = LENGTH vs')
           then Stuck
           else Step(FOLDR (fn x => fn y => Expr_and (x,y)) (Expr_constant(CONST_true))
                       (MAP2 (fn v => fn v' =>
                          Expr_apply(Expr_apply(Expr_bprim(Bprim_equal),
                                     v),
                          v')) vs vs')))
    | non_funval_equal (Expr_construct(ctor,vs))
        (Expr_construct(ctor',vs')) =
        (if not (ctor = ctor') then Step(Expr_constant(CONST_false))
           else if not (LENGTH vs = LENGTH vs') then Stuck
                  else Step(FOLDR (fn x => fn y => Expr_and (x,y)) (Expr_constant(CONST_true))
                              (MAP2 (fn v => fn v' =>
                                 Expr_apply(Expr_apply(Expr_bprim(Bprim_equal),
                                            v),
                                 v')) vs vs')))
    | non_funval_equal (Expr_construct(ctor,vs)) (Expr_constant(const))
        =
        (if is_const_constr const then Step(Expr_constant(CONST_false))
           else Stuck)
    | non_funval_equal (Expr_constant(const))
        (Expr_construct(ctor',vs')) =
        (if is_const_constr const then Step(Expr_constant(CONST_false))
           else Stuck)
    | non_funval_equal (Expr_record(field_exprs))
        (Expr_record(field_exprs')) =
        (if not
              (ottML.PERM
                 (MAP (fn x => field_to_fn (pairML.FST x)) field_exprs)
                 (MAP (fn x => field_to_fn (pairML.FST x))
                    field_exprs')) then Stuck
           else Step(FOLDR (fn x => fn y => Expr_and (x,y)) (Expr_constant(CONST_true))
                       (MAP (fn (field,v) =>
                          Expr_apply(Expr_apply(Expr_bprim(Bprim_equal),
                                     v),
                          Expr_field(Expr_record(field_exprs'),field)))
                          field_exprs)))
    | non_funval_equal (Expr_location(v49)) (Expr_assert(v588)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_letrec(v586,v587)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_let(v584,v585)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_try(v582,v583)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_function(v581)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_match(v579,v580)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_sequence(v577,v578)) =
        Stuck
    | non_funval_equal (Expr_location(v49))
        (Expr_for(v572,v573,v574,v575,v576)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_while(v570,v571)) =
        Stuck
    | non_funval_equal (Expr_location(v49))
        (Expr_ifthenelse(v567,v568,v569)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_field(v565,v566)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_or(v563,v564)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_and(v561,v562)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_apply(v559,v560)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_override(v557,v558)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_record(v556)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_cons(v554,v555)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_construct(v552,v553))
        = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_tuple(v551)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_typed(v549,v550)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_constant(v548)) =
        Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_ident(v547)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_bprim(v546)) = Stuck
    | non_funval_equal (Expr_location(v49)) (Expr_uprim(v545)) = Stuck
    | non_funval_equal (Expr_assert(v48)) v3 = Stuck
    | non_funval_equal (Expr_letrec(v46,v47)) v3 = Stuck
    | non_funval_equal (Expr_let(v44,v45)) v3 = Stuck
    | non_funval_equal (Expr_try(v42,v43)) v3 = Stuck
    | non_funval_equal (Expr_function(v41)) v3 = Stuck
    | non_funval_equal (Expr_match(v39,v40)) v3 = Stuck
    | non_funval_equal (Expr_sequence(v37,v38)) v3 = Stuck
    | non_funval_equal (Expr_for(v32,v33,v34,v35,v36)) v3 = Stuck
    | non_funval_equal (Expr_while(v30,v31)) v3 = Stuck
    | non_funval_equal (Expr_ifthenelse(v27,v28,v29)) v3 = Stuck
    | non_funval_equal (Expr_field(v25,v26)) v3 = Stuck
    | non_funval_equal (Expr_or(v23,v24)) v3 = Stuck
    | non_funval_equal (Expr_and(v21,v22)) v3 = Stuck
    | non_funval_equal (Expr_apply(v19,v20)) v3 = Stuck
    | non_funval_equal (Expr_override(v17,v18)) v3 = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_location(v499)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_assert(v498)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_letrec(v496,v497)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_let(v494,v495)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_try(v492,v493)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_function(v491)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_match(v489,v490)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_sequence(v487,v488)) =
        Stuck
    | non_funval_equal (Expr_record(v16))
        (Expr_for(v482,v483,v484,v485,v486)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_while(v480,v481)) =
        Stuck
    | non_funval_equal (Expr_record(v16))
        (Expr_ifthenelse(v477,v478,v479)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_field(v475,v476)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_or(v473,v474)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_and(v471,v472)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_apply(v469,v470)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_override(v467,v468)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_cons(v464,v465)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_construct(v462,v463)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_tuple(v461)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_typed(v459,v460)) =
        Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_constant(v458)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_ident(v457)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_bprim(v456)) = Stuck
    | non_funval_equal (Expr_record(v16)) (Expr_uprim(v455)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_location(v409)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_assert(v408)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_letrec(v406,v407)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_let(v404,v405)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_try(v402,v403)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_function(v401)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_match(v399,v400)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_sequence(v397,v398)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15))
        (Expr_for(v392,v393,v394,v395,v396)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_while(v390,v391)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15))
        (Expr_ifthenelse(v387,v388,v389)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_field(v385,v386)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_or(v383,v384)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_and(v381,v382)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_apply(v379,v380)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_override(v377,v378)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_record(v376)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_construct(v372,v373))
        = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_tuple(v371)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_typed(v369,v370)) =
        Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_ident(v367)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_bprim(v366)) = Stuck
    | non_funval_equal (Expr_cons(v14,v15)) (Expr_uprim(v365)) = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_location(v319)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_assert(v318)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13))
        (Expr_letrec(v316,v317)) = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_let(v314,v315)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_try(v312,v313)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_function(v311)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_match(v309,v310))
        = Stuck
    | non_funval_equal (Expr_construct(v12,v13))
        (Expr_sequence(v307,v308)) = Stuck
    | non_funval_equal (Expr_construct(v12,v13))
        (Expr_for(v302,v303,v304,v305,v306)) = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_while(v300,v301))
        = Stuck
    | non_funval_equal (Expr_construct(v12,v13))
        (Expr_ifthenelse(v297,v298,v299)) = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_field(v295,v296))
        = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_or(v293,v294)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_and(v291,v292)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_apply(v289,v290))
        = Stuck
    | non_funval_equal (Expr_construct(v12,v13))
        (Expr_override(v287,v288)) = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_record(v286)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_cons(v284,v285))
        = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_tuple(v281)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_typed(v279,v280))
        = Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_ident(v277)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_bprim(v276)) =
        Stuck
    | non_funval_equal (Expr_construct(v12,v13)) (Expr_uprim(v275)) =
        Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_location(v229)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_assert(v228)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_letrec(v226,v227)) =
        Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_let(v224,v225)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_try(v222,v223)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_function(v221)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_match(v219,v220)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_sequence(v217,v218)) =
        Stuck
    | non_funval_equal (Expr_tuple(v11))
        (Expr_for(v212,v213,v214,v215,v216)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_while(v210,v211)) = Stuck
    | non_funval_equal (Expr_tuple(v11))
        (Expr_ifthenelse(v207,v208,v209)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_field(v205,v206)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_or(v203,v204)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_and(v201,v202)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_apply(v199,v200)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_override(v197,v198)) =
        Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_record(v196)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_cons(v194,v195)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_construct(v192,v193)) =
        Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_typed(v189,v190)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_constant(v188)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_ident(v187)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_bprim(v186)) = Stuck
    | non_funval_equal (Expr_tuple(v11)) (Expr_uprim(v185)) = Stuck
    | non_funval_equal (Expr_typed(v9,v10)) v3 = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_location(v139)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_assert(v138)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_letrec(v136,v137)) =
        Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_let(v134,v135)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_try(v132,v133)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_function(v131)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_match(v129,v130)) =
        Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_sequence(v127,v128)) =
        Stuck
    | non_funval_equal (Expr_constant(v8))
        (Expr_for(v122,v123,v124,v125,v126)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_while(v120,v121)) =
        Stuck
    | non_funval_equal (Expr_constant(v8))
        (Expr_ifthenelse(v117,v118,v119)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_field(v115,v116)) =
        Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_or(v113,v114)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_and(v111,v112)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_apply(v109,v110)) =
        Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_override(v107,v108)) =
        Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_record(v106)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_tuple(v101)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_typed(v99,v100)) =
        Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_ident(v97)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_bprim(v96)) = Stuck
    | non_funval_equal (Expr_constant(v8)) (Expr_uprim(v95)) = Stuck
    | non_funval_equal (Expr_ident(v7)) v3 = Stuck
    | non_funval_equal (Expr_bprim(v6)) v3 = Stuck
    | non_funval_equal (Expr_uprim(v5)) v3 = Stuck
    
  fun eval_bprim Bprim_equal v1 v2 =
        (if funval v1
           then Step(Expr_apply(Expr_uprim(Uprim_raise),
                     Expr_construct(C_invalidargument,
                     [Expr_constant(CONST_string("equal: functional value"))])))
           else non_funval_equal v1 v2)
    | eval_bprim Bprim_plus v1 v2 = b_int_primop wordsML.word_add v1 v2
    | eval_bprim Bprim_minus v1 v2 = b_int_primop wordsML.word_sub v1 v2
    | eval_bprim Bprim_times v1 v2 = b_int_primop wordsML.word_mul v1 v2
    | eval_bprim Bprim_div v1 v2 =
        (if v2
            =
            Expr_constant(CONST_int(wordsML.n2w_itself
                                      (ZERO,(fcpML.ITSELF (numML.fromDecString"31")))))
           then (case v1
                 of Expr_uprim(v45) => Stuck
                  | Expr_bprim(v46) => Stuck
                  | Expr_ident(v47) => Stuck
                  | Expr_constant(CONST_int(n)) =>
                       Step(Expr_apply(Expr_uprim(Uprim_raise),
                            Expr_constant(CONST_constr(C_div_by_0))))
                  | Expr_constant(CONST_float(v96)) => Stuck
                  | Expr_constant(CONST_char(v97)) => Stuck
                  | Expr_constant(CONST_string(v98)) => Stuck
                  | Expr_constant(CONST_constr(v99)) => Stuck
                  | Expr_constant(CONST_false) => Stuck
                  | Expr_constant(CONST_true) => Stuck
                  | Expr_constant(CONST_nil) => Stuck
                  | Expr_constant(CONST_unit) => Stuck
                  | Expr_typed(v49,v50) => Stuck
                  | Expr_tuple(v51) => Stuck
                  | Expr_construct(v52,v53) => Stuck
                  | Expr_cons(v54,v55) => Stuck
                  | Expr_record(v56) => Stuck
                  | Expr_override(v57,v58) => Stuck
                  | Expr_apply(v59,v60) => Stuck
                  | Expr_and(v61,v62) => Stuck
                  | Expr_or(v63,v64) => Stuck
                  | Expr_field(v65,v66) => Stuck
                  | Expr_ifthenelse(v67,v68,v69) => Stuck
                  | Expr_while(v70,v71) => Stuck
                  | Expr_for(v72,v73,v74,v75,v76) => Stuck
                  | Expr_sequence(v77,v78) => Stuck
                  | Expr_match(v79,v80) => Stuck
                  | Expr_function(v81) => Stuck
                  | Expr_try(v82,v83) => Stuck
                  | Expr_let(v84,v85) => Stuck
                  | Expr_letrec(v86,v87) => Stuck
                  | Expr_assert(v88) => Stuck
                  | Expr_location(v89) => Stuck)
           else b_int_primop wordsML.word_sdiv v1 v2)
    | eval_bprim Bprim_assign v1 v2 =
        (case v1
         of Expr_uprim(v46) => Stuck
          | Expr_bprim(v47) => Stuck
          | Expr_ident(v48) => Stuck
          | Expr_constant(v49) => Stuck
          | Expr_typed(v50,v51) => Stuck
          | Expr_tuple(v52) => Stuck
          | Expr_construct(v53,v54) => Stuck
          | Expr_cons(v55,v56) => Stuck
          | Expr_record(v57) => Stuck
          | Expr_override(v58,v59) => Stuck
          | Expr_apply(v60,v61) => Stuck
          | Expr_and(v62,v63) => Stuck
          | Expr_or(v64,v65) => Stuck
          | Expr_field(v66,v67) => Stuck
          | Expr_ifthenelse(v68,v69,v70) => Stuck
          | Expr_while(v71,v72) => Stuck
          | Expr_for(v73,v74,v75,v76,v77) => Stuck
          | Expr_sequence(v78,v79) => Stuck
          | Expr_match(v80,v81) => Stuck
          | Expr_function(v82) => Stuck
          | Expr_try(v83,v84) => Stuck
          | Expr_let(v85,v86) => Stuck
          | Expr_letrec(v87,v88) => Stuck
          | Expr_assert(v89) => Stuck
          | Expr_location(l) =>
               StepAssign(Expr_constant(CONST_unit),l,v2))
    
  fun do_1override fn1 v1 [] = NONE
    | do_1override fn1 v1 ((fn2,v2)::record) =
        (if fn1 = fn2 then SOME((fn1,v1)::record)
           else OPTION_MAP (fn r => (fn2,v2)::r)
                  (do_1override fn1 v1 record))
    
  fun eval_override v [] [] = Stuck
    | eval_override v1 [fn1] [v] =
        (case v1
         of Expr_uprim(v46) => Stuck
          | Expr_bprim(v47) => Stuck
          | Expr_ident(v48) => Stuck
          | Expr_constant(v49) => Stuck
          | Expr_typed(v50,v51) => Stuck
          | Expr_tuple(v52) => Stuck
          | Expr_construct(v53,v54) => Stuck
          | Expr_cons(v55,v56) => Stuck
          | Expr_record(fn_expr_list) =>
               (case do_1override fn1 v fn_expr_list
                of NONE => Stuck | SOME(x) => Step(Expr_record(x)))
          | Expr_override(v58,v59) => Stuck
          | Expr_apply(v60,v61) => Stuck
          | Expr_and(v62,v63) => Stuck
          | Expr_or(v64,v65) => Stuck
          | Expr_field(v66,v67) => Stuck
          | Expr_ifthenelse(v68,v69,v70) => Stuck
          | Expr_while(v71,v72) => Stuck
          | Expr_for(v73,v74,v75,v76,v77) => Stuck
          | Expr_sequence(v78,v79) => Stuck
          | Expr_match(v80,v81) => Stuck
          | Expr_function(v82) => Stuck
          | Expr_try(v83,v84) => Stuck
          | Expr_let(v85,v86) => Stuck
          | Expr_letrec(v87,v88) => Stuck
          | Expr_assert(v89) => Stuck
          | Expr_location(v90) => Stuck)
    | eval_override v1 (fn1::v12::v13) (v::voverrides) =
        (case v1
         of Expr_uprim(v46) => Stuck
          | Expr_bprim(v47) => Stuck
          | Expr_ident(v48) => Stuck
          | Expr_constant(v49) => Stuck
          | Expr_typed(v50,v51) => Stuck
          | Expr_tuple(v52) => Stuck
          | Expr_construct(v53,v54) => Stuck
          | Expr_cons(v55,v56) => Stuck
          | Expr_record(fn_expr_list) =>
               (case do_1override fn1 v fn_expr_list
                of NONE => Stuck
                 | SOME(x) =>
                      Step(Expr_override(Expr_record(x),
                           ZIP (v12::v13,voverrides))))
          | Expr_override(v58,v59) => Stuck
          | Expr_apply(v60,v61) => Stuck
          | Expr_and(v62,v63) => Stuck
          | Expr_or(v64,v65) => Stuck
          | Expr_field(v66,v67) => Stuck
          | Expr_ifthenelse(v68,v69,v70) => Stuck
          | Expr_while(v71,v72) => Stuck
          | Expr_for(v73,v74,v75,v76,v77) => Stuck
          | Expr_sequence(v78,v79) => Stuck
          | Expr_match(v80,v81) => Stuck
          | Expr_function(v82) => Stuck
          | Expr_try(v83,v84) => Stuck
          | Expr_let(v85,v86) => Stuck
          | Expr_letrec(v87,v88) => Stuck
          | Expr_assert(v89) => Stuck
          | Expr_location(v90) => Stuck)
    | eval_override v1 [fn1] (v::v18::v19) =
        (case v1
         of Expr_uprim(v46) => Stuck
          | Expr_bprim(v47) => Stuck
          | Expr_ident(v48) => Stuck
          | Expr_constant(v49) => Stuck
          | Expr_typed(v50,v51) => Stuck
          | Expr_tuple(v52) => Stuck
          | Expr_construct(v53,v54) => Stuck
          | Expr_cons(v55,v56) => Stuck
          | Expr_record(fn_expr_list) =>
               (case do_1override fn1 v fn_expr_list
                of NONE => Stuck
                 | SOME(x) =>
                      Step(Expr_override(Expr_record(x),
                           ZIP ([],v18::v19))))
          | Expr_override(v58,v59) => Stuck
          | Expr_apply(v60,v61) => Stuck
          | Expr_and(v62,v63) => Stuck
          | Expr_or(v64,v65) => Stuck
          | Expr_field(v66,v67) => Stuck
          | Expr_ifthenelse(v68,v69,v70) => Stuck
          | Expr_while(v71,v72) => Stuck
          | Expr_for(v73,v74,v75,v76,v77) => Stuck
          | Expr_sequence(v78,v79) => Stuck
          | Expr_match(v80,v81) => Stuck
          | Expr_function(v82) => Stuck
          | Expr_try(v83,v84) => Stuck
          | Expr_let(v85,v86) => Stuck
          | Expr_letrec(v87,v88) => Stuck
          | Expr_assert(v89) => Stuck
          | Expr_location(v90) => Stuck)
    
  fun eval_apply v1 v2 =
        case v1
         of Expr_uprim(up) => eval_uprim up v2
          | Expr_bprim(v49) => Stuck
          | Expr_ident(v50) => Stuck
          | Expr_constant(v51) => Stuck
          | Expr_typed(v52,v53) => Stuck
          | Expr_tuple(v54) => Stuck
          | Expr_construct(v55,v56) => Stuck
          | Expr_cons(v57,v58) => Stuck
          | Expr_record(v59) => Stuck
          | Expr_override(v60,v61) => Stuck
          | Expr_apply(Expr_uprim(v47),v63) => Stuck
          | Expr_apply(Expr_bprim(bp),v63) => eval_bprim bp v63 v2
          | Expr_apply(Expr_ident(v49),v63) => Stuck
          | Expr_apply(Expr_constant(v50),v63) => Stuck
          | Expr_apply(Expr_typed(v51,v52),v63) => Stuck
          | Expr_apply(Expr_tuple(v53),v63) => Stuck
          | Expr_apply(Expr_construct(v54,v55),v63) => Stuck
          | Expr_apply(Expr_cons(v56,v57),v63) => Stuck
          | Expr_apply(Expr_record(v58),v63) => Stuck
          | Expr_apply(Expr_override(v59,v60),v63) => Stuck
          | Expr_apply(Expr_apply(v61,v62),v63) => Stuck
          | Expr_apply(Expr_and(v163,v64),v63) => Stuck
          | Expr_apply(Expr_or(v65,v66),v63) => Stuck
          | Expr_apply(Expr_field(v67,v68),v63) => Stuck
          | Expr_apply(Expr_ifthenelse(v69,v70,v71),v63) => Stuck
          | Expr_apply(Expr_while(v72,v73),v63) => Stuck
          | Expr_apply(Expr_for(v74,v75,v76,v77,v78),v63) => Stuck
          | Expr_apply(Expr_sequence(v79,v80),v63) => Stuck
          | Expr_apply(Expr_match(v81,v82),v63) => Stuck
          | Expr_apply(Expr_function(v83),v63) => Stuck
          | Expr_apply(Expr_try(v84,v85),v63) => Stuck
          | Expr_apply(Expr_let(v86,v87),v63) => Stuck
          | Expr_apply(Expr_letrec(v88,v89),v63) => Stuck
          | Expr_apply(Expr_assert(v90),v63) => Stuck
          | Expr_apply(Expr_location(v91),v63) => Stuck
          | Expr_and(v64,v65) => Stuck
          | Expr_or(v66,v67) => Stuck
          | Expr_field(v68,v69) => Stuck
          | Expr_ifthenelse(v70,v71,v72) => Stuck
          | Expr_while(v73,v74) => Stuck
          | Expr_for(v75,v76,v77,v78,v79) => Stuck
          | Expr_sequence(v80,v81) => Stuck
          | Expr_match(v82,v83) => Stuck
          | Expr_function(pm) => Step(Expr_match(v2,pm))
          | Expr_try(v85,v86) => Stuck
          | Expr_let(v87,v88) => Stuck
          | Expr_letrec(v89,v90) => Stuck
          | Expr_assert(v91) => Stuck
          | Expr_location(v92) => Stuck
    
  fun eval_field field v =
        case v
         of Expr_uprim(v45) => Stuck
          | Expr_bprim(v46) => Stuck
          | Expr_ident(v47) => Stuck
          | Expr_constant(v48) => Stuck
          | Expr_typed(v49,v50) => Stuck
          | Expr_tuple(v51) => Stuck
          | Expr_construct(v52,v53) => Stuck
          | Expr_cons(v54,v55) => Stuck
          | Expr_record(fn_expr_list) =>
               (case ottML.list_assoc field fn_expr_list
                of NONE => Stuck | SOME(x) => Step(x))
          | Expr_override(v57,v58) => Stuck
          | Expr_apply(v59,v60) => Stuck
          | Expr_and(v61,v62) => Stuck
          | Expr_or(v63,v64) => Stuck
          | Expr_field(v65,v66) => Stuck
          | Expr_ifthenelse(v67,v68,v69) => Stuck
          | Expr_while(v70,v71) => Stuck
          | Expr_for(v72,v73,v74,v75,v76) => Stuck
          | Expr_sequence(v77,v78) => Stuck
          | Expr_match(v79,v80) => Stuck
          | Expr_function(v81) => Stuck
          | Expr_try(v82,v83) => Stuck
          | Expr_let(v84,v85) => Stuck
          | Expr_letrec(v86,v87) => Stuck
          | Expr_assert(v88) => Stuck
          | Expr_location(v89) => Stuck
    
  fun eval_ite expr2 expr3 v1 =
        if v1 = Expr_constant(CONST_true) then Step(expr2)
          else if v1 = Expr_constant(CONST_false) then Step(expr3)
                 else Stuck
    
  fun eval_while e1 e2 =
        Step(Expr_ifthenelse(e1,
             Expr_sequence(e2,Expr_while(e1,e2)),
             Expr_constant(CONST_unit)))
    
  fun eval_for x for_dirn expr3 v2 v1 =
        case v1
         of Expr_uprim(v47) => Stuck
          | Expr_bprim(v48) => Stuck
          | Expr_ident(v49) => Stuck
          | Expr_constant(CONST_int(n1)) =>
               (case v2
                of Expr_uprim(v47) => Stuck
                 | Expr_bprim(v48) => Stuck
                 | Expr_ident(v49) => Stuck
                 | Expr_constant(CONST_int(n2)) =>
                      (case for_dirn
                       of FD_upto =>
                             if wordsML.word_le n1 n2
                               then Step(Expr_sequence(Expr_let(LB_simple(P_var(x),
                                                                v1),
                                                       expr3),
                                         Expr_for(x,
                                         Expr_constant(CONST_int(wordsML.word_add
                                                                   n1
                                                                   (wordsML.n2w_itself
                                                                      (ONE,(fcpML.ITSELF (numML.fromDecString"31")))))),
                                         for_dirn,
                                         v2,
                                         expr3)))
                               else Step(Expr_constant(CONST_unit))
                        | FD_downto =>
                             if wordsML.word_le n2 n1
                               then Step(Expr_sequence(Expr_let(LB_simple(P_var(x),
                                                                v1),
                                                       expr3),
                                         Expr_for(x,
                                         Expr_constant(CONST_int(wordsML.word_sub
                                                                   n1
                                                                   (wordsML.n2w_itself
                                                                      (ONE,(fcpML.ITSELF (numML.fromDecString"31")))))),
                                         for_dirn,
                                         v2,
                                         expr3)))
                               else Step(Expr_constant(CONST_unit)))
                 | Expr_constant(CONST_float(v98)) => Stuck
                 | Expr_constant(CONST_char(v99)) => Stuck
                 | Expr_constant(CONST_string(v100)) => Stuck
                 | Expr_constant(CONST_constr(v101)) => Stuck
                 | Expr_constant(CONST_false) => Stuck
                 | Expr_constant(CONST_true) => Stuck
                 | Expr_constant(CONST_nil) => Stuck
                 | Expr_constant(CONST_unit) => Stuck
                 | Expr_typed(v51,v52) => Stuck
                 | Expr_tuple(v53) => Stuck
                 | Expr_construct(v54,v55) => Stuck
                 | Expr_cons(v56,v57) => Stuck
                 | Expr_record(v58) => Stuck
                 | Expr_override(v59,v60) => Stuck
                 | Expr_apply(v61,v62) => Stuck
                 | Expr_and(v63,v64) => Stuck
                 | Expr_or(v65,v66) => Stuck
                 | Expr_field(v67,v68) => Stuck
                 | Expr_ifthenelse(v69,v70,v71) => Stuck
                 | Expr_while(v72,v73) => Stuck
                 | Expr_for(v74,v75,v76,v77,v78) => Stuck
                 | Expr_sequence(v79,v80) => Stuck
                 | Expr_match(v81,v82) => Stuck
                 | Expr_function(v83) => Stuck
                 | Expr_try(v84,v85) => Stuck
                 | Expr_let(v86,v87) => Stuck
                 | Expr_letrec(v88,v89) => Stuck
                 | Expr_assert(v90) => Stuck
                 | Expr_location(v91) => Stuck)
          | Expr_constant(CONST_float(v98)) => Stuck
          | Expr_constant(CONST_char(v99)) => Stuck
          | Expr_constant(CONST_string(v100)) => Stuck
          | Expr_constant(CONST_constr(v101)) => Stuck
          | Expr_constant(CONST_false) => Stuck
          | Expr_constant(CONST_true) => Stuck
          | Expr_constant(CONST_nil) => Stuck
          | Expr_constant(CONST_unit) => Stuck
          | Expr_typed(v51,v52) => Stuck
          | Expr_tuple(v53) => Stuck
          | Expr_construct(v54,v55) => Stuck
          | Expr_cons(v56,v57) => Stuck
          | Expr_record(v58) => Stuck
          | Expr_override(v59,v60) => Stuck
          | Expr_apply(v61,v62) => Stuck
          | Expr_and(v63,v64) => Stuck
          | Expr_or(v65,v66) => Stuck
          | Expr_field(v67,v68) => Stuck
          | Expr_ifthenelse(v69,v70,v71) => Stuck
          | Expr_while(v72,v73) => Stuck
          | Expr_for(v74,v75,v76,v77,v78) => Stuck
          | Expr_sequence(v79,v80) => Stuck
          | Expr_match(v81,v82) => Stuck
          | Expr_function(v83) => Stuck
          | Expr_try(v84,v85) => Stuck
          | Expr_let(v86,v87) => Stuck
          | Expr_letrec(v88,v89) => Stuck
          | Expr_assert(v90) => Stuck
          | Expr_location(v91) => Stuck
    
  fun eval_match (PM_pm([])) v = Stuck
    | eval_match (PM_pm([PE_inj(p,e)])) v =
        Step(case matching_funML.pat_match p v
              of NONE =>
                    Expr_apply(Expr_uprim(Uprim_raise),
                    Expr_constant(CONST_constr(C_matchfailure)))
               | SOME(substs) => substs_value_name_expr substs e)
    | eval_match (PM_pm(PE_inj(p,e)::v8::v9)) v =
        Step(case matching_funML.pat_match p v
              of NONE => Expr_match(v,PM_pm(v8::v9))
               | SOME(substs) => substs_value_name_expr substs e)
    
  fun eval_try expr pattern_matching =
        case expr
         of Expr_uprim(v45) => Stuck
          | Expr_bprim(v46) => Stuck
          | Expr_ident(v47) => Stuck
          | Expr_constant(v48) => Stuck
          | Expr_typed(v49,v50) => Stuck
          | Expr_tuple(v51) => Stuck
          | Expr_construct(v52,v53) => Stuck
          | Expr_cons(v54,v55) => Stuck
          | Expr_record(v56) => Stuck
          | Expr_override(v57,v58) => Stuck
          | Expr_apply(e1,e2) =>
               if e1 = Expr_uprim(Uprim_raise)
                 then (case pattern_matching
                       of PM_pm(pe_list) =>
                             Step(Expr_match(e2,
                                  PM_pm(APPEND pe_list
                                          [PE_inj(P_any,expr)])))
                        ) else Stuck
          | Expr_and(v61,v62) => Stuck
          | Expr_or(v63,v64) => Stuck
          | Expr_field(v65,v66) => Stuck
          | Expr_ifthenelse(v67,v68,v69) => Stuck
          | Expr_while(v70,v71) => Stuck
          | Expr_for(v72,v73,v74,v75,v76) => Stuck
          | Expr_sequence(v77,v78) => Stuck
          | Expr_match(v79,v80) => Stuck
          | Expr_function(v81) => Stuck
          | Expr_try(v82,v83) => Stuck
          | Expr_let(v84,v85) => Stuck
          | Expr_letrec(v86,v87) => Stuck
          | Expr_assert(v88) => Stuck
          | Expr_location(v89) => Stuck
    
  fun eval_let pattern expr2 v1 =
        Step(case matching_funML.pat_match pattern v1
              of NONE =>
                    Expr_apply(Expr_uprim(Uprim_raise),
                    Expr_constant(CONST_constr(C_matchfailure)))
               | SOME(substs) => substs_value_name_expr substs expr2)
    
  fun eval_letrec letrec_bindings expr =
        Step(substs_value_name_expr
               (MAP (fn lb =>
                  case lb
                   of LRB_simple(vn,pm) =>
                         (vn,recfun letrec_bindings pm)
                    ) (lrbs_to_lrblist letrec_bindings)) expr)
    
  fun eval_assert v =
        if v = Expr_constant(CONST_true)
          then Step(Expr_constant(CONST_unit))
          else if v = Expr_constant(CONST_false)
                 then Step(Expr_apply(Expr_uprim(Uprim_raise),
                           Expr_constant(CONST_constr(C_assertfailure))))
                 else Stuck
    
  fun red (Expr_uprim(unary_prim)) = Stuck
    | red (Expr_bprim(binary_prim)) = Stuck
    | red (Expr_ident(value_name)) = Stuck
    | red (Expr_constant(constant)) = Stuck
    | red (Expr_typed(expr,typexpr)) = Step(expr)
    | red (Expr_tuple(exprs)) =
        red_list (REVERSE exprs) Expr_tuple (fn v => Stuck) []
    | red (Expr_construct(constr,exprs)) =
        red_list (REVERSE exprs) (fn x => Expr_construct(constr,x)) (fn x =>
          Stuck) []
    | red (Expr_cons(expr1,expr2)) =
        red_2 expr1 expr2 (fn x => fn y => Expr_cons (x,y)) (fn v1 => fn v2 => Stuck)
    | red (Expr_record(field_exprs)) =
        let val (fields,exprs) = UNZIP field_exprs
        in
           red_list (REVERSE exprs) (fn es =>
             Expr_record(ZIP (fields,es))) (fn v => Stuck) []
        end
    | red (Expr_override(expr,field_exprs)) =
        red_1 expr (fn e => Expr_override(e,field_exprs)) (fn v =>
          let val (fields,exprs) = UNZIP field_exprs
          in
             red_list (REVERSE exprs) (fn es =>
               Expr_override(v,ZIP (fields,es)))
               (eval_override v fields) []
          end)
    | red (Expr_apply(expr1,expr2)) =
        red_2 expr1 expr2 (fn x => fn y => Expr_apply(x,y)) eval_apply
    | red (Expr_and(expr1,expr2)) =
        Step(Expr_ifthenelse(expr1,expr2,Expr_constant(CONST_false)))
    | red (Expr_or(expr1,expr2)) =
        Step(Expr_ifthenelse(expr1,Expr_constant(CONST_true),expr2))
    | red (Expr_field(expr,field)) =
        red_1 expr (fn e => Expr_field(e,field)) (eval_field field)
    | red (Expr_ifthenelse(expr1,expr2,expr3)) =
        red_1 expr1 (fn e => Expr_ifthenelse(e,expr2,expr3))
          (eval_ite expr2 expr3)
    | red (Expr_while(expr1,expr2)) = eval_while expr1 expr2
    | red (Expr_for(value_name,expr1,for_dirn,expr2,expr3)) =
        red_2 expr2 expr1 (fn e2 => fn e1 =>
          Expr_for(value_name,e1,for_dirn,e2,expr3))
          (eval_for value_name for_dirn expr3)
    | red (Expr_sequence(expr1,expr2)) =
        red_1 expr1 (fn e => Expr_sequence(e,expr2)) (fn v =>
          Step(expr2))
    | red (Expr_match(expr,pattern_matching)) =
        red_1 expr (fn e => Expr_match(e,pattern_matching))
          (eval_match pattern_matching)
    | red (Expr_function(pattern_matching)) = Stuck
    | red (Expr_try(expr,pattern_matching)) =
        (if is_raise expr then eval_try expr pattern_matching
           else if is_value_of_expr expr then Step(expr)
                  else result_map (fn e => Expr_try(e,pattern_matching))
                         (red expr))
    | red (Expr_let(LB_simple(pattern,expr1),expr2)) =
        red_1 expr1 (fn e1 => Expr_let(LB_simple(pattern,e1),expr2))
          (eval_let pattern expr2)
    | red (Expr_letrec(letrec_bindings,expr)) =
        eval_letrec letrec_bindings expr
    | red (Expr_assert(expr)) = red_1 expr Expr_assert eval_assert
    | red (Expr_location(location)) = Stuck
    
  and red_1 expr pack1 eval1 =
        if is_raise expr then Step(expr)
          else if not (is_value_of_expr expr)
                 then result_map pack1 (red expr) else eval1 expr
    
  and red_2 expr1 expr2 pack2 eval2 =
        if is_raise expr2 then Step(expr2)
          else if not (is_value_of_expr expr2)
                 then result_map (pack2 expr1) (red expr2)
                 else if is_raise expr1 then Step(expr1)
                        else if not (is_value_of_expr expr1)
                               then result_map (fn e => pack2 e expr2)
                                      (red expr1) else eval2 expr1 expr2
    
  and red_list [] packl evall acc = evall acc
    | red_list (expr::exprs) packl evall acc =
        (if is_raise expr then Step(expr)
           else if not (is_value_of_expr expr)
                  then result_map (fn e =>
                         packl
                           (APPEND (APPEND (REVERSE exprs) [e]) acc))
                         (red expr)
                  else red_list exprs packl evall (expr::acc))
    
end
