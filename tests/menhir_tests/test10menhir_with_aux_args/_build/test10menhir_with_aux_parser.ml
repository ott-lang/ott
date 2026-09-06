
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | VAR of (
# 11 "test10menhir_with_aux_parser.mly"
       (string)
# 15 "test10menhir_with_aux_parser.ml"
  )
    | RPAREN
    | LPAREN
    | FOO
    | EOF
    | DOT
    | BACKSLASH
  
end

include MenhirBasics

# 2 "test10menhir_with_aux_parser.mly"
  
open Test10menhir_with_aux_ast

# 32 "test10menhir_with_aux_parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_term_start) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: term_start. *)

  | MenhirState02 : (('s, _menhir_box_term_start) _menhir_cell1_LPAREN, _menhir_box_term_start) _menhir_state
    (** State 02.
        Stack shape : LPAREN.
        Start symbol: term_start. *)

  | MenhirState03 : (('s, _menhir_box_term_start) _menhir_cell1_FOO, _menhir_box_term_start) _menhir_state
    (** State 03.
        Stack shape : FOO.
        Start symbol: term_start. *)

  | MenhirState06 : (('s, _menhir_box_term_start) _menhir_cell1_BACKSLASH _menhir_cell0_VAR, _menhir_box_term_start) _menhir_state
    (** State 06.
        Stack shape : BACKSLASH VAR.
        Start symbol: term_start. *)

  | MenhirState08 : (('s, _menhir_box_term_start) _menhir_cell1_lhs, _menhir_box_term_start) _menhir_state
    (** State 08.
        Stack shape : lhs.
        Start symbol: term_start. *)


and ('s, 'r) _menhir_cell1_lhs = 
  | MenhirCell1_lhs of 's * ('s, 'r) _menhir_state * (Test10menhir_with_aux_ast.term) * Lexing.position

and ('s, 'r) _menhir_cell1_BACKSLASH = 
  | MenhirCell1_BACKSLASH of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_FOO = 
  | MenhirCell1_FOO of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_VAR = 
  | MenhirCell0_VAR of 's * (
# 11 "test10menhir_with_aux_parser.mly"
       (string)
# 77 "test10menhir_with_aux_parser.ml"
) * Lexing.position * Lexing.position

and _menhir_box_term_start = 
  | MenhirBox_term_start of (Test10menhir_with_aux_ast.term) [@@unboxed]

let _menhir_action_01 =
  fun _endpos_x_ _startpos_x_ x ->
    let _endpos = _endpos_x_ in
    let _symbolstartpos = _startpos_x_ in
    (
# 39 "test10menhir_with_aux_parser.mly"
    ( (*Case 2*) T_var(x,Range(_symbolstartpos,_endpos)) )
# 90 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_02 =
  fun _endpos__3_ _startpos__1_ t ->
    let _endpos = _endpos__3_ in
    let _symbolstartpos = _startpos__1_ in
    (
# 41 "test10menhir_with_aux_parser.mly"
    ( (*Case 2*) T_paren(t,Range(_symbolstartpos,_endpos)) )
# 100 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_03 =
  fun _endpos_t_ _startpos__1_ t x ->
    let _endpos = _endpos_t_ in
    let _symbolstartpos = _startpos__1_ in
    (
# 57 "test10menhir_with_aux_parser.mly"
    ( (*Case 2*) T_lambda(x,t,Range(_symbolstartpos,_endpos)) )
# 110 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_04 =
  fun at ->
    (
# 45 "test10menhir_with_aux_parser.mly"
    ( (*Case 1*) at )
# 118 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_05 =
  fun _endpos_at_prime_ _startpos_lhs_ at_prime lhs ->
    let _endpos = _endpos_at_prime_ in
    let _symbolstartpos = _startpos_lhs_ in
    (
# 47 "test10menhir_with_aux_parser.mly"
    ( (*Case 1*) T_app(lhs, at_prime, Range(_symbolstartpos,_endpos)) )
# 128 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_06 =
  fun at ->
    (
# 51 "test10menhir_with_aux_parser.mly"
    ( (*Case 1*) at )
# 136 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_07 =
  fun lambda ->
    (
# 53 "test10menhir_with_aux_parser.mly"
    ( (*Case 1*) lambda )
# 144 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_08 =
  fun at ->
    (
# 29 "test10menhir_with_aux_parser.mly"
    ( (*Case 1*) at )
# 152 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_09 =
  fun _endpos_rhs_prime_ _startpos_lhs_ lhs rhs_prime ->
    let _endpos = _endpos_rhs_prime_ in
    let _symbolstartpos = _startpos_lhs_ in
    (
# 31 "test10menhir_with_aux_parser.mly"
    ( (*Case 2*) T_app(lhs,rhs_prime,Range(_symbolstartpos,_endpos)) )
# 162 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_10 =
  fun lambda ->
    (
# 33 "test10menhir_with_aux_parser.mly"
    ( (*Case 1*) lambda )
# 170 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_11 =
  fun _endpos_term_ _startpos__1_ term ->
    let _endpos = _endpos_term_ in
    let _symbolstartpos = _startpos__1_ in
    (
# 35 "test10menhir_with_aux_parser.mly"
    ( (*Case 2*) T_foo(term,Range(_symbolstartpos,_endpos)) )
# 180 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_action_12 =
  fun term ->
    (
# 21 "test10menhir_with_aux_parser.mly"
    ( term )
# 188 "test10menhir_with_aux_parser.ml"
     : (Test10menhir_with_aux_ast.term))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | BACKSLASH ->
        "BACKSLASH"
    | DOT ->
        "DOT"
    | EOF ->
        "EOF"
    | FOO ->
        "FOO"
    | LPAREN ->
        "LPAREN"
    | RPAREN ->
        "RPAREN"
    | VAR _ ->
        "VAR"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_18 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _v _tok ->
      match (_tok : MenhirBasics.token) with
      | EOF ->
          let term = _v in
          let _v = _menhir_action_12 term in
          MenhirBox_term_start _v
      | _ ->
          _eRR ()
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
      let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
      _menhir_goto_atomic_term _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
  
  and _menhir_goto_atomic_term : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState02 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
  
  and _menhir_run_13 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | BACKSLASH | LPAREN | VAR _ ->
          let (_startpos_at_, at) = (_startpos, _v) in
          let _v = _menhir_action_04 at in
          _menhir_goto_lhs _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_at_ _v _menhir_s _tok
      | EOF | RPAREN ->
          let (_endpos_at_, at) = (_endpos, _v) in
          let _v = _menhir_action_08 at in
          _menhir_goto_term _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_at_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_lhs : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_lhs (_menhir_stack, _menhir_s, _v, _startpos) in
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState08
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | BACKSLASH ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState08
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState02 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOO ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BACKSLASH ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_FOO (_menhir_stack, _menhir_s, _startpos) in
      let _menhir_s = MenhirState03 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOO ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BACKSLASH ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_BACKSLASH (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _menhir_stack = MenhirCell0_VAR (_menhir_stack, _v, _startpos, _endpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | DOT ->
              let _menhir_s = MenhirState06 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | VAR _v ->
                  _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | LPAREN ->
                  _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FOO ->
                  _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BACKSLASH ->
                  _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_term : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_18 _menhir_stack _v _tok
      | MenhirState02 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState03 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState06 ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_15 : type  ttv_stack. (ttv_stack, _menhir_box_term_start) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _endpos_0 = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (t, _endpos__3_) = (_v, _endpos_0) in
          let _v = _menhir_action_02 _endpos__3_ _startpos__1_ t in
          _menhir_goto_atomic_term _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__3_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. (ttv_stack, _menhir_box_term_start) _menhir_cell1_FOO -> _ -> _ -> _ -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_FOO (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_term_, term) = (_endpos, _v) in
      let _v = _menhir_action_11 _endpos_term_ _startpos__1_ term in
      _menhir_goto_term _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_term_ _v _menhir_s _tok
  
  and _menhir_run_07 : type  ttv_stack. (ttv_stack, _menhir_box_term_start) _menhir_cell1_BACKSLASH _menhir_cell0_VAR -> _ -> _ -> _ -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell0_VAR (_menhir_stack, x, _, _) = _menhir_stack in
      let MenhirCell1_BACKSLASH (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
      let (_endpos_t_, t) = (_endpos, _v) in
      let _v = _menhir_action_03 _endpos_t_ _startpos__1_ t x in
      _menhir_goto_lambda _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_t_ _v _menhir_s _tok
  
  and _menhir_goto_lambda : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState02 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState03 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
  
  and _menhir_run_12 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_term_start) _menhir_state -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _menhir_s _tok ->
      let (_endpos_lambda_, lambda) = (_endpos, _v) in
      let _v = _menhir_action_10 lambda in
      _menhir_goto_term _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_lambda_ _v _menhir_s _tok
  
  and _menhir_run_10 : type  ttv_stack. (ttv_stack, _menhir_box_term_start) _menhir_cell1_lhs -> _ -> _ -> _ -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let (_endpos_lambda_, lambda) = (_endpos, _v) in
      let _v = _menhir_action_07 lambda in
      _menhir_goto_rhs _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_lambda_ _v _tok
  
  and _menhir_goto_rhs : type  ttv_stack. (ttv_stack, _menhir_box_term_start) _menhir_cell1_lhs -> _ -> _ -> _ -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_lhs (_menhir_stack, _menhir_s, lhs, _startpos_lhs_) = _menhir_stack in
      let (_endpos_rhs_prime_, rhs_prime) = (_endpos, _v) in
      let _v = _menhir_action_09 _endpos_rhs_prime_ _startpos_lhs_ lhs rhs_prime in
      _menhir_goto_term _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_rhs_prime_ _v _menhir_s _tok
  
  and _menhir_run_11 : type  ttv_stack. (ttv_stack, _menhir_box_term_start) _menhir_cell1_lhs -> _ -> _ -> _ -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      match (_tok : MenhirBasics.token) with
      | BACKSLASH | LPAREN | VAR _ ->
          let MenhirCell1_lhs (_menhir_stack, _menhir_s, lhs, _startpos_lhs_) = _menhir_stack in
          let (_endpos_at_prime_, at_prime) = (_endpos, _v) in
          let _v = _menhir_action_05 _endpos_at_prime_ _startpos_lhs_ at_prime lhs in
          _menhir_goto_lhs _menhir_stack _menhir_lexbuf _menhir_lexer _startpos_lhs_ _v _menhir_s _tok
      | EOF | RPAREN ->
          let (_endpos_at_, at) = (_endpos, _v) in
          let _v = _menhir_action_06 at in
          _menhir_goto_rhs _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_at_ _v _tok
      | _ ->
          _eRR ()
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_term_start =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState00 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | LPAREN ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOO ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BACKSLASH ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
end

let term_start =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_term_start v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
