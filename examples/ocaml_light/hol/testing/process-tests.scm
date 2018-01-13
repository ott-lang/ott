#!/home/so294/scratch/plt/bin/mzscheme -qr

(require (lib "process.ss")
         (lib "plt-match.ss")
         (lib "port.ss"))

(define infile "tests")
(define outfile "tests.sml")
(define filter "../ocamlpp/filter")
(define run-tests "run_tests.sml")

(define ip (open-input-file infile))
(define op (open-output-file outfile #:exists 'replace))

(fprintf op #<<end-string
val init_substs_def = new_definition ("init_substs",
``init_substs = [(VN_id "raise", Expr_uprim Uprim_raise);
                 (VN_id "not", Expr_uprim Uprim_not);
                 (VN_id "~~-", Expr_uprim Uprim_minus);
                 (VN_id "ref", Expr_uprim Uprim_ref);
                 (VN_id "!", Expr_uprim Uprim_deref);
                 (VN_id "=", Expr_bprim Bprim_equal);
                 (VN_id "+", Expr_bprim Bprim_plus);
                 (VN_id "-", Expr_bprim Bprim_minus);
                 (VN_id "*", Expr_bprim Bprim_times);
                 (VN_id "/", Expr_bprim Bprim_div);
                 (VN_id ":=", Expr_bprim Bprim_assign)]``);

end-string
)

(fprintf op "val tests = (\n")
(flush-output op)

(define test-indices
  (let loop ([i 1])
    (define match (regexp-match "TESTEXPR|TESTSTUCK|TESTDEFS" ip))
    (cond
      [(equal? match '(#"TESTEXPR"))
       (fprintf op #<<end-string
new_definition ("test~a", ``test~a = substs_value_name_program init_substs
  (Prog_defs (Ds_cons (D_let (LB_simple P_any (Expr_apply (Expr_uprim Uprim_raise) 

end-string
                i i)
       (flush-output op)
       (match-let (((list #f to-filter id #f proc) (process/ports op #f (current-output-port) filter)))
         (regexp-match "EXPECT" ip 0 #f to-filter)
         (close-output-port to-filter)
         (proc 'wait))
       (fprintf op "))) Ds_nil))``)::\n")
       (fprintf op #<<end-string
new_definition ("result~a", ``result~a = substs_value_name_program init_substs (Prog_raise (

end-string
                i i)
       (flush-output op)
       (match-let (((list #f to-filter id #f proc) (process/ports op #f (current-output-port) filter)))
         (regexp-match "END" ip 0 #f to-filter)
         (close-output-port to-filter)
         (proc 'wait))
       (fprintf op "))``)::\n")
       (cons (cons i 'expr)
             (loop (add1 i)))]
      [(equal? match '(#"TESTDEFS"))
       (fprintf op #<<end-string
new_definition ("test~a", ``test~a = substs_value_name_program init_substs
  (Prog_defs (definitions_snoc (list_to_defs

end-string
                i i)
       (flush-output op)
       (match-let (((list #f to-filter id #f proc) (process/ports op #f (current-output-port) filter)))
         (regexp-match "EXPR" ip 0 #f to-filter)
         (close-output-port to-filter)
         (proc 'wait))
       (fprintf op ")\n(D_let (LB_simple P_any (Expr_apply (Expr_uprim Uprim_raise) ")
       (flush-output op)
       (match-let (((list #f to-filter id #f proc) (process/ports op #f (current-output-port) filter)))
         (regexp-match "EXPECT" ip 0 #f to-filter)
         (close-output-port to-filter)
         (proc 'wait))
       (fprintf op ")))))``)::\n")
       (fprintf op #<<end-string
new_definition ("result~a", ``result~a = substs_value_name_program init_substs (Prog_raise (

end-string
                i i)
       (flush-output op)
       (match-let (((list #f to-filter id #f proc) (process/ports op #f (current-output-port) filter)))
         (regexp-match "END" ip 0 #f to-filter)
         (close-output-port to-filter)
         (proc 'wait))
       (fprintf op "))``)::\n")
       (cons (cons i 'expr)
             (loop (add1 i)))]
      [(equal? match '(#"TESTSTUCK"))
       (fprintf op #<<end-string
new_definition ("test~a", ``test~a = substs_value_name_expr init_substs (

end-string
                i i)
       (flush-output op)
       (match-let (((list #f to-filter id #f proc) (process/ports op #f (current-output-port) filter)))
         (regexp-match "END" ip 0 #f to-filter)
         (close-output-port to-filter)
         (proc 'wait))
       (fprintf op ")``)::\n")
       (cons (cons i 'stuck) 
             (loop (add1 i)))]
      [else
       null])))

(close-input-port ip)

(fprintf op "[]);\n")

(fprintf op #<<end-string
val _ =
 let open EmitML combinSyntax
 in emitML (".")
     ("tests",
      map MLSIG sigs @
      OPEN ["num", "list", "string", "option", "caml_typedef"] ::
      map (DEFN o wordsLib.WORDS_EMIT_RULE) (init_substs_def::tests))
 end;

end-string
        )
(close-output-port op)

(define op (open-output-file run-tests #:exists 'replace))

(fprintf op #<<end-string
Control.polyEqWarn := false;
CM.make "sources1.cm";
CM.make "$smlnj-tdp/coverage.cm";
SMLofNJ.Internals.TDP.mode := true;
open Coverage;
Coverage.install();
CM.make "sources2.cm";

local
open testsML caml_typedefML defs_red_funML reduction_funML;
in

fun is_stuck_expr expr = 
  case red expr of
      Stuck => true
    | _ => false;

fun eval prog = 
  let fun loop (store, (defs, Prog_raise r)) = Prog_raise r
        | loop (store, (defs, Prog_defs Ds_nil)) = Prog_defs Ds_nil
        | loop (state as (store, (defs, Prog_defs ds))) =
          (case top_red max_alloc state of
             NONE => Prog_defs ds 
           | SOME state2 => loop state2)
  in
    loop ([], (Ds_nil, prog))
  end;
end;

Control.Print.printDepth := 100;

end-string
         )
(let loop ([idx test-indices])
  (unless (null? idx)
    (let ([i (caar idx)]
          [type (cdar idx)])
      (case type
        [(expr)
         (fprintf op "val answer~a = eval testsML.test~a = testsML.result~a;\n" i i i)]
        [(stuck)
         (fprintf op "val answer~a = is_stuck_expr testsML.test~a;\n" i i)])
      (loop (cdr idx)))))

(fprintf op #<<end-string
not_covered [functions, tail_calls, non_tail_calls];

end-string
        )
(close-output-port op)
