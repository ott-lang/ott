theory test10st_codegen 
imports test10st_snapshot_out Executable_Set
begin

ML "reset Codegen.quiet_mode"

(* Code generation for the test10st simply typed lambda calculus. *)

constdefs
 ta :: t
"ta == (t_App (t_Lam ''z'' (t_Var ''z''))) (t_Lam ''y'' (t_Var ''y''))"
;

code_module Test10st_codegen file "test10st_codegen.ml" contains 
(*is_v
tsubst_T
tsubst_t*)
reduce_ta  = "(ta,_):reduce"


(* ...to build and demo the resulting test10st_codegen.ml code...

Isabelle test10st_codegen.thy
...`use' that...

...in a shell...
isabelle
use "test10st_codegen.ml";
open Test10st_codegen;

...a test term...
ta;
val it = t_App (t_Lam (["z"], t_Var ["z"]), t_Lam (["y"], t_Var ["y"]))

...a sample reduction...
DSeq.hd(reducep__1 ta);
val it = t_Lam (["y"], t_Var ["y"]) : Test10st_codegen.t 

*)

end
