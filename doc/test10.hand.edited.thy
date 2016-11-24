theory out = Main:
(** syntax *)
types termvar = "string"

datatype 
t = 
   t_Var "termvar"
 | t_Lam "termvar" "t"
 | t_App "t" "t"

(** subrules *)
consts
is_v :: "t => bool"

primrec
"is_v ((t_Var x)) = False"
"is_v ((t_Lam x t)) = (True)"
"is_v ((t_App t t')) = False"

(** substitutions *)
consts
tsubst_t :: "t => termvar => t => t"

primrec
"tsubst_t t0 termvar0 (t_Var x) = 
  (if x=termvar0 then t0 else (t_Var x))"
"tsubst_t t0 termvar0 (t_Lam x t) = 
  (t_Lam x (if termvar0 mem [x] then t else (tsubst_t t0 termvar0 t)))"
"tsubst_t t0 termvar0 (t_App t t') = 
  (t_App (tsubst_t t0 termvar0 t) (tsubst_t t0 termvar0 t'))"

(** definitions *)
(*defns Jop *)
consts
  E :: "(t*t) set"
inductive E
intros

(* defn E *)

ax_appI: "[|is_v v2|] ==> 
 ( (t_App T v2) , ( tsubst_t  v2   x   t12  ) ) : E"

ctx_app_funI: "[| ( t1 , t1' ) : E|] ==> 
 ( (t_App t1 t) , (t_App t1' t) ) : E"

ctx_app_argI: "[|is_v v ;
 ( t1 , t1' ) : E|] ==> 
 ( (t_App v t1) , (t_App v t1') ) : E"

end
