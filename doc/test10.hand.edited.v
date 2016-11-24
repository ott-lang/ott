Require Import List.  Require Import Arith.
(** syntax *)
Definition termvar_t := nat.
Lemma eq_termvar_t: forall (x y : termvar_t), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.


Inductive 
t_t : Set := 
   t_Var : termvar_t -> t_t
 | t_Lam : termvar_t -> t_t -> t_t
 | t_App : t_t -> t_t -> t_t
.

(** subrules *)
Definition is_v (t0:t_t) : Prop :=
  match t0 with
  | (t_Var x) => False
  | (t_Lam x t) => (True)
  | (t_App t t') => False
end.

(** substitutions *)

Fixpoint list_mem (A:Set) (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=
  match l with
  | nil => false
  | cons h t => if eq h x then true else list_mem A eq x t
end.
Implicit Arguments list_mem.

Fixpoint tsubst_t (t0:t_t) (termvar0:termvar_t) (t1:t_t) {struct t1} : t_t :=
  match t1 with
  | (t_Var x) => if eq_termvar_t x termvar0 then t0 else (t_Var x)
  | (t_Lam x t) => t_Lam x (if list_mem eq_termvar_t termvar0 (cons x nil) then t else (tsubst_t t0 termvar0 t))
  | (t_App t t') => t_App (tsubst_t t0 termvar0 t) (tsubst_t t0 termvar0 t')
end.


(** definitions *)
(* defns Jop *)

Inductive
(* defn E *)

E : t_t -> t_t -> Prop :=
 | ax_app : forall v2 x t12,
     is_v v2 ->
     E (t_App T v2) ( tsubst_t  v2   x   t12  )
 | ctx_app_fun : forall t1 t1' t,
     E t1 t1' ->
     E (t_App t1 t) (t_App t1' t)
 | ctx_app_arg : forall t1 v t1',
     is_v v ->
     E t1 t1' ->
     E (t_App v t1) (t_App v t1')

.