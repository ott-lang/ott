signature ottLib = sig
  type thm = Thm.thm;
  type term = Term.term;
  type 'a frag = 'a Portable.frag;
  val ottDefine : string -> term frag list -> thm
  val RULE_INDUCT_TAC : Thm.thm -> Thm.thm list -> (Term.term list * Tactic.tactic) list -> Tactic.tactic
  val INDUCT_TAC : Thm.thm -> Thm.thm list -> (Term.term list * Tactic.tactic) list -> Tactic.tactic
  val get_terms : Thm.thm -> Term.term list
  val structural_cases : Thm.thm list -> int -> Term.term list list -> Thm.thm -> Thm.thm
end
