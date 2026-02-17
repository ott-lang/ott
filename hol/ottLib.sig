signature ottLib = sig
  include Abbrev;
  val ottDefine : string -> term frag list -> thm;
  val RULE_INDUCT_TAC : thm -> thm list -> (term list * tactic) list -> tactic;
  val INDUCT_TAC : thm -> thm list -> (term list * tactic) list -> tactic;
  val get_terms : thm -> term list;
  val structural_cases : thm list -> int -> term list list -> thm -> thm;
end
