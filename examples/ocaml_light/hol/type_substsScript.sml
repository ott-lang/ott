open bossLib HolKernel boolLib listTheory;
open ottTheory caml_typedefTheory;
open basicTheory utilTheory;

val _ = new_theory "type_substs";

val substs_tv_empty_thm = Q.store_thm ("substs_tv_empty_thm",
`(!t. substs_typevar_typexpr [] t = t) /\
 (!tl. MAP (substs_typevar_typexpr []) tl = tl)`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def, list_assoc_def] THEN METIS_TAC []);

val substs_typevar_typexpr_drop_lem = Q.store_thm ("substs_typevar_typexpr_drop_lem",
`!subst t tv t'. ~MEM tv (ftv_typexpr t) ==>
       (substs_typevar_typexpr ((tv, t')::subst) t = substs_typevar_typexpr subst t)`,
recInduct substs_typevar_typexpr_ind THEN
SRW_TAC [] [substs_typevar_typexpr_def, ftv_typexpr_def, list_assoc_def, MAP_EQ, MEM_FLAT, EVERY_MAP,
                EVERY_MEM]);



val substs_typevar_typexpr_id_lem = Q.store_thm ("substs_typevar_typexpr_id_lem",
`!subst t. (ftv_typexpr t = []) ==> (substs_typevar_typexpr subst t = t)`,
recInduct substs_typevar_typexpr_ind THEN
SRW_TAC [] [substs_typevar_typexpr_def, ftv_typexpr_def] THEN
Induct_on `typexpr_list` THEN SRW_TAC [] []);




val _ = export_theory ();

