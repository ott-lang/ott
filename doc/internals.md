# Ott Internals

## Symbolic terms
A key component of Ott's internal representation are the symbolic terms.
These follow a structure defined by the object language's grammar and are a little like abstract syntax trees.
The key differences are:

1. What might be a subtree in an AST can be represented by a single node that is abstract and is just
a place holder for a non-terminal.

2. A symterm can include a list form as a component to represent, abstractly, a list of further symterms of indefinite length
In an actual AST this would be a concrete list of definite of AST child nodes.

Given the above, the relation between ASTs and symterms is that an AST maps to one symterm whilst a single
symterm represents a family of ASTs.

For example, the string
```
if true then t2 else t3
```
has the following symterm representation
```
(St_node :t:TmIf: (Ste_st (St_node :t:TmTrue: )) (Ste_st (St_nonterm t2)) (Ste_st (St_nonterm t3)))
```
The top level node is a symterm node (St_node) that has a list of 3  symterm elements that are themselves symterms.
The first is a concrete symterm node for True and the other two are symterm nodes for the non-terminals t2 and t3 which are terms
in the object language.

In terms of AST's, the symterm would represent a family of ASTs with an IF-node as root where the guard is True but the two branches are any term.



## Datatypes
Key datatypes are in [types.ml](https://github.com/rems-project/ott/src/types.ml).
We present datatypes from this file below but with non-key constructors elided.

The top-level datatype is `systemdefn` that holds a complete system definition from the input files
specified on the command line.
Source structure is stored in the structure field.

```OCaml
and systemdefn =  (* sd *)
    { syntax : syntaxdefn;
      relations : relationsdefn;
      structure : structure;
      sources : string}
```

The syntax definition datatype is
```Ocaml
and syntaxdefn = (* xd *)  (* all the nt occurrences are fully resolved *)
    { xd_mds : metavardefn list;   
      xd_rs  : rule list; 
      ...
      xd_embed_preamble : embed list;
      xd_embed : embed list;
      xd_isa_imports : string list;
      ...
      }
```

Non-terminals in the grammar are defined by rules that comprise a list of productions.

```OCaml
and rule =  (* r *)
    { rule_ntr_name : nontermroot; 
      rule_ntr_names : (nontermroot * homomorphism list) list;   
      rule_pn_wrapper : string;
      rule_ps : prod list;
      rule_homs : homomorphism list;
      ...
 }
```

```OCaml
Key parts of a production are its name, a list of elements and a hom list.
and prod = (* p *)
    { prod_name : prodname;
      ...
      prod_es : element list;
      prod_homs : homomorphism list;
      ...
      }
```

```OCaml
and element = (* e *)
  | Lang_nonterm of nontermroot * nonterm  (* primary, as-written *)
  | Lang_metavar of metavarroot * metavar  (* primary, as-written *)
  | Lang_terminal of terminal
  | Lang_option of element list    (* not currently implemented *)
  | Lang_sugaroption of terminal   (* not currently implemented *)
  | Lang_list of element_list_body

and element_list_body = (* elb *)
    { elb_boundo : bound option;
      elb_tmo : terminal option;
      elb_es : element list ;} 
```

The definitions of judgements are in

```OCaml
and defnclass =  (* dc *)
    { dc_name : defnclassname; 
      dc_homs : homomorphism list;
      ...
      dc_defns : defn list; (* defns of each judgement *)
      ...
 }
```

Key parts of a definition are its name, form and its rules.

```OCaml
and defn =  (* d *)
    { d_name : defnname;   (* eg Eet - the base for the proof asst reln name*)
      d_form : symterm;  (* eg E |- expr : typexpr *)
      d_wrapper : string;  (* prefix for individual rules, eg Eet_ *)
      d_rules : processed_semiraw_rule list;
      d_homs : homomorphism list;
      d_loc : loc }

and drule =  (* dr *)
    { drule_name : defnrulename;                (* eg Eet_value_name *)
      drule_categories : StringSet.t;
      drule_premises : (string option * symterm * (homomorphism list) ) list;
      drule_conclusion : symterm;
      drule_homs : homomorphism list;
      drule_loc : loc }

and fun_or_reln_defnclass = (* frdc *)
  | FDC of fundefnclass
  | RDC of defnclass

and relationsdefn = fun_or_reln_defnclass list  (* rd *)
```

## Processing pipeline

(Mention can interleave -i and -o on command line and so export out partial systems)