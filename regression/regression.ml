(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2010                                                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

open Unix
open Sys

type outcome = Success | Failure | Undone | Skipped

type tp_result = { ott : bool; tp : outcome }

type result = 
    { coq_t : tp_result ref;
      coq_no_list_t : tp_result ref;
      hol_t : tp_result ref;
      isa_t : tp_result ref;
(*      isa07_t : tp_result ref; *)
(*      twelf_t : tp_result ref; *)
      caml_t : tp_result ref;
      latex_t : tp_result ref }

(* ** options *)
let compute_baseline = ref false
let baseline_file_name = ref "baseline.bl"
let use_config = ref false
let config_file_name = ref "config.otr"
let todo_list_file = ref "regression.otl"
let todo_list = ref false
let tests = ref []
let isa_test = ref true
let caml_test = ref true
let coq_test = ref true
let hol_test = ref true
(* let twelf_test = ref true *)
let latex_test = ref true
let dump_baseline = ref false
let night = ref false
let jenkins = ref false
let emails = ref []
let dump_report = ref false
let keep_temporary_files = ref false
let colour_output = ref true

(* ** state *)
let progressions = ref 0
let regressions = ref 0
let ott_progressions = ref 0
let ott_regressions = ref 0
let coq_progressions = ref 0
let coq_regressions = ref 0
let coq_no_list_progressions = ref 0
let coq_no_list_regressions = ref 0
let caml_progressions = ref 0
let caml_regressions = ref 0
let isa_progressions = ref 0
let isa_regressions = ref 0
(* let isa07_progressions = ref 0 *)
(* let isa07_regressions = ref 0 *)
let hol_progressions = ref 0
let hol_regressions = ref 0
let latex_progressions = ref 0
let latex_regressions = ref 0
(* let twelf_progressions = ref 0 *)
(* let twelf_regressions = ref 0 *)
let summary = ref []
let report_fd = ref Pervasives.stdout
let config_state = ref []

let _ =
  if !night then begin
    putenv "CVSROOT" ":pserver:zappa@localhost:/usr/groups/netsem/dynsem/cvs";
    putenv "CVS_RSH" "ssh";
    putenv "PATH" "/home/yquem/moscova/zappa/bin:/home/yquem/moscova/zappa/source/godi/bin:/usr/bin:/bin";
    putenv "TWELFSERVER" "/home/yquem/moscova/zappa/lib/twelf/bin/twelf-server";
  end


(** ******************* *)
(** colour highlighting *)
(** ******************* *)

(* vt220 colour definitions *)

let black   = 0
let red     = 1
let green   = 2
let yellow  = 3
let blue    = 4
let magenta = 5
let cyan    = 6
let white   = 7
let dark_gray = 60

let _reset = "\x1b[0m"
let _color fg br = Printf.sprintf "\x1b[%u;%um" br (fg+30)
let _bold = Printf.sprintf "\x1b[%u;%um" 0 (1)
let _w = "\x1b[0;1;4m"
let _r = _color red 0
let _b = _color blue 0  (* was blue 1 *)
let _g = _color green 0

let col_wrap col s = col ^ s ^ _reset

let col_bold  s =  col_wrap  _bold s
let col_red  s =  col_wrap  _r s
let col_black  s = col_wrap  _b s
let col_green  s = col_wrap  _g s
let col_yellow  s = col_wrap  (_color yellow 0) s
let col_blue  s = col_wrap  (_color blue 0)  s
let col_magenta  s = col_wrap  (_color  magenta 0) s
let col_cyan  s = col_wrap  (_color  cyan 0) s
let col_white  s = col_wrap   (_color  white 0)  s
let col_dark_gray  s = col_wrap   (_color  dark_gray 0)  s

(* ******************************************* *)

let pp_fn s =
  Filename.basename s

let error s =
  print_endline ("regression: " ^ s);
  exit 1

let pp s =
  print_endline s
(*  if not !night then print_endline s *)


let pp_coloured c s =
  if !colour_output then pp (col_wrap (_color c black) s) else pp s

let pp_bold s =
  if !colour_output then pp (_bold ^ s ^ _reset) else pp s

let pp_tgt i_of_n s cmd = 
  pp ("*** " ^ i_of_n ^ " " ^ s ^ ": " ^ cmd)

let pp_success s name =
  pp_coloured green (" *  " ^ name ^ " " ^ s ^ ": " ^ "success")

let pp_failure s name = 
  pp_coloured red  (" *  " ^ name ^ " " ^ s ^ ": " ^ "failure")

let pp_report s =
  output_string !report_fd s;
  output_char !report_fd '\n'

let maybe_remove filename =
  if not !keep_temporary_files && Sys.file_exists filename
  then Sys.remove filename;
  ()

let execute_cmd_list l =
  List.iter
    (fun c -> 
      print_endline ("*** executing "^c); 
      let status = system c in
      match status with
      | WEXITED n -> if not (n= 0) then error ("error while executing "^c)
      | _ -> error ("error2 while executing "^c) )
    l 

let parse_todo_list () =
  let rec parse_lines fd =
    try 
      let l = input_line fd in
      let pl = Str.split (Str.regexp "[ \t]+") l in
      ( match pl with
      | t::[] -> tests := (t,[t]) :: !tests
      | n::":"::tl -> tests := (n,tl) :: !tests
      | _ -> error ("malformed line in todo_list: "^l^"\n") );
      print_endline ("todolist"^String.concat " " pl);
      parse_lines fd
    with End_of_file -> ()
  in
  if not (file_exists !todo_list_file)
  then error ("todo_list file does not exists");
  let todo_fd = open_in !todo_list_file in
  parse_lines todo_fd;
  close_in todo_fd 
  
let parse_config_file () =
  let convert c =
    match c with
    | "+" -> true
    | "." -> false
    | _ -> error "malformed entry in config file" in
  let rec parse_lines fd =
    try
      let l = input_line fd in
      let pl = Str.split (Str.regexp "[ \t]+") l in
      match pl with
      | c::cl::i::h::o::l::n::[] -> 
          let c = convert c in
          let cl = convert cl in
          let i = convert i in
(*          let i07 = convert i07 in *)
          let h = convert h in
(*	  let t = convert t in *)
          let o = convert o in
	  let l = convert l in
          config_state := (n,(c,cl,i,h,o,l))::!config_state;
	  Printf.printf "config: %s %b %b %b %b %b %b\n" n c cl i h o l;
          parse_lines fd
      | _ -> error ("malformed line in config file: "^l)
    with End_of_file -> () in
  if not (file_exists !config_file_name)
  then error ("config file does not exists");
  let config_fd = open_in !config_file_name in
  parse_lines config_fd;
  close_in config_fd

let options =
  Arg.align
    [ ("-baseline",
       Arg.Unit (fun () -> compute_baseline := true),
       " compute and save the baseline");
      ("-baseline_file",
       Arg.String (fun s -> baseline_file_name := s),
       "<"^ !baseline_file_name^">  name of baseline file");
      ("-todo_list",
       Arg.Unit (fun () -> todo_list := true),
       " use todo_list");
      ("-todo_list_file",
       Arg.String (fun s -> todo_list_file := s),
       "<"^ !todo_list_file^">  name of todo_list file");
      ("-use_config",
       Arg.Unit (fun () -> use_config := true),
       " use a configuration file");
      ("-config_file",
       Arg.String (fun s -> config_file_name := s),
       "<"^ !config_file_name^">  name of config file");
      ("-no_isa",
       Arg.Unit (fun () -> isa_test := false),
       " do not run the Isabelle test");
      ("-no_coq",
       Arg.Unit (fun () -> coq_test := false),
       " do not run the Coq test");
      ("-no_hol",
       Arg.Unit (fun () -> hol_test := false),
       " do not run the HOL test");
(*       ("-no_twelf", *)
(*        Arg.Unit (fun () -> twelf_test := false), *)
(*        " do not run the Twelf test"); *)
      ("-no_caml",
       Arg.Unit (fun () -> caml_test := false),
       " do not run the OCaml test");
      ("-no_latex",
       Arg.Unit (fun () -> latex_test := false),
       " do not run the LaTeX test");
      ("-dump_baseline",
       Arg.Unit (fun () -> dump_baseline := true),
       " dump the baseline");
      ("-night",
       Arg.Unit (fun () -> night := true),
       " perform the nightly regression test");
      ("-jenkins",
       Arg.Unit (fun () -> jenkins := true),
       " output result in XML format for Jenkins");
      ("-email",
       Arg.String (fun s -> emails := s::!emails),
       "<email> send the night report to");
      ("-report",
       Arg.Unit (fun () -> dump_report := true),
       " dump a report of the outcome of the tests");
      ("-keep_temp",
       Arg.Unit (fun () -> keep_temporary_files := true),
       " do not clean up temporary files");
      ("-no_colour",
       Arg.Unit (fun () -> colour_output := false),
       " do not use colour in output");
    ]

let rec search t state =
  match state with
  | [] -> raise Not_found
  | (x,e)::tl -> if (String.compare x t = 0) then e else search t tl

let check_config t tp =
  try
    if !use_config 
    then
      let entry = search t !config_state in
      ( match tp, entry with
      | "Coq", (c,_,_,_,_,_) -> c
      | "CoqNL", (_,cl,_,_,_,_) -> cl
      | "Isa", (_,_,i,_,_,_) -> i
(*      | "Isa07", (_,_,_,i07,_,_,_,_) -> i07 *)
      | "HOL", (_,_,_,h,_,_) -> h
(*      | "Twelf", (_,_,_,_,_,t,_,_) -> t *)
      | "OCaml", (_,_,_,_,o,_) -> o 
      | "LaTeX", (_,_,_,_,_,l) -> l
      | _,_ -> failwith "Never happen" )
    else true
  with Not_found -> print_endline ("*** test "^t^" not found in config file"); true

let run_test i n (tn,tl) =
  let i_of_n = Printf.sprintf "(%d/%d)" i n in

  let t = 
    if List.length tl = 1 
    then "-i "^(List.hd tl)
    else "-merge true -i "^String.concat " -i " tl in

  let result = { coq_t = ref { ott = false; tp = Undone };
		 coq_no_list_t = ref { ott = false; tp = Undone };
                 hol_t = ref { ott = false; tp = Undone };
                 isa_t = ref { ott = false; tp = Undone };
(*                  isa07_t = ref { ott = false; tp = Undone }; *)
(* 		 twelf_t = ref { ott = false; tp = Undone }; *)
                 caml_t = ref { ott = false; tp = Undone };
		 latex_t = ref { ott = false; tp = Undone }; } in
  pp ("\n*** " ^ i_of_n ^ " " ^ tn ^ "\n");

  (* ** preliminary *)
  let name = "testRegr"^(string_of_int (Random.int 1000)) in

  (* ** run Coq *)
  if (not !coq_test) || (not (check_config tn "Coq"))
  then result.coq_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "../bin/ott -show_sort false -show_defns false "^t ^" -o "^name^".v " (* ^" > /dev/null" *) in
    let tgt = "Ott-Coq" in
    pp_tgt i_of_n tgt cmd; 
    if (command cmd) = 0
    then begin
      pp_success tgt name;
      let cmd = "coqc -init-file _ott_coqrc.v "^name^".v > " ^ name ^ ".coq.out" (* was "/dev/null"*)  in
      let tgt = "Coq" in
      pp_tgt i_of_n tgt cmd;
      if (command cmd) = 0 then begin
	result.coq_t := { ott = true; tp = Success };
	pp_success tgt name;
	maybe_remove (name^".vo");
	maybe_remove (name^".glob");
	maybe_remove (name^".coq.out");
      end else begin
	result.coq_t := { ott = true; tp = Failure };
	pp_failure tgt name;
	maybe_remove (name^".coq.out");
      end;
      maybe_remove (name^".v")
    end else
      pp_failure tgt name;  
  end;
  (* Coq with native lists *)
  if (not !coq_test) || (not (check_config tn "CoqNL"))
  then result.coq_no_list_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "../bin/ott -coq_expand_list_types false "^t^" -o "^name^".v " (*^" > /dev/null"*) in
    let tgt = "Ott-Coq" in
    pp_tgt i_of_n tgt cmd; 
    if (command cmd) = 0
    then begin
      pp_success tgt name;
      let cmd = "coqc -init-file _ott_coqrc.v "^name^".v" in
      let tgt = "Coq" in
      pp_tgt i_of_n tgt cmd;
      if (command cmd) = 0 then begin
	result.coq_no_list_t := { ott = true; tp = Success };
	pp_success tgt name;
	maybe_remove (name^".vo");
	maybe_remove (name^".glob")
      end else begin
	result.coq_no_list_t := { ott = true; tp = Failure };
	pp_failure tgt name;
      end;
      maybe_remove (name^".v")
    end else
      pp_failure tgt name;  
  end;
  
  (* ** run Isa *)
  if (not !isa_test) || (not (check_config tn "Isa"))
  then result.isa_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "../bin/ott "^t^" -o "^name^".thy" (* ^" > /dev/null"*) in
    let tgt = "Ott-Isa" in
    pp_tgt i_of_n tgt cmd;
    if (command cmd) = 0
    then begin
      pp_success tgt name;
      let cmd =
        (* Victor's suggestion *)
        "echo '(use_thy \"" ^ name ^ "\"; OS.Process.exit OS.Process.success) handle _ => (OS.Process.exit OS.Process.failure);' | isabelle console" in
(*
	"echo 'ML_command {* (use_thy \"" ^ name
	^ "\"; OS.Process.exit OS.Process.success) handle e => (OS.Process.exit OS.Process.failure); *}'"
	^ " | isabelle console \"\"" (*^ " > /dev/null"*) in (* was isabelle tty -p *)
*)
      let tgt = "Isa" in
      pp_tgt i_of_n tgt cmd;
      if (command cmd) = 0 then begin
	result.isa_t := { ott = true; tp = Success };
	pp_success tgt name
      end else begin
	result.isa_t := { ott = true; tp = Failure };
	pp_failure tgt name;
      end;
      maybe_remove (name^".thy")
    end else
      pp_failure tgt name;  
  end;
  (* ** run Isa07 *)
(*   if (not !isa_test) || (not (check_config tn "Isa07")) *)
(*  result.isa07_t := { ott = false; tp = Skipped } ; *)
(*   else begin *)
(*     let cmd = "../bin/ott -isabelle "^name^".thy -isabelle2007_syntax " ^t ^" > /dev/null" in *)
(*     pp ("*** Ott-Isa07: " ^ cmd); *)
(*     if (command cmd) = 0 *)
(*     then begin *)
(*       pp_success ""; *)
(*       let cmd = *)
(* 	"echo 'use_thy \"" ^ name *)
(* 	^ "\" handle e => (OS.Process.exit OS.Process.failure);'" *)
(* 	^ " | isabelle > /dev/null" in       (\* FZ PUT HERE ISABELLE07 *\) *)
(*       pp ("*** Isa07: " ^ cmd); *)
(*       if (command cmd) = 0 then begin *)
(* 	result.isa07_t := { ott = true; tp = Success }; *)
(* 	pp_success "" *)
(*       end else begin *)
(* 	result.isa07_t := { ott = true; tp = Failure }; *)
(* 	pp_failure s; *)
(*       end; *)
(*       maybe_remove (name^".thy") *)
(*     end else *)
(*       pp_failure s;   *)
(*   end; *)
  
  (* ** run HOL *)
  if (not !hol_test) || (not (check_config tn "HOL"))
  then result.hol_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "../bin/ott "^t^" -o "^name^"Script.sml" (* ^" > /dev/null"*) in
    let tgt = "Ott-Hol" in
    pp_tgt i_of_n tgt cmd;
    if (command cmd) = 0
    then begin
      pp_success tgt name;
      let cmd = "Holmake -I ../hol/ "^name^"Theory.uo" (* ^ " &> /dev/null"*) in
      let tgt = "HOL" in
      pp_tgt i_of_n tgt cmd;
      if (command cmd) = 0 then begin
	result.hol_t := { ott = true; tp = Success };
	pp_success tgt name;
      end else begin
	result.hol_t := { ott = true; tp = Failure };
	pp_failure tgt name;
      end;
      maybe_remove (name^"Theory.sml");
      maybe_remove (name^"Theory.sig");
      maybe_remove (name^"Theory.ui");
      maybe_remove (name^"Script.sml");
      maybe_remove (name^"Theory.uo");
    end else
      pp_failure tgt name;  
  end;

  (* ** run Twelf *)
(*   if (not !twelf_test) || (not (check_config tn "Twelf")) *)
(*   then result.twelf_t := { ott = false; tp = Skipped } *)
(*   else begin *)
(*     let cmd = "../bin/ott -twelf "^name^".elf " ^t ^" > /dev/null" in *)
(*     pp ("*** Ott-Twelf: " ^ cmd); *)
(*     if (command cmd) = 0 *)
(*     then begin *)
(*       pp_success ""; *)
(*       let cmd = "./run_twelf "^name^".elf &> /dev/null" in *)
(*       pp ("*** Twelf: " ^ cmd); *)
(*       if (command cmd) = 0 then begin *)
(* 	result.twelf_t := { ott = true; tp = Success }; *)
(* 	pp_success "" *)
(*       end else begin *)
(* 	result.twelf_t := { ott = true; tp = Failure }; *)
(* 	pp_failure s *)
(*       end; *)
(*       maybe_remove (name^".elf"); *)
(*     end else *)
(*       pp_failure s;   *)
(*   end; *)

  (* ** run OCaml *)
  if (not !caml_test) || (not (check_config tn "OCaml"))
  then result.caml_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "../bin/ott "^t^" -o "^name^".ml" (* ^" > /dev/null"*) in
    let tgt = "Ott-OCaml" in
    pp_tgt i_of_n tgt cmd;
    if (command cmd) = 0
    then begin
      pp_success tgt name;
      let cmd = "ocamlc "^name^".ml" (* " > /dev/null"*) in
      let tgt = "OCaml" in
      pp_tgt i_of_n tgt cmd;
      if (command cmd) = 0 then begin
	result.caml_t := { ott = true; tp = Success };
	pp_success tgt name;
	maybe_remove (name^".cmi");
	maybe_remove (name^".cmo")
      end else begin
	result.caml_t := { ott = true; tp = Failure };
	pp_failure tgt name
      end;
      maybe_remove (name^".ml")
    end else
      pp_failure tgt name;  
  end;

  (* ** run LaTeX *)
  if (not !latex_test) || (not (check_config tn "LaTeX"))
  then result.latex_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "../bin/ott "^t^" -o "^name^".tex" (* ^ " > /dev/null"*) in
    let tgt = "Ott-LaTeX" in
    pp_tgt i_of_n tgt cmd;
    if (command cmd) = 0
    then begin
      pp_success tgt name;
      let cmd = "latex -interaction=batchmode "^name^".tex" (* ^ " > /dev/null"*) in
      let tgt = "LaTeX" in 
      pp_tgt i_of_n tgt cmd;
      if (command cmd) = 0 then begin
	result.latex_t := { ott = true; tp = Success };
	pp_success tgt name ;
	maybe_remove (name^".dvi");
	maybe_remove (name^".aux");
	maybe_remove (name^".log");
      end else begin
	result.latex_t := { ott = true; tp = Failure };
	pp_failure tgt name;
	maybe_remove (name^".dvi");
	maybe_remove (name^".log");
	maybe_remove (name^".aux");
      end;
      maybe_remove (name^".tex")
    end else
      pp_failure tgt name;  
  end;

  (* ** return the result *)
  result

let report tp a b =
  if a.ott && not b.ott 
  then begin
    progressions := !progressions + 1;
    ott_progressions := !ott_progressions + 1
  end else 
    if not a.ott && b.ott 
    then begin
      regressions := !regressions + 1;
      ott_regressions := !ott_regressions + 1
    end;
  
  if (a.tp = Success) && (b.tp = Failure)
  then begin
    progressions := !progressions + 1;
    ( match tp with
    | "Coq" -> coq_progressions := !coq_progressions + 1
    | "CoqNL" -> coq_no_list_progressions := !coq_no_list_progressions + 1
    | "Isa" -> isa_progressions := !isa_progressions + 1
(*    | "Isa07" -> isa07_progressions := !isa07_progressions + 1 *)
    | "HOL" -> hol_progressions := !hol_progressions + 1
(*    | "Twelf" -> twelf_progressions := !twelf_progressions + 1 *)
    | "OCaml" -> caml_progressions := !caml_progressions + 1
    | "LaTeX" -> latex_progressions := !latex_progressions + 1
    | _ -> failwith "never happens" );
    pp ("*** progression:" ^ tp) end
  else if (b.tp = Success) && (a.tp = Failure)
  then begin
    regressions := !regressions + 1;
    ( match tp with
    | "Coq" -> coq_regressions := !coq_regressions + 1
    | "CoqNL" -> coq_no_list_regressions := !coq_no_list_regressions + 1
    | "Isa" -> isa_regressions := !isa_regressions + 1
(*    | "Isa07" -> isa07_regressions := !isa07_regressions + 1 *)
    | "HOL" -> hol_regressions := !hol_regressions + 1
(*    | "Twelf" -> twelf_regressions := !twelf_regressions + 1 *)
    | "OCaml" -> caml_regressions := !caml_regressions + 1
    | "LaTeX" -> latex_regressions := !latex_regressions + 1
    | _ -> failwith "never happens" );
    pp ("*** regression:" ^ tp) end
  else ()

let print_result r =
  ( match r.ott, r.tp with
  | true, _ -> " + "
  | false, Skipped -> " ? "
  | false, _ -> " - " ) 
  ^ ( match r.tp with
  | Success -> "+ "
  | Failure -> "- "
  | Skipped -> "  "
  | Undone  -> "  " )


let dump_baseline_fc () = 
  if not (file_exists !baseline_file_name)
  then error ("baseline file does not exists");
  let baseline_fd = open_in !baseline_file_name in
  let baseline = Marshal.from_channel baseline_fd in
  pp " Coq CoqNL Isa  HOL OCaml LaTeX";
  List.iter
    ( fun (t,r) ->
      pp
        ( print_result !(r.coq_t)
	  ^ print_result !(r.coq_no_list_t)
	  ^ print_result !(r.isa_t)
(*	  ^ print_result !(r.isa07_t) *)
	  ^ print_result !(r.hol_t)
(*	  ^ print_result !(r.twelf_t) *)
	  ^ print_result !(r.caml_t)
	  ^ print_result !(r.latex_t)
	  ^ t) )
    baseline;
  close_in baseline_fd

let compute_baseline_fc () = 
  let baseline = ref [] in
  let n_tests = List.length !tests in 
  List.iteri
    ( fun i -> 
      fun t ->
      let result_t = run_test i n_tests t in
      baseline := ((fst t),result_t)::!baseline )
    (List.rev !tests);
  if file_exists !baseline_file_name then remove !baseline_file_name;
  let baseline_fd = open_out_bin !baseline_file_name in
  Marshal.to_channel baseline_fd (List.rev !baseline) [];
  close_out baseline_fd;
  pp "\n*** baseline built succesfully"

let test_fc auto =
  (* ** open the baseline file *)
  if not (file_exists !baseline_file_name)
  then error ("baseline file does not exists");
  let baseline_fd = open_in_bin !baseline_file_name in
  let baseline = (Marshal.from_channel baseline_fd : (string * result) list) in
  print_endline "content of baseline";
  List.iter (fun (n,_) -> print_endline n) baseline;
  print_endline "end content of baseline";

  (* ** for each test *)
  let n_tests = List.length !tests in 
  List.iteri
    ( fun i -> 
      fun (tn,tl) ->
      let result_t = run_test i n_tests (tn,tl) in
      summary := (tn,result_t)::!summary;
      try
        let result_baseline = List.assoc tn baseline in
        report "Coq" !(result_t.coq_t) !(result_baseline.coq_t);
        report "CoqNL" !(result_t.coq_no_list_t) !(result_baseline.coq_no_list_t);
        report "Isa" !(result_t.isa_t) !(result_baseline.isa_t);
(*        report "Isa07" !(result_t.isa07_t) !(result_baseline.isa07_t); *)
        report "HOL" !(result_t.hol_t) !(result_baseline.hol_t);
(*        report "Twelf" !(result_t.twelf_t) !(result_baseline.twelf_t); *)
        report "OCaml" !(result_t.caml_t) !(result_baseline.caml_t);
        report "LaTeX" !(result_t.latex_t) !(result_baseline.latex_t);
      with Not_found -> pp ("*** test " ^ tn ^ " not in the baseline") )
    (List.rev !tests);
  (* ** print summary *)
  pp_report ("\n*** final report");

  if !dump_report then begin
    pp_report "\n*** results";
    pp_report "\n Coq CoqNL Isa HOL OCaml LaTeX";
    List.iter
      ( fun (t,r) ->
        pp_report
          ( print_result !(r.coq_t)
	    ^ print_result !(r.coq_no_list_t)
	    ^ print_result !(r.isa_t)
(*	    ^ print_result !(r.isa07_t) *)
	    ^ print_result !(r.hol_t)
(*	    ^ print_result !(r.twelf_t) *)
            ^ print_result !(r.caml_t)
            ^ print_result !(r.latex_t)
	    ^ pp_fn t ) )
      !summary;
  end;

  pp_report
    ( "\n*** progressions: " ^ (string_of_int !progressions)
      ^ " (Ott : " ^ (string_of_int !ott_progressions)^")"
      ^ " (Coq : " ^ (string_of_int !coq_progressions)^")"
      ^ " (CoqNL : " ^ (string_of_int !coq_no_list_progressions)^")"
      ^ " (Isa : " ^ (string_of_int !isa_progressions)^")"
(*      ^ " (Isa07 : " ^ (string_of_int !isa07_progressions)^")" *)
      ^ " (Hol : " ^ (string_of_int !hol_progressions)^")" 
(*      ^ " (Twelf : " ^ (string_of_int !twelf_progressions)^")"  *)
      ^ " (OCaml : " ^ (string_of_int !caml_progressions)^")" 
      ^ " (LaTeX : " ^ (string_of_int !latex_progressions)^")" );
  pp_report
    ("*** regressions:  " ^ (string_of_int !regressions)
     ^ " (Ott : " ^ (string_of_int !ott_regressions)^")"
     ^ " (Coq : " ^ (string_of_int !coq_regressions)^")"
     ^ " (CoqNL : " ^ (string_of_int !coq_no_list_regressions)^")"
     ^ " (Isa : " ^ (string_of_int !isa_regressions)^")"
(*     ^ " (Isa07 : " ^ (string_of_int !isa07_regressions)^")" *)
     ^ " (Hol : " ^ (string_of_int !hol_regressions)^")"
(*     ^ " (Twelf : " ^ (string_of_int !twelf_regressions)^")"  *)
     ^ " (OCaml : " ^ (string_of_int !caml_regressions)^")"
     ^ " (LaTeX : " ^ (string_of_int !latex_progressions)^")" );
  
  let p_out n b =
    let s_ott =
      if n.tp = Skipped then " S " else
      if n.ott && not b.ott then " + " else 
      if b.ott && not n.ott then " - " else "   " in
    let s_tp = 
      if (b.tp = Success) && (n.tp = Failure) then "- "
      else if (b.tp = Failure) && (n.tp = Success) then "+ "
      else if (n.tp = Skipped) || (b.tp = Skipped) then "  "
      else "  " in
    s_ott ^ s_tp in

  pp_report "\n Coq CoqNL Isa HOL OCaml LaTeX";
  List.iter
    ( fun (t,r) ->
      try
	let b = List.assoc t baseline in
        pp_report
          ( p_out !(r.coq_t) !(b.coq_t)
	    ^ p_out !(r.coq_no_list_t) !(b.coq_no_list_t)
	    ^ p_out !(r.isa_t) !(b.isa_t)
(*	    ^ p_out !(r.isa07_t) !(b.isa07_t) *)
	    ^ p_out !(r.hol_t) !(b.hol_t)
(*	    ^ p_out !(r.twelf_t) !(b.twelf_t) *)
	    ^ p_out !(r.caml_t) !(b.caml_t)
	    ^ p_out !(r.latex_t) !(b.latex_t)
	    ^ pp_fn t )
      with Not_found -> pp_report ("  ?    ?    ?    ?    ?     ?  " ^ t) )
    !summary;
  close_in baseline_fd;

  if auto && (!regressions = 0) && (!progressions > 0)
  then begin
    if file_exists !baseline_file_name then remove !baseline_file_name;
    let baseline_fd = open_out_bin !baseline_file_name in
    Marshal.to_channel baseline_fd !summary [];
    close_out baseline_fd;
  end

let main () =
  match !dump_baseline, !compute_baseline with
  | true, _ -> dump_baseline_fc ()
  | false, true -> compute_baseline_fc ()
  | false, false -> test_fc !night

let _ =
  Random.self_init ();
  Arg.parse options
    (fun s -> tests := (s,[s]) :: !tests)
    ("\n" ^ "regression <options> <test1> .. <testn> \n");
  tests := List.rev !tests;
  if ((List.length !tests) = 0) && not (!dump_baseline) && not (!todo_list)
  then error "specify at least one test";
  if !night 
  then begin
    putenv "PATH" "/home/yquem/moscova/zappa/bin:/home/yquem/moscova/zappa/source/godi/bin:/usr/bin:/bin";
    putenv "TWELFSERVER" "/home/yquem/moscova/zappa/lib/twelf/bin/twelf-server";
    chdir "/home/yquem/moscova/zappa/repo/update/Ott2/src";
    execute_cmd_list [ "./regression_night_script.sh" ];
(*     chdir "/home/yquem/moscova/zappa/repo/update/Ott2/tests/"; *)
(*     execute_cmd_list [ "cvs update" ]; *)
(*     chdir "/home/yquem/moscova/zappa/repo/update/Ott2/examples/tapl/"; *)
(*     execute_cmd_list [ "cvs update" ]; *)
(*     chdir "/home/yquem/moscova/zappa/repo/update/Ott2/src"; *)
(*     let cmd_list =  *)
(*       [ "env"; *)
(* 	"cvs update"; *)
(*         "make > /dev/null"; *)
(*         "make tmp_test7a.ott"; *)
(* 	"make tmp_test7.ott" ] in *)
(*     execute_cmd_list cmd_list; *)
    chdir "/home/yquem/moscova/zappa/repo/update/Ott2/src";
    report_fd := open_out "report.txt";
  end;
  if !use_config then parse_config_file ();
  if !todo_list then parse_todo_list ();
  main ();
  if !night then begin
    close_out !report_fd;
    let date = Unix.localtime (Unix.time ()) in
    let subject = 
      Printf.sprintf ("[Ott regression report] %d/%d/%d") 
        date.tm_mday
        date.tm_mon
        (1900 + date.tm_year) in
    let cmd_list = 
      List.map 
        (fun e -> "mail -s '" ^ subject ^ "' " ^ e ^ " < report.txt" )
        !emails in
    execute_cmd_list cmd_list
  end;

  if !jenkins then begin
    let fd = open_out "tests.xml" in
    output_string fd "<testsuite tests=\"1\">\n";
    if !regressions == 0
    then begin
      output_string fd "  <testcase classname=\"regression\" name=\"SuccessfulRegressionTest\"/>\n";
    end else begin
      output_string fd "  <testcase classname=\"regression\" name=\"FailureRegressionTest\">\n";
      output_string fd "    <failure type=\"FailureRegression\">\n";
      output_string fd "      todo\n";
      output_string fd "    <failure>\n";
      output_string fd "  </testcase>\n";
    end;
    output_string fd "</testsuite>\n";
    close_out fd
  end
