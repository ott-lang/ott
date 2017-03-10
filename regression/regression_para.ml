(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2006                                                   *)
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
      hol_t : tp_result ref;
      isa_t : tp_result ref;
      twelf_t : tp_result ref;
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
let twelf_test = ref true
let latex_test = ref true
let dump_baseline = ref false
let night = ref false
let emails = ref []
let dump_report = ref false

(* ** state *)
let progressions = ref 0
let regressions = ref 0
let ott_progressions = ref 0
let ott_regressions = ref 0
let coq_progressions = ref 0
let coq_regressions = ref 0
let caml_progressions = ref 0
let caml_regressions = ref 0
let isa_progressions = ref 0
let isa_regressions = ref 0
let hol_progressions = ref 0
let hol_regressions = ref 0
let latex_progressions = ref 0
let latex_regressions = ref 0
let twelf_progressions = ref 0
let twelf_regressions = ref 0
let summary = ref []
let report_fd = ref Pervasives.stdout
let config_state = ref []

let _ =
  putenv "CVSROOT" ":pserver:zappa@localhost:/usr/groups/netsem/dynsem/cvs";
  putenv "CVS_RSH" "ssh";
  putenv "PATH" "/home/nis/zappanar/source/coq/bin:/home/nis/zappanar/source/Isabelle/bin:/home/nis/zappanar/source/hol98/bin:/home/nis/zappanar/source/ocaml/bin:/usr/bin:/bin";
  putenv "TWELFSERVER" "/home/nis/zappanar/source/twelf/bin/twelf-server";
  print_endline "CIAO"

 

let pp_fn s =
  Filename.basename s

let error s =
  print_endline ("regression: " ^ s);
  exit 1

let pp s =
  if not !night then print_endline s

let pp_report s =
  output_string !report_fd s;
  output_char !report_fd '\n'

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
      | c::i::h::t::o::l::n::[] -> 
          let c = convert c in
          let i = convert i in
          let h = convert h in
	  let t = convert t in
          let o = convert o in
	  let l = convert l in
          config_state := (n,(c,i,h,t,o,l))::!config_state;
	  Printf.printf "config: %s %b %b %b %b %b %b\n" n c i h t o l;
          parse_lines fd
      | _ -> error "malformed line in config file"
    with End_of_file -> () in
  if not (file_exists !config_file_name)
  then error ("config file does not exists");
  let config_fd = open_in !config_file_name in
  parse_lines config_fd;
  close_in config_fd


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
      | "Isa", (_,i,_,_,_,_) -> i
      | "HOL", (_,_,h,_,_,_) -> h
      | "Twelf", (_,_,_,t,_,_) -> t
      | "OCaml", (_,_,_,_,o,_) -> o 
      | "LaTeX", (_,_,_,_,_,l) -> l
      | _,_ -> failwith "Never happen" )
    else true
  with Not_found -> print_endline ("*** test "^t^" not found in config file"); true

let run_test (tn,tl) =
  let t = 
    if List.length tl = 1 
    then List.hd tl
    else "-merge true "^String.concat " " tl in

  let result = { coq_t = ref { ott = false; tp = Undone };
                 hol_t = ref { ott = false; tp = Undone };
                 isa_t = ref { ott = false; tp = Undone };
		 twelf_t = ref { ott = false; tp = Undone };
                 caml_t = ref { ott = false; tp = Undone };
		 latex_t = ref { ott = false; tp = Undone }; } in
  pp ("\n*** " ^ tn ^ "\n");

  (* ** preliminary *)
  let name = "testRegr"^(string_of_int (Random.int 1000)) in

  (* ** run Coq *)
  if (not !coq_test) || (not (check_config tn "Coq"))
  then result.coq_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -coq "^name^".v " ^t ^" > /dev/null" in
    pp ("*** Ott-Coq: " ^ cmd);
    if (command cmd) = 0
    then begin
      pp (" *  success");
      let cmd = "coqc "^name^".v > /dev/null" in
      pp ("*** Coq: " ^ cmd);
      if (command cmd) = 0 then begin
	result.coq_t := { ott = true; tp = Success };
	pp (" *  success");
	remove (name^".vo")
      end else begin
	result.coq_t := { ott = true; tp = Failure };
	pp (" *  failure");
      end;
      remove (name^".v")
    end else
      pp (" *  failure");  
  end;
  
  (* ** run Isa *)
  if (not !isa_test) || (not (check_config tn "Isa"))
  then result.isa_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -isabelle "^name^".thy " ^t ^" > /dev/null" in
    pp ("*** Ott-Isa: " ^ cmd);
    if (command cmd) = 0
    then begin
      pp (" *  success");
      let cmd =
	"echo 'use_thy \"" ^ name
	^ "\" handle e => (OS.Process.exit OS.Process.failure);'"
	^ " | isabelle > /dev/null" in
      pp ("*** Isa: " ^ cmd);
      if (command cmd) = 0 then begin
	result.isa_t := { ott = true; tp = Success };
	pp (" *  success")
      end else begin
	result.isa_t := { ott = true; tp = Failure };
	pp (" *  failure");
      end;
      remove (name^".thy")
    end else
      pp (" *  failure");  
  end;
  
  (* ** run HOL *)
  if (not !hol_test) || (not (check_config tn "HOL"))
  then result.hol_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -hol "^name^"Script.sml " ^t ^" > /dev/null" in
    pp ("*** Ott-Hol: " ^ cmd);
    if (command cmd) = 0
    then begin
      pp (" *  success");
      let cmd = "Holmake "^name^"Theory.uo &> /dev/null" in
      pp ("*** HOL: " ^ cmd);
      if (command cmd) = 0 then begin
	result.hol_t := { ott = true; tp = Success };
	pp (" *  success")
      end else begin
	result.hol_t := { ott = true; tp = Failure };
	pp (" *  failure")
      end;
      if file_exists (name^"Theory.sml") then remove (name^"Theory.sml");
      if file_exists (name^"Theory.sig") then remove (name^"Theory.sig");
      if file_exists (name^"Theory.ui") then remove (name^"Theory.ui");
      if file_exists (name^"Script.sml") then remove (name^"Script.sml");
      if file_exists (name^"Theory.uo") then remove (name^"Theory.uo");
    end else
      pp (" *  failure");  
  end;

  (* ** run Twelf *)
  if (not !twelf_test) || (not (check_config tn "Twelf"))
  then result.twelf_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -twelf "^name^".elf " ^t ^" > /dev/null" in
    pp ("*** Ott-Twelf: " ^ cmd);
    if (command cmd) = 0
    then begin
      pp (" *  success");
      let cmd = "./run_twelf "^name^".elf &> /dev/null" in
      pp ("*** Twelf: " ^ cmd);
      if (command cmd) = 0 then begin
	result.twelf_t := { ott = true; tp = Success };
	pp (" *  success")
      end else begin
	result.twelf_t := { ott = true; tp = Failure };
	pp (" *  failure")
      end;
      if file_exists (name^".elf") then remove (name^".elf");
    end else
      pp (" *  failure");  
  end;

  (* ** run OCaml *)
  if (not !caml_test) || (not (check_config tn "OCaml"))
  then result.caml_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -caml "^name^".ml " ^t ^" > /dev/null" in
    pp ("*** Ott-Ocaml: " ^ cmd);
    if (command cmd) = 0
    then begin
      pp (" * success");
      let cmd = "ocamlc "^name^".ml > /dev/null" in
      pp ("*** OCaml: " ^ cmd);
      if (command cmd) = 0 then begin
	result.caml_t := { ott = true; tp = Success };
	pp (" *  success");
	remove (name^".cmo")
      end else begin
	result.caml_t := { ott = true; tp = Failure };
	pp (" *  failure")
      end;
      remove (name^".ml")
    end else
      pp (" *  failure");  
  end;

  (* ** run LaTeX *)
  if (not !latex_test) || (not (check_config tn "LaTeX"))
  then result.latex_t := { ott = false; tp = Skipped }
  else begin
    let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -tex "^name^".tex " ^t ^" > /dev/null" in
    pp ("*** Ott-LaTeX: " ^ cmd);
    if (command cmd) = 0
    then begin
      pp (" * success");
      let cmd = "latex -interaction=batchmode "^name^".tex > /dev/null" in
      pp ("*** LaTeX: " ^ cmd);
      if (command cmd) = 0 then begin
	result.latex_t := { ott = true; tp = Success };
	pp (" *  success");
	remove (name^".dvi");
	remove (name^".aux");
	remove (name^".log");
      end else begin
	result.latex_t := { ott = true; tp = Failure };
	pp (" *  failure");
	if file_exists (name^".log") then remove (name^".log");
	if file_exists (name^".aux") then remove (name^".aux");
      end;
      remove (name^".tex")
    end else
      pp (" *  failure");  
  end;

  (* ** return the result *)
  result

let run_test_p (tn,tl) =
  (tn, run_test(tn,tl))

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
    | "Isa" -> isa_progressions := !isa_progressions + 1
    | "HOL" -> hol_progressions := !hol_progressions + 1
    | "Twelf" -> twelf_progressions := !twelf_progressions + 1
    | "OCaml" -> caml_progressions := !caml_progressions + 1
    | "LaTeX" -> latex_progressions := !latex_progressions + 1
    | _ -> failwith "never happens" );
    pp ("*** progression:" ^ tp) end
  else if (b.tp = Success) && (a.tp = Failure)
  then begin
    regressions := !regressions + 1;
    ( match tp with
    | "Coq" -> coq_regressions := !coq_regressions + 1
    | "Isa" -> isa_regressions := !isa_regressions + 1
    | "HOL" -> hol_regressions := !hol_regressions + 1
    | "Twelf" -> twelf_regressions := !twelf_regressions + 1
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
  pp " Coq  Isa  HOL Twelf OCaml LaTeX";
  List.iter
    ( fun (t,r) ->
      pp
        ( print_result !(r.coq_t)
	  ^ print_result !(r.isa_t)
	  ^ print_result !(r.hol_t)
	  ^ print_result !(r.twelf_t)
	  ^ print_result !(r.caml_t)
	  ^ print_result !(r.latex_t)
	  ^ t) )
    baseline;
  close_in baseline_fd

let compute_baseline_fc () = 
  let baseline = ref [] in
  List.iter
    ( fun t ->
      let result_t = run_test t in
      baseline := ((fst t),result_t)::!baseline )
    !tests;
  if file_exists !baseline_file_name then remove !baseline_file_name;
  let baseline_fd = open_out_bin !baseline_file_name in
  Marshal.to_channel baseline_fd !baseline [];
  close_out baseline_fd;
  pp "\n*** baseline built succesfully"

(* the skeleton expression to compute a test *)
let run_test_para = parfun(fun()->farm(seq(fun()->run_test_p),2));; (* FZ fix 2 *)

pardo (fun () ->
  Random.self_init ();
  putenv "PATH" "/home/nis/zappanar/source/coq/bin:/home/nis/zappanar/source/Isabelle/bin:/home/nis/zappanar/source/hol98/bin:/home/nis/zappanar/source/ocaml/bin:/usr/bin:/bin";
  putenv "TWELFSERVER" "/home/nis/zappanar/source/twelf/bin/twelf-server";
  chdir "/home/nis/zappanar/source/update/Ott2/tests/";
  execute_cmd_list [ "cvs update" ];
  chdir "/home/nis/zappanar/source/update/Ott2/examples/tapl/";
  execute_cmd_list [ "cvs update" ];
  chdir "/home/nis/zappanar/source/update/Ott2/src";
  let cmd_list = 
    [ "env";
      "cvs update";
      "make > /dev/null";
      "make tmp_test7a.ott";
      "make tmp_test7.ott" ] in
  execute_cmd_list cmd_list;
  report_fd := open_out "report.txt";
  
  (* if !use_config then parse_config_file (); *)
  parse_todo_list ();

  (* ** open the baseline file *)
  if not (file_exists !baseline_file_name)
  then error ("baseline file does not exists");
  let baseline_fd = open_in_bin !baseline_file_name in
  let baseline = (Marshal.from_channel baseline_fd : (string * result) list) in
  print_endline "content of baseline";
  List.iter (fun (n,_) -> print_endline n) baseline;
  print_endline "end content of baseline";

  let elaborate_result (tn,result_t) =
    summary := (tn,result_t) :: !summary;
    try
      let result_baseline = List.assoc tn baseline in
      report "Coq" !(result_t.coq_t) !(result_baseline.coq_t);
      report "Isa" !(result_t.isa_t) !(result_baseline.isa_t);
      report "HOL" !(result_t.hol_t) !(result_baseline.hol_t);
      report "Twelf" !(result_t.twelf_t) !(result_baseline.twelf_t);
      report "OCaml" !(result_t.caml_t) !(result_baseline.caml_t);
      report "LaTeX" !(result_t.latex_t) !(result_baseline.latex_t);
    with Not_found -> pp ("*** test " ^ tn ^ " not in the baseline") in
  
  (* ** here we do the parallel stuff *)
  P3lstream.iter elaborate_result (run_test_para (P3lstream.of_list !tests));
(*       List.iter *)
(*         ( fun (tn,tl) -> *)
(*           let result_t = run_test (tn,tl) in *)
(*           elaborate_result (tn,result_t) ) *)
(*         !tests; *)

  (* ** print summary *)
  pp_report ("\n*** final report");
  
  pp_report "\n*** results";
  pp_report "\n Coq  Isa  HOL Twelf OCaml LaTeX";
  List.iter
    ( fun (t,r) ->
      pp_report
        ( print_result !(r.coq_t)
	  ^ print_result !(r.isa_t)
	  ^ print_result !(r.hol_t)
	  ^ print_result !(r.twelf_t)
          ^ print_result !(r.caml_t)
          ^ print_result !(r.latex_t)
	  ^ pp_fn t ) )
    !summary;
  
  pp_report
    ( "\n*** progressions: " ^ (string_of_int !progressions)
      ^ " (Ott : " ^ (string_of_int !ott_progressions)^")"
      ^ " (Coq : " ^ (string_of_int !coq_progressions)^")"
      ^ " (Isa : " ^ (string_of_int !isa_progressions)^")"
      ^ " (Hol : " ^ (string_of_int !hol_progressions)^")" 
      ^ " (Twelf : " ^ (string_of_int !twelf_progressions)^")" 
      ^ " (OCaml : " ^ (string_of_int !caml_progressions)^")" 
      ^ " (LaTeX : " ^ (string_of_int !latex_progressions)^")" );
  pp_report
    ("*** regressions:  " ^ (string_of_int !regressions)
     ^ " (Ott : " ^ (string_of_int !ott_regressions)^")"
     ^ " (Coq : " ^ (string_of_int !coq_regressions)^")"
     ^ " (Isa : " ^ (string_of_int !isa_regressions)^")"
     ^ " (Hol : " ^ (string_of_int !hol_regressions)^")"
     ^ " (Twelf : " ^ (string_of_int !twelf_regressions)^")" 
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
  
  pp_report "\n Coq  Isa  HOL Twelf OCaml LaTeX";
  List.iter
    ( fun (t,r) ->
      try
	let b = List.assoc t baseline in
        pp_report
          ( p_out !(r.coq_t) !(b.coq_t)
	    ^ p_out !(r.isa_t) !(b.isa_t)
	    ^ p_out !(r.hol_t) !(b.hol_t)
	    ^ p_out !(r.twelf_t) !(b.twelf_t)
	    ^ p_out !(r.caml_t) !(b.caml_t)
	    ^ p_out !(r.latex_t) !(b.latex_t)
	    ^ pp_fn t )
      with Not_found -> pp_report (" ?    ?    ?    ?    ?    ?  " ^ t) )
    !summary;
  close_in baseline_fd;
  
  if (!regressions = 0) && (!progressions > 0)
  then begin
    if file_exists !baseline_file_name then remove !baseline_file_name;
    let baseline_fd = open_out_bin !baseline_file_name in
    Marshal.to_channel baseline_fd !summary [];
    close_out baseline_fd;
  end;

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
      )
