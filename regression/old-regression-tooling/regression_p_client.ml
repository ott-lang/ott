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

let hostname = gethostname () 

(* ** options *)
let todo_list_file = ref ("regr_todo_"^hostname^".otl")
let todo_list = ref false
let tests = ref []

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

(* let _ = *)
(*   putenv "CVSROOT" ":pserver:zappa@localhost:/usr/groups/netsem/dynsem/cvs"; *)
(*   putenv "CVS_RSH" "ssh"; *)
(*   putenv "PATH" "/home/nis/zappanar/source/coq/bin:/home/nis/zappanar/source/Isabelle/bin:/home/nis/zappanar/source/hol98/bin:/home/nis/zappanar/source/ocaml/bin:/usr/bin:/bin"; *)
(*   putenv "TWELFSERVER" "/home/nis/zappanar/source/twelf/bin/twelf-server"; *)
(*   print_endline "CIAO" *)

let pp_fn s =
  Filename.basename s

let error s =
  print_endline ("regression: " ^ s);
  exit 1

let pp_report s =
  output_string !report_fd s;
  output_char !report_fd '\n'

let pp s = 
  print_endline s

let execute_cmd_list l =
  List.iter
    (fun c -> 
      pp ("*** executing "^c); 
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
      pp ("todolist"^String.concat " " pl);
      parse_lines fd
    with End_of_file -> ()
  in
  if not (file_exists !todo_list_file)
  then error ("todo_list file "^(!todo_list_file)^" does not exists");
  let todo_fd = open_in !todo_list_file in
  parse_lines todo_fd;
  close_in todo_fd 
  
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
  
  (* ** run Isa *)
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
  
  (* ** run HOL *)
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
  
  (* ** run Twelf *)
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

  (* ** run OCaml *)
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
      remove (name^".cmi");
      remove (name^".cmo")
    end else begin
      result.caml_t := { ott = true; tp = Failure };
      pp (" *  failure")
    end;
    remove (name^".ml")
  end else
    pp (" *  failure");  

  (* ** run LaTeX *)
  let cmd = "/home/nis/zappanar/source/update/Ott2/src/ott -tex "^name^".tex " ^t ^" > /dev/null" in
  pp ("*** Ott-LaTeX: " ^ cmd);
  if (command cmd) = 0
  then begin
    pp (" * success");
    result.latex_t := { ott = true; tp = Skipped };
    remove (name^".tex")
  end else
    pp (" *  failure");  

  (* ** return the result *)
  result

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

let _ =
  Random.self_init (); 
  putenv "PATH" "/home/nis/zappanar/source/coq/bin:/home/nis/zappanar/source/Isabelle/bin:/home/nis/zappanar/source/hol98/bin:/home/nis/zappanar/source/ocaml/bin:/usr/bin:/bin";
  putenv "TWELFSERVER" "/home/nis/zappanar/source/twelf/bin/twelf-server";
  report_fd := open_out ("report_"^hostname^".txt");
  parse_todo_list ();

  let elaborate_result (tn,result_t) =
    summary := (tn,result_t) :: !summary in
  
  List.iter
    ( fun (tn,tl) ->
      let result_t = run_test (tn,tl) in
      elaborate_result (tn,result_t) )
    !tests;
  
  (* ** print summary *)
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
  
  close_out !report_fd

