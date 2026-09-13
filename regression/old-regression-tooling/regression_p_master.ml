(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2007                                                   *)
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

let machines = 
  List.map (fun n -> "clus64a"^(string_of_int n)^".mdkclus64a.lan") 
    [ 1;2;3;4;5;6;7;8;9;10;11;12 ]
let no_machines = List.length machines

(* ** options *)
let compute_baseline = ref false
let baseline_file_name = ref "baseline.bl"
let todo_list_file = ref "regression.otl"
let todo_list = ref false
let tests = ref []
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
let report_fd = ref Pervasives.stdout

(* let _ = *)
(*   if !night then begin *)
(*     putenv "CVSROOT" ":pserver:zappa@localhost:/usr/groups/netsem/dynsem/cvs"; *)
(*     putenv "CVS_RSH" "ssh"; *)
(*     putenv "PATH" "/home/yquem/moscova/zappa/bin:/home/yquem/moscova/zappa/source/godi/bin:/usr/bin:/bin"; *)
(*     putenv "TWELFSERVER" "/home/yquem/moscova/zappa/lib/twelf/bin/twelf-server"; *)
(*   end *)

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

let dump_todo_list m l =
  let fd = open_out ("regr_todo_"^m^".otl") in
  let rec dump_lines f =
    match f with
      (n,tl)::tail ->
	if List.length tl = 1 
	then output_string fd ((List.hd tl)^"\n")
	else output_string fd (n^" : "^(String.concat " " tl)^"\n");
	dump_lines tail
    | [] -> close_out fd
  in dump_lines l

let generate_tasks () =
  let rec gen_buf n buf =
    if n = 0 then buf else gen_buf (n-1) ([]::buf) in
  let rec gen tests buf =
    match tests with
    | [] -> buf
    | h::t -> 
	( match buf with
	| bh::bt -> gen t (bt @ [(h::bh)]) )
  in gen !tests (gen_buf no_machines [])

let options =
  Arg.align
    [ ("-email",
       Arg.String (fun s -> emails := s::!emails),
       "<email> send the night report to");
      ("-report",
       Arg.Unit (fun () -> dump_report := true),
       " dump a report of the outcome of the tests");
    ]

let collect_results () =
  let result_files = 
    List.map (fun x -> "report_"^x^".txt") machines in
  execute_cmd_list [ "cat " ^ (String.concat " " result_files) ^ " > report.txt" ];
  execute_cmd_list [ "rm " ^ (String.concat " " result_files) ]

let _ =
  Random.self_init ();
  Arg.parse options
    (fun s -> tests := (s,[s]) :: !tests)
    ("\n" ^ "regression <options> <test1> .. <testn> \n");
  tests := List.rev !tests;
  putenv "PATH" "/home/nis/zappanar/source/ocaml/bin:/usr/bin:/bin";
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
  parse_todo_list ();
  let tasks = generate_tasks () in
  List.iter2 dump_todo_list machines tasks;
  putenv "GEXEC_SVRS" (String.concat " " machines);

(*  execute_cmd_list [ "echo $GEXEC_SVRS"; "gexec -n 12 hostname" ] *)
  execute_cmd_list [ "gexec -n 0 /home/nis/zappanar/source/update/Ott2/src/regression_p_client" ];

  collect_results ()
  
    

(*   main (); *)
(*   if !night then begin *)
(*     close_out !report_fd; *)
(*     let date = Unix.localtime (Unix.time ()) in *)
(*     let subject =  *)
(*       Printf.sprintf ("[Ott regression report] %d/%d/%d")  *)
(*         date.tm_mday *)
(*         date.tm_mon *)
(*         (1900 + date.tm_year) in *)
(*     let cmd_list =  *)
(*       List.map  *)
(*         (fun e -> "mail -s '" ^ subject ^ "' " ^ e ^ " < report.txt" ) *)
(*         !emails in *)
(*     execute_cmd_list cmd_list *)
(*   end *)
