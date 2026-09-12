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


(* ** options *)
let temp_dir = ref ""
let use_config = ref false
let config_file_name = ref "config.otr"
let todo_list_file = ref "regression.otl"
let todo_list = ref false
let tests = ref []
let report_file = ref "report.txt"
let night = ref false
let jenkins = ref false
let emails = ref []
let keep_temporary_files = ref false
let colour_output = ref true

(* Claude: with -temp_dir the target tools run inside that directory, so every
   path a command mentions has to be absolute rather than relative to the
   regression directory.  These are resolved once, before anything chdirs. *)
let regression_dir = Sys.getcwd ()
let ott_dir = Filename.dirname regression_dir
let ott_bin = Filename.concat ott_dir "bin/ott"
let coq_lib = Filename.concat ott_dir "coq"
let hol_lib = Filename.concat ott_dir "hol"

let in_temp_dir cmd =
  if !temp_dir = "" then cmd
  else "cd " ^ Filename.quote !temp_dir ^ " && " ^ cmd

let in_temp_dir_path f =
  Filename.concat !temp_dir f

(* Claude: Ott writes the -o path into the generated file, as the Isabelle
   theory name and HOL new_theory name, so the output argument must stay a
   bare filename.  That means generating inside -temp_dir too, and giving the
   inputs as absolute paths since they are relative to the regression
   directory. *)
let absolute p =
  if Filename.is_relative p then Filename.concat regression_dir p else p

(* ** state *)
let regression_count = ref 0
let report_fd = ref Stdlib.stdout
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

(** ***************************************************************** *)
(** outcomes and report cells                                         *)
(** ***************************************************************** *)

type step = Ok | Failed | Skipped | Unreached

(* Claude: a report cell is exactly two non-blank characters: whether Ott
   generated the file for this tool, and whether the tool then accepted it.
   The old table rendered a skipped tool as blanks and an unreached one as
   fewer blanks, so a written report could not be read back; this encoding
   is unambiguous and still reads at a glance. *)
type cell = { gen : step; chk : step }

let char_of_step s =
  match s with
  | Ok -> '+'
  | Failed -> '-'
  | Skipped -> 's'
  | Unreached -> '.'

let step_of_char c =
  match c with
  | '+' -> Some Ok
  | '-' -> Some Failed
  | 's' -> Some Skipped
  | '.' -> Some Unreached
  | _ -> None

let string_of_cell c =
  let b = Bytes.create 2 in
  Bytes.set b 0 (char_of_step c.gen);
  Bytes.set b 1 (char_of_step c.chk);
  Bytes.to_string b

let cell_of_string s =
  if String.length s <> 2 then None
  else
    match step_of_char s.[0], step_of_char s.[1] with
    | Some g, Some k -> Some { gen = g; chk = k }
    | _, _ -> None

let skipped_cell = { gen = Skipped; chk = Skipped }

(** ***************************************************************** *)
(** the tools we run, and how                                         *)
(** ***************************************************************** *)

(* Claude: one entry per report column.  Everything that used to be spelled
   out eight times over - the result record, the per-tool counters, the
   config-file tuple, the table printers - is now driven from this list, so
   adding a backend is a single entry here plus its -no_ flag. *)
type tool =
  { t_name : string;                        (* report column name *)
    t_flag : string;                        (* command-line flag that selects it *)
    t_enabled : bool ref;                   (* set by that flag, or by -all *)
    t_out : string;                         (* suffix Ott writes for it *)
    t_gen : string -> string -> string;     (* inputs -> base -> ott command *)
    t_check : string -> string;             (* base -> tool command *)
    t_artefacts : string -> string list }   (* base -> files to clean up *)

let isa_test = ref false
let caml_test = ref false
let coq_test = ref false
let hol_test = ref false
let lem_test = ref false
let lean_test = ref false
let latex_test = ref false

let tools =
  [ { t_name = "Coq";
      t_out = ".v";
      t_flag = "-coq";
      t_enabled = coq_test;
      t_gen = (fun t base ->
        ott_bin ^ " -show_sort false -show_defns false " ^ t ^ " -o " ^ base ^ ".v");
      t_check = (fun base ->
        "rocq compile -Q " ^ coq_lib ^ " Ott " ^ base ^ ".v > " ^ base ^ ".coq.out 2>&1");
      t_artefacts = (fun base ->
        [ base ^ ".v"; base ^ ".vo"; base ^ ".glob"; base ^ ".coq.out";
          Filename.concat (Filename.dirname base) ("." ^ Filename.basename base ^ ".aux") ]) };

    { t_name = "CoqNL";
      t_out = ".v";
      t_flag = "-coq";
      t_enabled = coq_test;
      t_gen = (fun t base ->
        ott_bin ^ " -coq_expand_list_types false " ^ t ^ " -o " ^ base ^ ".v");
      t_check = (fun base ->
        "rocq compile -Q " ^ coq_lib ^ " Ott " ^ base ^ ".v > " ^ base ^ ".coqnl.out 2>&1");
      t_artefacts = (fun base ->
        [ base ^ ".v"; base ^ ".vo"; base ^ ".glob"; base ^ ".coqnl.out";
          Filename.concat (Filename.dirname base) ("." ^ Filename.basename base ^ ".aux") ]) };

    { t_name = "Isa";
      t_out = ".thy";
      t_flag = "-isa";
      t_enabled = isa_test;
      t_gen = (fun t base -> ott_bin ^ " " ^ t ^ " -o " ^ base ^ ".thy");
      t_check = (fun base ->
        "isabelle process_theories -U -O -f \"" ^ base ^ ".thy\" > "
        ^ base ^ ".isa.out 2>&1");
      t_artefacts = (fun base -> [ base ^ ".thy"; base ^ ".isa.out" ]) };

    { t_name = "HOL";
      t_out = "Script.sml";
      t_flag = "-hol";
      t_enabled = hol_test;
      t_gen = (fun t base -> ott_bin ^ " " ^ t ^ " -o " ^ base ^ "Script.sml");
      t_check = (fun base ->
        "Holmake -I " ^ hol_lib ^ " " ^ base ^ "Theory.uo > " ^ base ^ ".hol.out 2>&1");
      t_artefacts = (fun base ->
        [ base ^ "Script.sml"; base ^ "Theory.sml"; base ^ "Theory.sig";
          base ^ "Theory.ui"; base ^ "Theory.uo"; base ^ ".hol.out" ]) };

    { t_name = "Lem";
      t_out = ".lem";
      t_flag = "-lem";
      t_enabled = lem_test;
      t_gen = (fun t base -> ott_bin ^ " " ^ t ^ " -o " ^ base ^ ".lem");
      t_check = (fun base ->
        "lem " ^ base ^ ".lem > " ^ base ^ ".lem.out 2>&1");
      t_artefacts = (fun base -> [ base ^ ".lem"; base ^ ".lem.out" ]) };

    { t_name = "Lean";
      t_out = ".lean";
      t_flag = "-lean";
      t_enabled = lean_test;
      t_gen = (fun t base -> ott_bin ^ " " ^ t ^ " -o " ^ base ^ ".lean");
      t_check = (fun base ->
        "lean " ^ base ^ ".lean > " ^ base ^ ".lean.out 2>&1");
      t_artefacts = (fun base -> [ base ^ ".lean"; base ^ ".lean.out" ]) };

    { t_name = "OCaml";
      t_out = ".ml";
      t_flag = "-ocaml";
      t_enabled = caml_test;
      t_gen = (fun t base -> ott_bin ^ " " ^ t ^ " -o " ^ base ^ ".ml");
      t_check = (fun base ->
        "ocamlc " ^ base ^ ".ml > " ^ base ^ ".ocaml.out 2>&1");
      (* Claude: ocamlc links as well as compiles, so it drops an a.out in the
         regression directory too - that is why one kept turning up here. *)
      t_artefacts = (fun base ->
        [ base ^ ".ml"; base ^ ".cmi"; base ^ ".cmo"; base ^ ".ocaml.out";
          "a.out" ]) };

    { t_name = "LaTeX";
      t_out = ".tex";
      t_flag = "-latex";
      t_enabled = latex_test;
      t_gen = (fun t base -> ott_bin ^ " " ^ t ^ " -o " ^ base ^ ".tex");
      t_check = (fun base ->
        "pdflatex -interaction=batchmode " ^ base ^ ".tex > "
        ^ base ^ ".latex.out 2>&1");
      t_artefacts = (fun base ->
        [ base ^ ".tex"; base ^ ".pdf"; base ^ ".aux"; base ^ ".log";
          base ^ ".latex.out" ]) } ]

let tool_names = List.map (function tl -> tl.t_name) tools

(* Claude: classify a file in a -temp_dir by suffix rather than by test name,
   so the file comparison does not need to know which tests produced it.
   Anything ending in one of these is something Ott wrote; everything else in
   the directory is a by-product of a target tool. *)
let generated_suffixes =
  List.sort_uniq compare (List.map (function tl -> tl.t_out) tools)

let is_ott_generated f =
  List.exists (function sfx -> Filename.check_suffix f sfx) generated_suffixes

(** ***************************************************************** *)
(** reports                                                           *)
(** ***************************************************************** *)

let report_format = "ott-regression-report 1"

type report =
  { r_meta : (string * string) list;             (* header comment lines *)
    r_cols : string list;                        (* tool names, in order *)
    r_rows : (string * (string * cell) list) list }

(* Claude: the row labels of the totals block.  They double as the set of
   non-data first tokens the reader is allowed to skip, so keep them single
   tokens. *)
let total_labels = [ "generated"; "ott-failed"; "passed"; "failed"; "skipped" ]

let count_cells p cells = List.length (List.filter p cells)

let tally rep =
  List.map
    ( function c ->
      let cells =
        List.filter_map
          (function (_,rs) -> try Some (List.assoc c rs) with Not_found -> None)
          rep.r_rows in
      ( c,
        [ "generated",  count_cells (function x -> x.gen = Ok) cells;
          "ott-failed", count_cells (function x -> x.gen = Failed) cells;
          "passed",     count_cells (function x -> x.chk = Ok) cells;
          "failed",     count_cells (function x -> x.chk = Failed) cells;
          "skipped",    count_cells (function x -> x.gen = Skipped) cells ] ) )
    rep.r_cols

let pad_right w s = s ^ String.make (max 0 (w - String.length s)) ' '
let pad_left w s = String.make (max 0 (w - String.length s)) ' ' ^ s

let key_width rep =
  List.fold_left (function n -> function s -> max n (String.length s))
    (String.length "ott-failed")
    ("test" :: "totals" :: List.map fst rep.r_rows)

let col_width c = max 5 (String.length c + 1)
let all_width = 6

(* Claude: the totals block at the foot of a report, one row per outcome and
   one column per tool, with an "all" column summing across tools so there is
   a single number for the whole run. *)
let totals_lines rep kw =
  let t = tally rep in
  let head =
    pad_right kw "totals"
    ^ String.concat "" (List.map (function c -> pad_left (col_width c) c) rep.r_cols)
    ^ pad_left all_width "all" in
  let row label =
    let ns = List.map (function (_,counts) -> List.assoc label counts) t in
    pad_right kw label
    ^ String.concat ""
        (List.map2 (function c -> function n -> pad_left (col_width c) (string_of_int n))
           rep.r_cols ns)
    ^ pad_left all_width (string_of_int (List.fold_left (+) 0 ns)) in
  head :: List.map row total_labels

let report_lines rep =
  let kw = key_width rep in
  let head =
    pad_right kw "test"
    ^ String.concat "" (List.map (function c -> pad_left (col_width c) c) rep.r_cols) in
  let row (k,rs) =
    pad_right kw k
    ^ String.concat ""
        (List.map
           (function c ->
             let s =
               try string_of_cell (List.assoc c rs) with Not_found -> "  " in
             pad_left (col_width c) s)
           rep.r_cols) in
  [ "# " ^ report_format ]
  @ List.map (function (k,v) -> "# " ^ k ^ " " ^ v) rep.r_meta
  @ [ "# tools " ^ String.concat " " rep.r_cols; "" ]
  @ (head :: List.map row rep.r_rows)
  @ [ "" ]
  @ totals_lines rep kw

let write_report fn rep =
  let fd = open_out fn in
  List.iter (function l -> output_string fd l; output_char fd '\n') (report_lines rep);
  close_out fd

let read_report fn =
  if not (file_exists fn) then error ("report file " ^ fn ^ " does not exist");
  let fd = open_in fn in
  let meta = ref [] and cols = ref [] and rows = ref [] in
  ( try
      while true do
        let l = input_line fd in
        match Str.split (Str.regexp "[ \t]+") l with
        | [] -> ()
        | "#" :: "tools" :: cs -> cols := cs
        | "#" :: k :: v -> meta := (k, String.concat " " v) :: !meta
        | "#" :: [] -> ()
        | key :: rest ->
            let n = List.length !cols in
            if n = 0
            then error (fn ^ " has no \"# tools\" header line");
            let cs = List.map cell_of_string rest in
            if List.length rest = n && List.for_all (function c -> c <> None) cs
            then
              let get c = match c with Some c -> c | None -> assert false in
              rows := (key, List.combine !cols (List.map get cs)) :: !rows
            else if key = "test" || key = "totals" || List.mem key total_labels
            then ()
            else error ("cannot parse line in " ^ fn ^ ": " ^ l)
      done
    with End_of_file -> () );
  close_in fd;
  { r_meta = List.rev !meta; r_cols = !cols; r_rows = List.rev !rows }

(** ***************************************************************** *)
(** todo lists, config files, command line                            *)
(** ***************************************************************** *)

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
  then error ("todo list " ^ !todo_list_file ^ " does not exist");
  let todo_fd = open_in !todo_list_file in
  parse_lines todo_fd;
  close_in todo_fd

(* Claude: the config file names its columns in a "# tools" header rather than
   relying on position, so adding or reordering a backend no longer silently
   changes what every existing line means. *)
let parse_config_file () =
  let convert c =
    match c with
    | "+" -> true
    | "." -> false
    | _ -> error "malformed entry in config file" in
  let cols = ref [] in
  if not (file_exists !config_file_name)
  then error ("config file " ^ !config_file_name ^ " does not exist");
  let fd = open_in !config_file_name in
  ( try
      while true do
        let l = input_line fd in
        match Str.split (Str.regexp "[ \t]+") l with
        | [] -> ()
        | "#" :: "tools" :: cs -> cols := cs
        | "#" :: _ -> ()
        | toks ->
            let n = List.length !cols in
            if n = 0
            then error (!config_file_name ^ " has no \"# tools\" header line");
            if List.length toks <> n + 1
            then error ("malformed line in config file: " ^ l);
            let flags = List.filteri (function i -> function _ -> i < n) toks in
            let name = List.nth toks n in
            config_state :=
              (name, List.combine !cols (List.map convert flags)) :: !config_state;
            Printf.printf "config: %s %s\n" name (String.concat " " flags)
      done
    with End_of_file -> () );
  close_in fd

let check_config t tp =
  if not !use_config then true
  else
    try
      let entry = List.assoc t !config_state in
      ( try List.assoc tp entry with Not_found -> true )
    with Not_found ->
      print_endline ("*** test "^t^" not found in config file"); true

let run_ott_given = ref false
let run_targets_given = ref false
let compare_a = ref ""
let compare_b = ref ""
let compare_gen_a = ref ""
let compare_gen_b = ref ""
let compare_all_a = ref ""
let compare_all_b = ref ""

(* Claude: exactly one mode flag must be given, so record which were seen
   rather than inferring the mode from whether a filename happens to be set. *)
type mode =
  | RunOtt | RunOttAndTargets | Compare | CompareGenerated | CompareAll

let mode_flags =
  [ "-run_ott"; "-run_ott_and_targets"; "-compare_reports";
    "-compare_ott_generated_files"; "-compare_all_files" ]

let english_list ss =
  match List.rev ss with
  | last :: (_ :: _ as rest) -> String.concat ", " (List.rev rest) ^ " and " ^ last
  | _ -> String.concat "" ss

let selected_modes () =
  ( if !run_ott_given then [ ("-run_ott", RunOtt) ] else [] )
  @ ( if !run_targets_given
      then [ ("-run_ott_and_targets", RunOttAndTargets) ] else [] )
  @ ( if !compare_a <> "" then [ ("-compare_reports", Compare) ] else [] )
  @ ( if !compare_gen_a <> ""
      then [ ("-compare_ott_generated_files", CompareGenerated) ] else [] )
  @ ( if !compare_all_a <> "" then [ ("-compare_all_files", CompareAll) ] else [] )

let selected_mode () =
  match selected_modes () with
  | [ (_,m) ] -> m
  | [] -> error ("specify exactly one of " ^ english_list mode_flags)
  | ms ->
      error (english_list mode_flags ^ " are mutually exclusive, but "
             ^ english_list (List.map fst ms) ^ " were given")

let enable_all () = List.iter (function tl -> tl.t_enabled := true) tools

let any_tool_enabled () =
  List.exists (function tl -> !(tl.t_enabled)) tools

(* Claude: no target runs unless it is asked for, by name or by -all.  -coq
   selects both the Coq and CoqNL columns, since those two share one flag
   name; so emit each distinct flag once and let it set every enable ref that
   names it. *)
let tool_options =
  let flags =
    List.sort_uniq compare (List.map (function tl -> tl.t_flag) tools) in
  ( "-all",
    Arg.Unit enable_all,
    " build and optionally run every target" )
  :: List.map
       ( function f ->
         let affected =
           List.filter (function tl -> tl.t_flag = f) tools in
         ( f,
           Arg.Unit (function () ->
             List.iter (function tl -> tl.t_enabled := true) affected),
           " build and optionally run the "
           ^ String.concat " and " (List.map (function tl -> tl.t_name) affected)
           ^ " target" ) )
       flags

(* Claude: -no_coq turns off both the Coq and CoqNL columns, as it always
   has, because the two share one enable flag; so filter the generated
   options by flag identity rather than emitting one per column. *)
       
(* Claude: Arg takes the next word as an option's argument even when that word
   is plainly another flag, so "-run_ott_and_targets -all ..." quietly used
   "-all" as the report filename and then complained that no target had been
   selected.  Reject arguments that look like options. *)
let arg_value flag s =
  if String.length s > 0 && s.[0] = '-'
  then error (flag ^ " expects an argument, but was given the option " ^ s
              ^ " - did you leave its argument out?")
  else s

let set_arg flag r = Arg.String (function s -> r := arg_value flag s)

let options =
  Arg.align
    ( [ ("-run_ott",
         Arg.String (fun s ->
           run_ott_given := true; report_file := arg_value "-run_ott" s),
         "<"^ !report_file^">  run Ott only, and write the report here");
        ("-run_ott_and_targets",
         Arg.String (fun s ->
           run_targets_given := true;
           report_file := arg_value "-run_ott_and_targets" s),
         "<"^ !report_file^">  run Ott and the target tools, and report here");
        ("-compare_reports",
         Arg.Tuple [ set_arg "-compare_reports" compare_a;
                     set_arg "-compare_reports" compare_b ],
         " <a.txt> <b.txt>  compare two reports instead of running tests");
        ("-compare_ott_generated_files",
         Arg.Tuple [ set_arg "-compare_ott_generated_files" compare_gen_a;
                     set_arg "-compare_ott_generated_files" compare_gen_b ],
         " <dirA> <dirB>  compare the files Ott generated in two -temp_dir runs");
        ("-compare_all_files",
         Arg.Tuple [ set_arg "-compare_all_files" compare_all_a;
                     set_arg "-compare_all_files" compare_all_b ],
         " <dirA> <dirB>  as above, plus the files the target tools generated");
        ("-todo_list",
         Arg.String (fun s ->
           todo_list := true; todo_list_file := arg_value "-todo_list" s),
         "<"^ !todo_list_file^">  take the tests from this todo list instead of the command line");
        ("-use_config",
         Arg.String (fun s ->
           use_config := true; config_file_name := arg_value "-use_config" s),
         "<"^ !config_file_name^">  take per-test target choices from this config file");
        ("-temp_dir",
         set_arg "-temp_dir" temp_dir,
         "<dir>  put generated files here and run the tools inside it");
        ("-keep_temp",
         Arg.Unit (fun () -> keep_temporary_files := true),
         " do not clean up temporary files");
        ("-no_colour",
         Arg.Unit (fun () -> colour_output := false),
         " do not use colour in output")      ]
      @ tool_options
      @ [ ("-night",
           Arg.Unit (fun () -> night := true),
           " (likely bitrotted) perform the nightly regression test");
          ("-jenkins",
           Arg.Unit (fun () -> jenkins := true),
           " (likely bitrotted) output result in XML format for Jenkins");
          ("-email",
           Arg.String (fun s -> emails := (arg_value "-email" s) :: !emails),
           "<email> (likely bitrotted) send the night report to");
] )



(** ***************************************************************** *)
(** running the tests                                                 *)
(** ***************************************************************** *)

(* Claude: in -run_ott mode the target tool is never invoked, so its half of
   the cell is a skip rather than an unreached mark: nothing failed, we simply
   did not ask.  Comparing an Ott-only report against a full one then shows
   those cells as changes, not as progressions. *)
let run_tool with_targets i_of_n tn name stem t tl =
  if (not !(tl.t_enabled)) || (not (check_config tn tl.t_name))
  then skipped_cell
  else begin
    let gen_cmd = in_temp_dir (tl.t_gen t stem) in
    let gen_tgt = "Ott-" ^ tl.t_name in
    pp "";
    pp_tgt i_of_n gen_tgt gen_cmd;
    let c =
      if (command gen_cmd) <> 0
      then begin
        pp_failure gen_tgt name;
        { gen = Failed; chk = if with_targets then Unreached else Skipped }
      end else if not with_targets
      then begin
        pp_success gen_tgt name;
        { gen = Ok; chk = Skipped }
      end else begin
        pp_success gen_tgt name;
        let chk_cmd = in_temp_dir (tl.t_check stem) in
        pp_tgt i_of_n tl.t_name chk_cmd;
        if (command chk_cmd) = 0
        then begin pp_success tl.t_name name; { gen = Ok; chk = Ok } end
        else begin pp_failure tl.t_name name; { gen = Ok; chk = Failed } end
      end in
    List.iter maybe_remove (List.map in_temp_dir_path (tl.t_artefacts stem));
    c
  end

let run_test with_targets i n (tn,tl) =
  let i_of_n = Printf.sprintf "(%d/%d)" i n in
  let tl = if !temp_dir = "" then tl else List.map absolute tl in
  let t =
    if List.length tl = 1
    then "-i "^(List.hd tl)
    else "-merge true -i "^String.concat " -i " tl in
  let name = Filename.remove_extension (Filename.basename tn) in
  let base_name =
    String.map (function c -> match c with '.' -> '_' | '-' -> '_' | _ -> c) name in
  let stem = "testRegr_" ^ base_name in
  pp ("*** " ^ i_of_n ^ " " ^ tn ^ "\n");
  ( tn,
    List.map
      (function tool ->
        (tool.t_name, run_tool with_targets i_of_n tn name stem t tool))
      tools )

let now () =
  let d = Unix.localtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d"
    (1900 + d.tm_year) (d.tm_mon + 1) d.tm_mday d.tm_hour d.tm_min d.tm_sec

let ott_version () =
  let fn = Filename.concat (Filename.get_temp_dir_name ()) "ott_version_regr" in
  let v =
    if (command (ott_bin ^ " -help > " ^ fn ^ " 2>&1")) >= 0 && file_exists fn
    then ( let fd = open_in fn in
           let l = try input_line fd with End_of_file -> "" in
           close_in fd; l )
    else "" in
  maybe_remove fn;
  v

let run_fc with_targets =
  let n_tests = List.length !tests in
  let rows =
    List.mapi (function i -> function t -> run_test with_targets i n_tests t) !tests in
  let rep =
    { r_meta = [ ("date", now ()); ("ott", ott_version ()) ];
      r_cols = tool_names;
      r_rows = rows } in
  write_report !report_file rep;
  pp_report "";
  List.iter pp_report (report_lines rep);
  pp ("\n*** report written to " ^ !report_file)

(** ***************************************************************** *)
(** comparing two reports                                             *)
(** ***************************************************************** *)

type change = Progression | Regression | Change

(* Claude: a target that was simply not selected on one of the two runs has
   not progressed or regressed, whatever its other side says, so any cell with
   a skip on either side is only ever a change. *)
let classify a b =
  if a.gen = Skipped || b.gen = Skipped
  then Change
  else if (a.gen = Ok && b.gen = Failed) || (a.chk = Ok && b.chk = Failed)
  then Regression
  else if (a.gen <> Ok && b.gen = Ok) || (a.chk = Failed && b.chk = Ok)
  then Progression
  else Change

let string_of_change c =
  match c with
  | Progression -> "progression"
  | Regression -> "regression"
  | Change -> "change"

let change_labels = [ "progressions"; "regressions"; "changes" ]

let label_of_change c =
  match c with
  | Progression -> "progressions"
  | Regression -> "regressions"
  | Change -> "changes"

(* Claude: compare only the columns both reports carry, and say plainly which
   columns are in one and not the other, rather than silently dropping them.
   That is what lets a report written before a backend existed still be
   compared against one written after. *)
let compare_fc fn_a fn_b =
  let a = read_report fn_a and b = read_report fn_b in
  let cols = List.filter (function c -> List.mem c a.r_cols) b.r_cols in
  let only_a = List.filter (function c -> not (List.mem c b.r_cols)) a.r_cols in
  let only_b = List.filter (function c -> not (List.mem c a.r_cols)) b.r_cols in
  let meta r k = try List.assoc k r.r_meta with Not_found -> "?" in
  pp_report "\n*** comparison";
  pp_report ("*** A " ^ fn_a ^ "   " ^ meta a "date");
  pp_report ("*** B " ^ fn_b ^ "   " ^ meta b "date");
  if only_a <> []
  then pp_report ("*** columns only in A: " ^ String.concat " " only_a);
  if only_b <> []
  then pp_report ("*** columns only in B: " ^ String.concat " " only_b);
  pp_report "";

  let kw =
    List.fold_left (function n -> function s -> max n (String.length s))
      (String.length "progressions")
      (List.map fst a.r_rows @ List.map fst b.r_rows) in
  let cw = List.fold_left (function n -> function c -> max n (String.length c)) 4 cols in

  (* tallies, keyed by column then by change label *)
  let counts =
    List.map (function c -> (c, List.map (function l -> (l, ref 0)) change_labels)) cols in
  let bump c l = let r = List.assoc l (List.assoc c counts) in r := !r + 1 in

  let diff_test key rs_a rs_b =
    let ds =
      List.filter_map
        ( function c ->
          match (try Some (List.assoc c rs_a) with Not_found -> None),
                (try Some (List.assoc c rs_b) with Not_found -> None) with
          | Some ca, Some cb when ca <> cb -> Some (c, ca, cb)
          | _, _ -> None )
        cols in
    List.iteri
      ( function i -> function (c,ca,cb) ->
        let k = classify ca cb in
        bump c (label_of_change k);
        pp_report
          ( pad_right kw (if i = 0 then key else "")
            ^ "  " ^ pad_right cw c
            ^ "  " ^ string_of_cell ca ^ " -> " ^ string_of_cell cb
            ^ "  " ^ string_of_change k ) )
      ds;
    ds <> [] in

  let changed = ref 0 in
  List.iter
    ( function (key, rs_b) ->
      match (try Some (List.assoc key a.r_rows) with Not_found -> None) with
      | Some rs_a -> if diff_test key rs_a rs_b then changed := !changed + 1
      | None ->
          changed := !changed + 1;
          pp_report (pad_right kw key ^ "  only in B") )
    b.r_rows;
  List.iter
    ( function (key, _) ->
      if not (List.mem_assoc key b.r_rows)
      then begin
        changed := !changed + 1;
        pp_report (pad_right kw key ^ "  only in A")
      end )
    a.r_rows;
  if !changed = 0 then pp_report "no differences";

  pp_report "";
  let colw c = max 5 (String.length c + 1) in
  pp_report
    ( pad_right kw "totals"
      ^ String.concat "" (List.map (function c -> pad_left (colw c) c) cols)
      ^ pad_left all_width "all" );
  List.iter
    ( function l ->
      let ns = List.map (function c -> !(List.assoc l (List.assoc c counts))) cols in
      pp_report
        ( pad_right kw l
          ^ String.concat ""
              (List.map2
                 (function c -> function n -> pad_left (colw c) (string_of_int n))
                 cols ns)
          ^ pad_left all_width (string_of_int (List.fold_left (+) 0 ns)) ) )
    change_labels;
  regression_count :=
    List.fold_left (function n -> function c ->
      n + !(List.assoc "regressions" (List.assoc c counts))) 0 cols

(** ***************************************************************** *)
(** comparing the generated files of two runs                         *)
(** ***************************************************************** *)

(* Claude: this compares the -temp_dir directories of two runs, so both runs
   have to have been made with -temp_dir and -keep_temp; without the latter
   the harness deletes everything it generated and there is nothing left to
   compare. *)
let dir_files d =
  if not (file_exists d) then error (d ^ " does not exist");
  if not (Sys.is_directory d) then error (d ^ " is not a directory");
  List.sort compare
    ( List.filter
        (function f -> not (Sys.is_directory (Filename.concat d f)))
        (Array.to_list (Sys.readdir d)) )

let file_contents fn =
  let ic = open_in_bin fn in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let compare_files_fc what keep da db =
  let filter = List.filter keep in
  let fa = filter (dir_files da) and fb = filter (dir_files db) in
  (* Claude: two empty directories are not two matching runs.  Say so rather
     than reporting "no differences" over nothing, which is how a forgotten
     -temp_dir or -keep_temp used to look like success. *)
  if fa = [] && fb = []
  then error ("neither " ^ da ^ " nor " ^ db ^ " holds any of the " ^ what
              ^ " - were both runs made with -temp_dir and -keep_temp?");
  let all = List.sort_uniq compare (fa @ fb) in
  let labels = [ "same"; "differ"; "only in A"; "only in B" ] in
  let w =
    List.fold_left (function n -> function s -> max n (String.length s))
      (String.length "only in A") ("totals" :: all) in
  pp_report ("\n*** file comparison (" ^ what ^ ")");
  pp_report ("*** A " ^ da);
  pp_report ("*** B " ^ db);
  pp_report "";
  let counts = List.map (function l -> (l, ref 0)) labels in
  let bump l = let r = List.assoc l counts in r := !r + 1 in
  List.iter
    ( function f ->
      match List.mem f fa, List.mem f fb with
      | true, true ->
          if file_contents (Filename.concat da f) = file_contents (Filename.concat db f)
          then bump "same"
          else begin bump "differ"; pp_report (pad_right w f ^ "  differs") end
      | true, false ->
          bump "only in A"; pp_report (pad_right w f ^ "  only in A")
      | false, true ->
          bump "only in B"; pp_report (pad_right w f ^ "  only in B")
      | false, false -> () )
    all;
  if !(List.assoc "same" counts) = List.length all
  then pp_report "no differences";
  pp_report "";
  pp_report (pad_right w "totals" ^ pad_left 6 "files");
  List.iter
    ( function l ->
      pp_report (pad_right w l ^ pad_left 6 (string_of_int !(List.assoc l counts))) )
    labels

let main () =
  match selected_mode () with
  | RunOtt -> run_fc false
  | RunOttAndTargets -> run_fc true
  | Compare -> compare_fc !compare_a !compare_b
  | CompareGenerated ->
      compare_files_fc "files generated by Ott" is_ott_generated
        !compare_gen_a !compare_gen_b
  | CompareAll ->
      compare_files_fc "all files" (function _ -> true)
        !compare_all_a !compare_all_b

let _ =
  Arg.parse options
    (fun s -> tests := (s,[s]) :: !tests)
    ("\n" ^ "regression <options> <test1> .. <testn> \n");
  tests := List.rev !tests;
  let running =
    match selected_mode () with
    | RunOtt | RunOttAndTargets -> true
    | Compare | CompareGenerated | CompareAll -> false in
  if running then
    ( match !todo_list, !tests with
    | true, _::_ ->
        error "-todo_list and tests named on the command line are mutually exclusive"
    | false, [] -> error "specify at least one test, or a -todo_list"
    | _, _ -> () );
  if running && not (any_tool_enabled ())
  then error "specify at least one target (for example -coq -lean), or -all";
  if running && !temp_dir <> ""
  then execute_cmd_list ["mkdir -p " ^ Filename.quote !temp_dir] else ();
  if !night
  then begin
    putenv "PATH" "/home/yquem/moscova/zappa/bin:/home/yquem/moscova/zappa/source/godi/bin:/usr/bin:/bin";
    putenv "TWELFSERVER" "/home/yquem/moscova/zappa/lib/twelf/bin/twelf-server";
    chdir "/home/yquem/moscova/zappa/repo/update/Ott2/src";
    execute_cmd_list [ "./regression_night_script.sh" ];
    chdir "/home/yquem/moscova/zappa/repo/update/Ott2/src";
    report_fd := open_out "report.txt";
  end;
  if !use_config then parse_config_file ();
  if !todo_list && running then parse_todo_list ();
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

  (* Claude: the Jenkins verdict comes from the comparison, so it is only
     meaningful in -compare_reports mode; a bare run has nothing to regress against. *)
  if !jenkins then begin
    let fd = open_out "tests.xml" in
    output_string fd "<testsuite tests=\"1\">\n";
    if !regression_count == 0
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
