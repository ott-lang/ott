let ic = stdin;;

let ast =
  begin
    Location.input_name := "stdin";
    let lexbuf = Lexing.from_channel ic in
      Location.init lexbuf "stdin";
      Parse.implementation lexbuf
  end;;

let _ = 
  Format.fprintf Format.std_formatter "%a@." Printast.implementation ast;;

