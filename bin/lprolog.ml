open Core
open Lang_n_change

let file_pos lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let () =
  let filename = (Sys.get_argv ()).(1) in
  let directory = "lprolog/" in
  Unix.mkdir_p directory;
  In_channel.with_file filename ~f:(fun file ->
      let lexbuf = Lexing.from_channel file in
      let lprolog =
        try
          Language_parser.lan Language_lexer.token lexbuf
          |> Lprolog.of_language
        with
        | Language_lexer.Error msg ->
           failwith
             (Printf.sprintf "Lexer error: %s with message %s"
                (file_pos lexbuf) msg)
        | Language_parser.Error ->
           failwith (Printf.sprintf "Parser error: %s" (file_pos lexbuf))
      in
      let basename =
        Filename.basename filename
        |> String.chop_suffix_if_exists ~suffix:".lan"
      in
      let signame = directory ^ basename ^ ".sig" in
      let modname = directory ^ basename ^ ".mod" in
      Out_channel.with_file signame ~f:(fun file ->
          Out_channel.output_string file
            (Printf.sprintf "sig %s.\n\n%s\n"
               basename
               (Lprolog.Sigs.to_string lprolog.sigs)));
      Out_channel.with_file modname ~f:(fun file ->
          Out_channel.output_string file
            (Printf.sprintf "module %s.\n\n%s\n"
               basename
               (Map.data lprolog.rules
                |> List.map ~f:Lprolog.Rule.to_string
                |> String.concat ~sep:"\n\n"))))
