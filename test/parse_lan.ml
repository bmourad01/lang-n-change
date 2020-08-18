open Core_kernel
open Lang_n_change

let file_pos lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let () =
  In_channel.with_file Sys.argv.(1) ~f:(fun file ->
      let lexbuf = Lexing.from_channel file in
      let lan =
        try
          Language_parser.lan Language_lexer.token lexbuf
        with
        | Language_lexer.Error msg ->
           failwith
             (Printf.sprintf "Lexer error: %s with message %s"
                (file_pos lexbuf) msg)
        | Language_parser.Error ->
           failwith (Printf.sprintf "Parser error: %s" (file_pos lexbuf))
      in Printf.printf "%s\n" (Language.to_string lan))
