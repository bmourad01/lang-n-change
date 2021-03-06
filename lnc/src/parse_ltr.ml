open Core_kernel

let file_pos lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse filename =
  In_channel.with_file filename ~f:(fun file ->
      let lexbuf = Lexing.from_channel file in
      try Ltr_parser.ltr Ltr_lexer.token lexbuf with
      | Language_lexer.Error msg ->
          failwith
            (Printf.sprintf "L-Tr: %s lexing error: %s (%s)" filename
               (file_pos lexbuf) msg)
      | Language_parser.Error ->
          failwith
            (Printf.sprintf "L-Tr: %s parse error: %s" filename
               (file_pos lexbuf))
      | _ ->
          failwith
            (Printf.sprintf "L-Tr: %s unknown error: %s" filename
               (file_pos lexbuf)))
