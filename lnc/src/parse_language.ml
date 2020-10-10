open Core_kernel

let file_pos lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%d:%d"
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse filename =
  In_channel.with_file filename ~f:(fun file ->
      let lexbuf = Lexing.from_channel file in
      try
        Language_parser.lan Language_lexer.token lexbuf
      with
      | Language_lexer.Error msg ->
         failwith
           (Printf.sprintf "Language: %s lexing error: %s (%s)"
              filename (file_pos lexbuf) msg)
      | Language_parser.Error ->
         failwith
           (Printf.sprintf "Language %s parse error: %s"
              filename (file_pos lexbuf))
      | _ ->
         failwith
           (Printf.sprintf "Language: %s unknown error: %s"
              filename (file_pos lexbuf)))

