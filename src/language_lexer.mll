{
  open Lexing
  open Language_parser

  exception Syntax_error of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      {pos with pos_lnum = pos.pos_lnum + 1;
                pos_bol = pos.pos_cnum}
}

let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['a'-'z'] (alpha | '_' | '\'' | digit)*
let integer = digit+

rule token = parse                            
  | '\n' {next_line lexbuf; token lexbuf} 
  | space {token lexbuf}
  | "::=" {GRAMMAR_ASSIGN}
  | "," {COMMA}
  | "|" {MID}
  | "[" {LSQUARE}
  | "]" {RSQUARE}
  | "(" {LPAREN}
  | ")" {RPAREN}
  | "{" {LBRACE}
  | "}" {RBRACE}
  | "-" {DASH}
  | "\"" {QUOTE}
  | "/" {FSLASH}
  | "=>" {MAPSTO}
  | "=" {EQ}
  | "in" {IN}
  | "forall" {FORALL}
  | "find" {FIND}
  | "where" {WHERE}
  | "with" {WITH}
  | integer as n {INT (int_of_string n)}
  | ident as id {ID id}
  | eof {EOF}
  | _ {raise (Syntax_error
        (Printf.sprintf "At offset %d: unexpected character %s.\n"
          (Lexing.lexeme_start lexbuf)
          (Lexing.lexeme lexbuf)))}
