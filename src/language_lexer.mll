{
  open Lexing
  open Language_parser

  exception Error of string

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      {pos with pos_lnum = pos.pos_lnum + 1;
                pos_bol = pos.pos_cnum}
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let name = ['a'-'z' 'A'-'Z'] (alpha | '_' | '-' | '\'' | digit)*
let integer = digit+

rule token = parse                            
  | ['\r' '\n'] {next_line lexbuf; token lexbuf} 
  | [' ' '\t'] {token lexbuf}
  | '%' {MOD}
  | "::=" {GRAMMARASSIGN}
  | "," {COMMA}
  | ":" {COLON}
  | "." {DOT}
  | "_" {WILDCARD}
  | "|" {MID}
  | "[" {LSQUARE}
  | "]" {RSQUARE}
  | "(" {LPAREN}
  | ")" {RPAREN}
  | "{" {LBRACE}
  | "}" {RBRACE}
  | "<" {LANGLE}
  | ">" {RANGLE}
  | "-" {DASH}
  | "/" {FSLASH}
  | "=>" {MAPSTO}
  | "=" {EQ}
  | "in" {IN}
  | "forall" {FORALL}
  | "find" {FIND}
  | "where" {WHERE}
  | "with" {WITH}
  | "dom" {DOM}
  | "range" {RANGE}
  | "member" {MEMBER}
  | "not" {NOT}
  | "\"" {QUOTE}
  | integer as n {INT (int_of_string n)}
  | name as n {NAME n}
  | eof {EOF}
  | _ {raise (Error
        (Printf.sprintf "At offset %d: unexpected token %s.\n"
          (Lexing.lexeme_start lexbuf)
          (Lexing.lexeme lexbuf)))}
