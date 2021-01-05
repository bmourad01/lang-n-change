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
let integer = digit+
let alpha = ['a'-'z' 'A'-'Z']
let name = ['a'-'z' 'A'-'Z'] (alpha | '_' | '-' | '\'' | digit)*

rule token = parse                            
  | ['\r' '\n'] {next_line lexbuf; token lexbuf} 
  | [' ' '\t'] {token lexbuf}
  | integer as n {NUM (int_of_string n)}
  | "\"" (name as s) "\"" {STRING s}
  | '%' {MOD}
  | "::=" {GRAMMARASSIGN}
  | "," {COMMA}
  | "::" {CONS}
  | ":" {COLON}
  | "." {DOT}
  | "_" {WILDCARD}
  | "~" {TILDE}
  | "|-" {TURNSTILE}
  | "-->" {STEP}
  | "<:" {SUBTYPE}
  | "|" {MID}
  | "[" {LSQUARE}
  | "]" {RSQUARE}
  | "{" {LBRACE}
  | "}" {RBRACE}
  | "(" {LPAREN}
  | ")" {RPAREN}
  | "<" {LANGLE}
  | ">" {RANGLE}
  | "-" {DASH}
  | "/" {FSLASH}
  | "==>" {BIGARROW}
  | "=>" {MAPSTO}
  | "=" {EQ}
  | "nil" {NIL}
  | "dom" {DOM}
  | "range" {RANGE}
  | "member" {MEMBER}
  | "not" {NOT}
  | "union" {UNION}
  | "map_union" {MAPUNION}
  | "subset" {SUBSET}
  | "zip" {ZIP}
  | "fresh" {FRESH}
  | name as s {NAME s}
  | eof {EOF}
  | _ {raise (Error
        (Printf.sprintf "At offset %d: unexpected token %s.\n"
          (Lexing.lexeme_start lexbuf)
          (Lexing.lexeme lexbuf)))}
