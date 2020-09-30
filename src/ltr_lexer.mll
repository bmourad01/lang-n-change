{
  open Lexing
  open Ltr_parser

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
  | "\"" (name as s) "\"" {STRING s}
  | "%" {MOD}
  | "::=" {GRAMMARASSIGN}
  | "," {COMMA}
  | "::" {CONS}
  | ":" {COLON}
  | ";" {SEMI}
  | "." {DOT}
  | "'" {TICK}
  | "!" {EXCL}
  | "^" {CARET}
  | "|-" {TURNSTYLE}
  | "-->" {STEP}
  | "<:" {SUBTYPE}
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
  | "member?" {QMEMBER}
  | "nothing?" {QNOTHING}
  | "something?" {QSOMETHING}
  | "empty?" {QEMPTY}
  | "var?" {QVAR}
  | "str?" {QSTR}
  | "constructor?" {QCONSTRUCTOR}
  | "binding?" {QBINDING}
  | "subst?" {QSUBST}
  | "list?" {QLIST}
  | "map?" {QMAP}
  | "tuple?" {QTUPLE}
  | "var_kind?" {QVARKIND}
  | "op_kind?" {QOPKIND}
  | "syntax?" {QSYNTAX}
  | "nil" {NIL}
  | "dom" {DOM}
  | "range" {RANGE}
  | "member" {MEMBER}
  | "not" {NOT}
  | "union" {UNION}
  | "map_union" {MAPUNION}
  | "subset" {SUBSET}
  | "zip" {ZIP}
  | "fresh_var" {FRESHVAR}
  | "fresh" {FRESH}
  | "substitute" {SUBSTITUTE}
  | "var_overlap" {VAROVERLAP}
  | "nth" {NTH}
  | "head" {HEAD}
  | "tail" {TAIL}
  | "last" {LAST}
  | "diff" {DIFF}
  | "assoc" {ASSOC}
  | "append" {APPEND}
  | "rev" {REV}
  | "dedup" {DEDUP}
  | "concat" {CONCAT}
  | "vars" {VARS}
  | "unbind" {UNBIND}
  | "bound" {BOUND}
  | "nothing" {NOTHING}
  | "something" {SOMETHING}
  | "get" {GET}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "let" {LET}
  | "rec" {REC}
  | "uppercase" {UPPERCASE}
  | "lowercase" {LOWERCASE}
  | "int_str" {INTSTR}
  | "self" {SELF}
  | "uniquify" {UNIQUIFY}
  | "remove_syntax" {REMOVESYNTAX}
  | "meta_var" {METAVAR}
  | "syntax" {SYNTAX}
  | "rule_name" {RULENAME}
  | "premises" {PREMISES}
  | "conclusion" {CONCLUSION}
  | "rules" {RULES}
  | "add_rule" {ADDRULE}
  | "set_rules" {SETRULES}
  | "hint" {HINT}
  | "and" {AND}
  | "or" {OR} 
  | name as n {NAME n}
  | integer as n {INT (int_of_string n)}
  | eof {EOF}
  | _ {raise (Error
        (Printf.sprintf "At offset %d: unexpected token %s.\n"
          (Lexing.lexeme_start lexbuf)
          (Lexing.lexeme lexbuf)))}
