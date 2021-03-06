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
let alnum = (alpha | '_' | digit)*
let alnum' = (alpha | '_' | '-' | digit)*
let cap_name = ['A'-'Z'] alnum
let name = ['a'-'z'] alnum

rule token = parse
  | ['\r' '\n'] {next_line lexbuf; token lexbuf} 
  | [' ' '\t'] {token lexbuf}
  | "(*" {comment 0 lexbuf}
  | integer as n {NUM (int_of_string n)}
  | "\"" (alnum' as s) "\"" {STR s}
  | "&&" {AND}
  | "||" {OR} 
  | "#" {HASH}
  | "$" {DOLLAR}
  | "@" {AT}
  | "&" {AMPERSAND}
  | "_" {WILDCARD}
  | "::=" {GRAMMARASSIGN}
  | "," {COMMA}
  | "::" {CONS}
  | ":" {COLON}
  | ";" {SEMI}
  | "." {DOT}
  | "'" {TICK}
  | "!" {EXCL}
  | "^" {CARET}
  | "|-" {TURNSTILE}
  | "-->" {STEP}
  | "->" {ARROW}
  | "<:" {SUBTYPE}
  | "~" {TILDE}
  | "`" {BACKTICK}
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
  | "==>" {BIGARROW}
  | "=>" {MAPSTO}
  | "=" {EQ}
  | "lift" {LIFT}
  | "to" {TO}
  | "keep" {KEEP}
  | "skip" {SKIP}
  | "match" {MATCH}
  | "with" {WITH}
  | "when" {WHEN}
  | "less?" {QLESS}
  | "greater?" {QGREATER}
  | "member?" {QMEMBER}
  | "assoc?" {QASSOC}
  | "none?" {QNOTHING}
  | "some?" {QSOMETHING}
  | "empty?" {QEMPTY}
  | "var?" {QVAR}
  | "const_var?" {QCONSTVAR}
  | "str?" {QSTR}
  | "constructor?" {QCONSTRUCTOR}
  | "binding?" {QBINDING}
  | "subst?" {QSUBST}
  | "list?" {QLIST}
  | "tuple?" {QTUPLE}
  | "var_kind?" {QVARKIND}
  | "op_kind?" {QOPKIND}
  | "syntax?" {QSYNTAX}
  | "starts_with?" {QSTARTSWITH}
  | "ends_with?" {QENDSWITH}
  | "nil" {NIL}
  | "dom" {DOM}
  | "range" {RANGE}
  | "member" {MEMBER}
  | "not" {NOT}
  | "union" {UNION}
  | "map_union" {MAPUNION}
  | "map_union_uniq" {MAPUNIONUNIQ}
  | "subset" {SUBSET}
  | "zip" {ZIP}
  | "unzip" {UNZIP}
  | "fresh_var" {FRESHVAR}
  | "fresh" {FRESH}
  | "substitute" {SUBSTITUTE}
  | "var_overlap" {VAROVERLAP}
  | "nth" {NTH}
  | "head" {HEAD}
  | "tail" {TAIL}
  | "last" {LAST}
  | "diff" {DIFF}
  | "intersect" {INTERSECT}
  | "assoc!" {GETASSOC}
  | "assoc" {ASSOC}
  | "keys" {KEYS}
  | "length" {LENGTH}
  | "append" {APPEND}
  | "rev" {REV}
  | "dedup" {DEDUP}
  | "concat" {CONCAT}
  | "vars" {VARS}
  | "unbind" {UNBIND}
  | "bound" {BOUND}
  | "none" {NOTHING}
  | "some" {SOMETHING}
  | "get" {GET}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "let" {LET}
  | "rec" {REC}
  | "uppercase" {UPPERCASE}
  | "lowercase" {LOWERCASE}
  | "str_int" {STRINT}
  | "int_str" {INTSTR}
  | "self" {SELF}
  | "unify_normalize" {UNIFYNORMALIZE}
  | "unify" {UNIFY}
  | "uniquify" {UNIQUIFY}
  | "remove_syntax" {REMOVESYNTAX}
  | "meta_var" {METAVAR}
  | "categories" {CATEGORIES}
  | "syntax" {SYNTAX}
  | "var_kind" {VARKIND}
  | "op_kind" {OPKIND}
  | "add_relation" {ADDRELATION}
  | "relations" {RELATIONS}
  | "set_relations" {SETRELATIONS}
  | "remove_relation" {REMOVERELATION}
  | "rule_name" {RULENAME}
  | "premises" {PREMISES}
  | "Premises" {PREMISESELF}
  | "conclusion" {CONCLUSION}
  | "set_conclusion" {SETCONCLUSION}
  | "rules" {RULES}
  | "Rule" {CAPRULE}
  | "add_rules" {ADDRULES}
  | "add_rule" {ADDRULE}
  | "set_rules" {SETRULES}
  | "hint" {HINT}
  | "hint_list" {HINTLIST}
  | "remove_hint" {REMOVEHINT}
  | "lan" {LAN}
  | "rule" {RULE}
  | "formula" {FORMULA}
  | "term" {TERM}
  | "string" {STRING}
  | "bool" {BOOL}
  | "int" {INT}
  | "tuple" {TUPLE} 
  | "option" {OPTION}
  | "list" {LIST}
  | "true" {TRUE}
  | "false" {FALSE}
  | "in" {IN}
  | cap_name as n {CAPNAME n}
  | name as n {NAME n}
  | eof {EOF}
  | _ {raise (Error
        (Printf.sprintf "At offset %d: unexpected token %s.\n"
          (Lexing.lexeme_start lexbuf)
          (Lexing.lexeme lexbuf)))}
and comment depth = parse
  | '\n' {next_line lexbuf; comment depth lexbuf}
  | "(*" {comment (succ depth) lexbuf}
  | "*)"
    {
      match depth with
      | 0 -> token lexbuf
      | _ -> comment (pred depth) lexbuf
    }
  | eof {raise (Error
          (Printf.sprintf "At offset %d: unexpected EOF in comment %s.\n"
            (Lexing.lexeme_start lexbuf)
            (Lexing.lexeme lexbuf)))}
  | _ {comment depth lexbuf}
