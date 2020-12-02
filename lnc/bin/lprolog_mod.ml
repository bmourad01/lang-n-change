open Core_kernel
open Lang_n_change

let () =
  let filename = Sys.argv.(1) in
  let lprolog = Parse_language.parse filename |> Lprolog.of_language in
  let basename =
    Filename.basename filename |> String.chop_suffix_if_exists ~suffix:".lan"
  in
  Printf.printf "module %s.\n\n%s\n" basename
    ( Map.data lprolog.rules
    |> List.map ~f:Lprolog.Rule.to_string
    |> String.concat ~sep:"\n\n" )
