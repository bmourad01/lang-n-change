open Core_kernel
open Lang_n_change

let () =
  let lprolog =
    Parse_language.parse Sys.argv.(1)
    |> Lprolog.of_language
  in
  Printf.printf "%s\n\n%s\n"
    (Lprolog.Sigs.to_string lprolog.sigs)
    (Map.data lprolog.rules
     |> List.map ~f:Lprolog.Rule.to_string
     |> String.concat ~sep:"\n\n")
