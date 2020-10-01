open Core_kernel
open Lang_n_change

let () =
  let lan = Parse_language.parse Sys.argv.(1) in
  Printf.printf "%s\n"
    (Transform.transform lan
     |> Language.to_string)
