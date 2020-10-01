open Core_kernel
open Lang_n_change

let () =
  let e = Parse_ltr.parse Sys.argv.(1) in
  Printf.printf "%s\n" (Ltr.generate_caml e)
