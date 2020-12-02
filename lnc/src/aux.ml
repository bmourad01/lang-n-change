open Core_kernel

let dedup_list_stable l ~compare =
  let equal x x' = compare x x' = 0 in
  let rec loop res = function
    | [] -> res
    | x :: xs ->
        let dups = List.find_all_dups (x :: xs) ~compare in
        let res = if List.mem dups x ~equal then res else x :: res in
        loop res xs
  in
  loop [] (List.rev l)

let diff_list_stable l1 l2 ~equal =
  List.filter l1 ~f:(fun x -> not (List.mem l2 x ~equal))

let intersect_list_stable l1 l2 ~equal =
  List.filter l1 ~f:(fun x -> List.mem l2 x ~equal)

let interleave_pairs_of_list l =
  let rec loop = function
    | [] -> []
    | x :: y :: rest -> (x, y) :: loop (y :: rest)
    | [x] -> []
  in
  loop l
