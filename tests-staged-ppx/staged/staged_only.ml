
let tail_string bs =
  match%bitstring bs with
  | {| _ : 8 ; s : -1 : string |} -> Some s
  | {| _ |} -> None
