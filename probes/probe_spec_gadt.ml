

module Rt = struct
  let extract_int_be_unsigned (data : bytes) (off : int) (size : int) : int =
    let rec go acc i =
      if i = size then acc
      else
        let bit = off + i in
        let b = Char.code (Bytes.get data (bit lsr 3)) in
        let v = (b lsr (7 - (bit land 7))) land 1 in
        go ((acc lsl 1) lor v) (i + 1)
    in
    go 0 0
end


type off = Static of int | Dynamic of int expr

type ('f, 'r) spec =
  | Done : ('r expr, 'r) spec
  | Int : int * ('f, 'r) spec -> (int expr -> 'f, 'r) spec
      
type 'r case = Case : ('f, 'r) spec * 'f -> 'r case


$let rec spec_bits_ : type f r. (f, r) spec -> int = function
  | Done -> 0
  | Int (size, rest) -> size + spec_bits_ rest

$let[..] rec match_one_ :
  type f r. (f, r) spec -> bytes expr -> f -> off -> r expr =
  fun spec data k off ->
  match spec with
  | Done -> k
  | Int (size, rest) ->
      let ex =
        match off with
        | Static n ->
            << Rt.extract_int_be_unsigned $data $(Expr.int n)
                 $(Expr.int size) >>
        | Dynamic e ->
            << Rt.extract_int_be_unsigned $data $e $(Expr.int size) >>
      in
      let off' =
        match off with
        | Static n -> Static (n + size)
        | Dynamic e -> Dynamic << $e + $(Expr.int size) >>
      in
      << let v = $ex in $(match_one_ rest data (k << v >>) off') >>

$let[..] rec match_cases_ :
  'r. 'r case list -> bytes expr -> int expr -> (unit -> 'r) expr -> 'r expr =
  fun cases data avail_bits fallback ->
  match cases with
  | [] -> << $fallback () >>
  | Case (spec, k) :: rest ->
      << if $avail_bits >= $(Expr.int (spec_bits_ spec)) then
           $(match_one_ spec data k (Static 0))
         else $(match_cases_ rest data avail_bits fallback) >>


let () =
  let data = Bytes.of_string "\xab\x5a" in
  let avail = 8 * Bytes.length data in

    let sum =
    $(match_one_
        (Int (8, Int (4, Int (4, Done))))
        << data >>
        (fun a b c -> << $a + $b + $c >>)
        (Static 0))
  in
  assert (sum = 0xab + 0x5 + 0xa);

    let sq =
    $(match_one_ (Int (8, Done)) << data >> (fun a -> << $a * $a >>)
        (Static 0))
  in
  assert (sq = 0xab * 0xab);

    let tag =
    $(match_cases_
        [ Case (Int (24, Done), (fun a -> << `Wide $a >>));
          Case (Int (8, Done), (fun a -> << `Byte $a >>)) ]
        << data >> << avail >>
        << fun () -> `None >>)
  in
  assert (tag = `Byte 0xab);

    let none =
    $(match_cases_
        [ Case (Int (24, Done), (fun a -> << `Wide $a >>)) ]
        << data >> << 8 >>
        << fun () -> `None >>)
  in
  assert (none = `None);

  print_endline "probe_spec_gadt: all assertions passed"
