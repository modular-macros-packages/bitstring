

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


macro spec_bits_ : 'f 'r. ('f, 'r) spec -> int = fun spec ->
  let rec go : type f r. (f, r) spec -> int = function
    | Done -> 0
    | Int (size, rest) -> size + go rest
  in
  go spec

macro match_one_ : 'f 'r. ('f, 'r) spec -> bytes expr -> 'f -> 'r expr =
  fun spec data k ->
  let rec go : type f r. (f, r) spec -> f -> off -> r expr =
    fun spec k off ->
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
          << let v = $ex in $(go rest (k << v >>) off') >>
  in
  go spec k (Static 0)

macro match_cases_ :
  'r. 'r case list -> bytes expr -> int expr -> (unit -> 'r) expr -> 'r expr =
  fun cases data avail_bits fallback ->
  let rec go : 'r case list -> 'r expr = function
    | [] -> << $fallback () >>
    | Case (spec, k) :: rest ->
        << if $avail_bits >= $(Expr.int (spec_bits_ spec)) then
             $(match_one_ spec data k)
           else $(go rest) >>
  in
  go cases


let () =
  let data = Bytes.of_string "\xab\x5a" in
  let avail = 8 * Bytes.length data in

    let sum =
    $(match_one_
        (Int (8, Int (4, Int (4, Done))))
        << data >>
        (fun a b c -> << $a + $b + $c >>))
  in
  assert (sum = 0xab + 0x5 + 0xa);

    let sq =
    $(match_one_ (Int (8, Done)) << data >> (fun a -> << $a * $a >>))
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
