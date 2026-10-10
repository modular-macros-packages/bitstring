

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

    let extract_fastpath_char_unsigned (data : bytes) (byte_off : int) : int =
    Char.code (Bytes.get data byte_off)
end


type off = Static of int | Dynamic of int expr

$let[..] extract_u_be_ : size:int -> off:off -> bytes expr -> int expr =
  fun ~size ~off data ->
  match off with
  | Static n when size = 8 && n land 7 = 0 ->
        << Rt.extract_fastpath_char_unsigned $data $(Expr.int (n asr 3)) >>
  | Static n ->
    << Rt.extract_int_be_unsigned $data $(Expr.int n) $(Expr.int size) >>
  | Dynamic e ->
    << Rt.extract_int_be_unsigned $data $e $(Expr.int size) >>

$let check_avail_ : bits:int -> avail:int expr -> 'a expr -> 'a option expr =
  fun ~bits ~avail k ->
  << if $avail >= $(Expr.int bits) then Some $k else None >>

$let construct2_aligned_ : size1:int -> size2:int
  -> int expr -> int expr -> bytes expr =
  fun ~size1 ~size2 v1 v2 ->
  assert (size1 = 8 && size2 = 8);          
  let total_bytes = (size1 + size2 + 7) asr 3 in
  << let b = Bytes.create $(Expr.int total_bytes) in
     Bytes.set b 0 (Char.chr ($v1 land 0xff));
     Bytes.set b 1 (Char.chr ($v2 land 0xff));
     b >>


let () =
    let data = Bytes.of_string "\xab\x5a\xcd" in
  let avail = 8 * Bytes.length data in

    let f1 = $(extract_u_be_ ~size:8 ~off:(Static 0) << data >>) in
  assert (f1 = 0xab);

    let f2 = $(extract_u_be_ ~size:4 ~off:(Static 8) << data >>) in
  assert (f2 = 0x5);

    let dyn_off = 12 in
  let f3 = $(extract_u_be_ ~size:4 ~off:(Dynamic << dyn_off >>) << data >>) in
  assert (f3 = 0xa);

    let checked =
    $(check_avail_ ~bits:16 ~avail:<< avail >>
        << ($(extract_u_be_ ~size:8 ~off:(Static 0) << data >>),
            $(extract_u_be_ ~size:8 ~off:(Static 8) << data >>)) >>)
  in
  assert (checked = Some (0xab, 0x5a));

    let packet = $(construct2_aligned_ ~size1:8 ~size2:8 << 0xde >> << 0xad >>) in
  assert (Bytes.to_string packet = "\xde\xad");

  print_endline "probe_field_macros: all assertions passed"
