
open Bitstring_staged

let fail () = failwith "unexpected fall-through"

let base =
  Bitstring.bitstring_of_string
    "\xa5\x3c\x7e\x01\xff\x80\x42\x99\xde\xad\xbe\xef\x01\x23\x45\x67\x89\xab\xcd\xef"


let test_static_mixed sub name =
  let d, o, l = sub in
    let r_bit = Bitstring.extract_bit d o l 1 in
  let r_i5 = Bitstring.extract_char_unsigned d (o + 1) (l - 1) 5 in
  let r_i12 = Bitstring.extract_int_be_signed d (o + 6) (l - 6) 12 in
  let r_i20 = Bitstring.extract_int_le_unsigned d (o + 18) (l - 18) 20 in
  let r_32 = Bitstring.extract_int32_be_unsigned d (o + 38) (l - 38) 32 in
  let r_48 = Bitstring.extract_int64_le_unsigned d (o + 70) (l - 70) 48 in
  let r_str = Bitstring.string_of_bitstring (d, o + 118, 16) in
  let r_bits = Bitstring.string_of_bitstring (d, o + 134, 12) in
  let staged =
    $(match_ << sub >>
        [ Bit (fun b ->
              Int ({ size = 5; sign = Unsigned; endian = Big }, fun i5 ->
                  Int ({ size = 12; sign = Signed; endian = Big }, fun i12 ->
                      Int ({ size = 20; sign = Unsigned; endian = Little },
                          fun i20 ->
                            Int32 (Big, fun i32 ->
                                Int64 ({ size64 = Const 48;
                                         endian64 = Little }, fun i48 ->
                                    String (Const 16, fun s ->
                                        Bits (Const 12, fun bits ->
                                            Done
                                              << ( $b, $i5, $i12, $i20, $i32,
                                                   $i48, $s,
                                                   Bitstring.string_of_bitstring
                                                     $bits ) >>)))))))) ]
        ~default:<< fun () -> fail () >>)
  in
  assert (staged = (r_bit, r_i5, r_i12, r_i20, r_32, r_48, r_str, r_bits));
  Printf.printf "static mixed (%s): ok\n" name


let test_dependent () =
    let bs = Bitstring.bitstring_of_string "\x03abc\x7f" in
  let staged =
    $(match_ << bs >>
        [ Int ({ size = 8; sign = Unsigned; endian = Big }, fun len ->
              String (Dyn << $len * 8 >>, fun payload ->
                  Int ({ size = 8; sign = Unsigned; endian = Big },
                      fun trailer -> Done << ($len, $payload, $trailer) >>))) ]
        ~default:<< fun () -> fail () >>)
  in
  assert (staged = (3, "abc", 0x7f));
  print_endline "field-dependent size: ok"


let cascade bs =
  $(match_ << bs >>
      [ Int64 ({ size64 = Const 64; endian64 = Big }, fun v ->
            Done << `Wide $v >>);
        Int ({ size = 16; sign = Unsigned; endian = Big }, fun v ->
            Done << `Narrow $v >>) ]
      ~default:<< fun () -> `None >>)

let test_cascade () =
  let bs64 = Bitstring.bitstring_of_string "\x01\x02\x03\x04\x05\x06\x07\x08" in
  let bs32 = Bitstring.bitstring_of_string "\xbe\xef\x01\x02" in
  let bs8 = Bitstring.bitstring_of_string "\x55" in
  assert (cascade bs64 = `Wide 0x0102030405060708L);
  let d, o, l = bs32 in
  assert (cascade bs32 = `Narrow (Bitstring.extract_int_be_unsigned d o l 16));
  assert (cascade bs8 = `None);
  print_endline "cascade/fall-through/default: ok"


let test_rest () =
  let bs = Bitstring.bitstring_of_string "\xab\xcd\xef" in
  let tag, rest_s =
    $(match_ << bs >>
        [ Int ({ size = 8; sign = Unsigned; endian = Big }, fun tag ->
              Bits (All, fun rest ->
                  Done << ($tag, Bitstring.string_of_bitstring $rest) >>)) ]
        ~default:<< fun () -> fail () >>)
  in
  assert (tag = 0xab);
  assert (rest_s = Bitstring.string_of_bitstring (Bitstring.dropbits 8 bs));
  print_endline "rest: ok"


let test_referred rt_endian =
  let bs = Bitstring.bitstring_of_string "\x12\x34\x56\x78" in
  let d, o, l = bs in
  let staged =
    $(match_ << bs >>
        [ Int ({ size = 24; sign = Unsigned;
                 endian = Referred << rt_endian >> }, fun v ->
              Done << $v >>) ]
        ~default:<< fun () -> fail () >>)
  in
  assert (staged = Bitstring.extract_int_ee_unsigned rt_endian d o l 24);
  Printf.printf "referred endian (%s): ok\n"
    (Bitstring.string_of_endian rt_endian)


let test_signed () =
  let bs = Bitstring.bitstring_of_string "\xff\xff" in
  let neg1_char, neg1_int =
    $(match_ << bs >>
        [ Int ({ size = 4; sign = Signed; endian = Big }, fun a ->
              Int ({ size = 12; sign = Signed; endian = Big }, fun b ->
                  Done << ($a, $b) >>)) ]
        ~default:<< fun () -> fail () >>)
  in
  assert (neg1_char = -1);
  assert (neg1_int = -1);
  print_endline "signed: ok"


let guarded bs =
  $(match_ << bs >>
      [ Int ({ size = 8; sign = Unsigned; endian = Big }, fun v ->
            Guard (<< $v land 1 = 0 >>, Done << `Even $v >>));
        Int ({ size = 8; sign = Unsigned; endian = Big }, fun v ->
            Done << `Odd $v >>) ]
      ~default:<< fun () -> `None >>)

let test_guard () =
  assert (guarded (Bitstring.bitstring_of_string "\x02") = `Even 2);
  assert (guarded (Bitstring.bitstring_of_string "\x03") = `Odd 3);
  print_endline "guard: ok"


let test_string_all () =
  let bs = Bitstring.bitstring_of_string "\x01rest" in
  let tag, s =
    $(match_ << bs >>
        [ Int ({ size = 8; sign = Unsigned; endian = Big }, fun tag ->
              String (All, fun s -> Done << ($tag, $s) >>)) ]
        ~default:<< fun () -> fail () >>)
  in
  assert (tag = 1);
  assert (s = "rest");
  print_endline "string all: ok"

let () =
  test_static_mixed base "aligned";
  test_static_mixed (Bitstring.dropbits 3 base) "misaligned+3";
  test_dependent ();
  test_cascade ();
  test_rest ();
  test_referred Bitstring.BigEndian;
  test_referred Bitstring.LittleEndian;
  test_referred Bitstring.NativeEndian;
  test_signed ();
  test_guard ();
  test_string_all ();
  print_endline "bitstring.staged battery: all ok"
