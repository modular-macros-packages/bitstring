
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


$let u8 : int_desc = { size = 8; sign = Unsigned; endian = Big }
$let s8 : int_desc = { size = 8; sign = Signed; endian = Big }
$let u4 : int_desc = { size = 4; sign = Unsigned; endian = Big }
$let u16 : int_desc = { size = 16; sign = Unsigned; endian = Big }

let tagged bs =
  $(match_ << bs >>
      [ IntLit (u8, 1, Int (u8, fun a -> Done << `A $a >>));
        IntLit (u8, 2, Int (u16, fun w -> Done << `B $w >>));
        IntLit (u8, 3, Int (u8, fun len ->
            String (Dyn << $len * 8 >>, fun s -> Done << `C ($len, $s) >>)));
        IntLit (u8, 4, Int (u8, fun v -> Guard (<< $v > 100 >>, Done << `Dbig $v >>)));
        IntLit (u8, 4, Int (u8, fun v -> Done << `D $v >>));
        IntLit (u8, 5, Done << `E >>);
        IntLit (u8, 6, Bits (All, fun r ->
            Done << `F (Bitstring.bitstring_length $r) >>)) ]
      ~default:<< fun () -> `None >>)

let ref_tagged (d, o, l) =
  if l < 8 then `None
  else
    let tag = Bitstring.extract_char_unsigned d o l 8 in
    let o' = o + 8 and l' = l - 8 in
    match tag with
    | 1 when l' >= 8 -> `A (Bitstring.extract_char_unsigned d o' l' 8)
    | 2 when l' >= 16 -> `B (Bitstring.extract_int_be_unsigned d o' l' 16)
    | 3 when l' >= 8 ->
        let len = Bitstring.extract_char_unsigned d o' l' 8 in
        if l' - 8 >= len * 8 then
          `C (len, Bitstring.string_of_bitstring (d, o' + 8, len * 8))
        else `None
    | 4 when l' >= 8 ->
        let v = Bitstring.extract_char_unsigned d o' l' 8 in
        if v > 100 then `Dbig v else `D v
    | 5 -> `E
    | 6 -> `F l'
    | _ -> `None

let mixed bs =
  $(match_ << bs >>
      [ IntLit (u8, 1, Int (u8, fun a -> Done << `A $a >>));
        IntLit (u8, 2, Int (u8, fun a -> Done << `B $a >>));
        Int (u8, fun t -> IntLit (u8, 0xff, Done << `Esc $t >>));
        IntLit (u8, 3, IntLit (u8, 0x10, Int (u8, fun a -> Done << `C1 $a >>)));
        IntLit (u8, 3, IntLit (u8, 0x20, Int (u8, fun a -> Done << `C2 $a >>)));
        IntLit (u8, 3, Int (u8, fun sub -> Int (u8, fun a -> Done << `C ($sub, $a) >>)));
        IntLit (u8, 4, Done << `D >>) ]
      ~default:<< fun () -> `None >>)

let ref_mixed (d, o, l) =
  if l < 8 then `None
  else
    let tag = Bitstring.extract_char_unsigned d o l 8 in
    let o' = o + 8 and l' = l - 8 in
    let byte k = Bitstring.extract_char_unsigned d (o' + (8 * k)) (l' - (8 * k)) 8 in
    match tag with
    | 1 when l' >= 8 -> `A (byte 0)
    | 2 when l' >= 8 -> `B (byte 0)
    | _ when l' >= 8 && byte 0 = 0xff -> `Esc tag
    | 3 when l' >= 16 && byte 0 = 0x10 -> `C1 (byte 1)
    | 3 when l' >= 16 && byte 0 = 0x20 -> `C2 (byte 1)
    | 3 when l' >= 16 -> `C (byte 0, byte 1)
    | 4 -> `D
    | _ -> `None

let signed_tagged bs =
  $(match_ << bs >>
      [ IntLit (s8, -1, Int (u8, fun a -> Done << `M1 $a >>));
        IntLit (s8, -2, Int (u8, fun a -> Done << `M2 $a >>));
        IntLit (s8, 3, Int (u8, fun a -> Done << `P3 $a >>));
        IntLit (s8, 200, Int (u8, fun a -> Done << `Never $a >>)) ]
      ~default:<< fun () -> `None >>)

let ref_signed_tagged (d, o, l) =
  if l < 16 then `None
  else
    let tag = Bitstring.extract_char_signed d o l 8 in
    let a = Bitstring.extract_char_unsigned d (o + 8) (l - 8) 8 in
    match tag with -1 -> `M1 a | -2 -> `M2 a | 3 -> `P3 a | _ -> `None

let nibble bs =
  $(match_ << bs >>
      (List.init 16 (fun k ->
           IntLit (u4, k, Int (u4, fun x -> Done << ($(Expr.int k), $x) >>))))
      ~default:<< fun () -> (-1, -1) >>)

let ref_nibble (d, o, l) =
  if l < 8 then (-1, -1)
  else
    ( Bitstring.extract_char_unsigned d o l 4,
      Bitstring.extract_char_unsigned d (o + 4) (l - 4) 4 )

let wide bs =
  $(match_ << bs >>
      [ IntLit (u16, 0xCAFE, Int (u8, fun a -> Done << `Cafe $a >>));
        IntLit (u16, 0xBEEF, Int (u8, fun a -> Done << `Beef $a >>));
        IntLit (u8, 9, Done << `Nine >>) ]
      ~default:<< fun () -> `None >>)

let ref_wide (d, o, l) =
  if l >= 24 && Bitstring.extract_int_be_unsigned d o l 16 = 0xCAFE then
    `Cafe (Bitstring.extract_char_unsigned d (o + 16) (l - 16) 8)
  else if l >= 24 && Bitstring.extract_int_be_unsigned d o l 16 = 0xBEEF then
    `Beef (Bitstring.extract_char_unsigned d (o + 16) (l - 16) 8)
  else if l >= 8 && Bitstring.extract_char_unsigned d o l 8 = 9 then `Nine
  else `None

let dispatch_subjects =
  let tails = [ ""; "\x42"; "\x42\x43"; "\x10\x42"; "\x20\x42"; "\xff";
                "\x02ab"; "\x02a"; "\x00"; "\xc8"; "\x32\x99\x11" ] in
  let tags = List.init 10 Char.chr @ [ '\xff'; '\xfe'; '\xc8'; '\x7f';
                                       '\xca'; '\xbe'; '\x09' ] in
  let bytes =
    List.concat_map (fun t -> List.map (fun tl -> String.make 1 t ^ tl) tails) tags
    @ [ "\xca\xfe\x07"; "\xbe\xef\x09"; "\xca\xfe"; "\xbe\xef" ]
  in
  let misalign k bs =
    Bitstring.dropbits k
      (Bitstring.concat [ Bitstring.takebits k (Bitstring.bitstring_of_string "\xa7"); bs ])
  in
    let prefixes s =
    let bs = Bitstring.bitstring_of_string s in
    List.init (Bitstring.bitstring_length bs + 1) (fun n -> Bitstring.takebits n bs)
  in
  let whole = List.map Bitstring.bitstring_of_string bytes in
  List.concat_map (fun bs -> List.init 8 (fun k -> misalign k bs)) whole
  @ prefixes "\x03\x02ab" @ prefixes "\x04\xc8" @ prefixes "\xff\x42"

let test_dispatch () =
  let n = ref 0 in
  let check name f g =
    List.iter (fun bs -> incr n; if f bs <> g bs then failwith ("dispatch mismatch: " ^ name)) dispatch_subjects
  in
  check "tagged" tagged ref_tagged;
  check "mixed" mixed ref_mixed;
  check "signed_tagged" signed_tagged ref_signed_tagged;
  check "nibble" nibble ref_nibble;
  check "wide" wide ref_wide;
    let s = Bitstring.bitstring_of_string in
  assert (tagged (s "\x04\xc8") = `Dbig 200);
  assert (tagged (s "\x04\x32") = `D 50);
  assert (tagged (s "\x03\x02ab") = `C (2, "ab"));
  assert (tagged (s "\x03\x02a") = `None);
  assert (tagged (s "\x07\x42") = `None);
  assert (tagged (s "") = `None);
  assert (mixed (s "\x01\xff") = `A 0xff);
  assert (mixed (s "\x05\xff") = `Esc 5);
  assert (mixed (s "\x03\x20\x42") = `C2 0x42);
  assert (mixed (s "\x03\x30\x42") = `C (0x30, 0x42));
  assert (signed_tagged (s "\xff\x42") = `M1 0x42);
  assert (signed_tagged (s "\xc8\x42") = `None);
  assert (nibble (s "\xf3") = (15, 3));
  assert (wide (s "\xca\xfe\x07") = `Cafe 7);
  assert (wide (s "\x09") = `Nine);
  Printf.printf "tag dispatch: ok (%d checks)\n" !n

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
  test_dispatch ();
  print_endline "bitstring.staged battery: all ok"
