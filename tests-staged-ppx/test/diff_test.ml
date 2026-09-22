
module S = Matchers_staged.Matchers
module P = Matchers_plain.Matchers

let subjects =
  let raw =
    [ "";
      "\xab";
      "\xab\x12";
      "\xab\x13\x02hi\x34\x12";           
      "\xab\x03\x02hi\x34\x12";           
      "\xcd\x13\x02hi\x34\x12";           
      "\xab\x1f\x05apple\xff\x00tail";
      "\x02even";
      "\x03odd";
      "\xa5\x3c\x7e\x01\xff\x80\x42\x99\xde\xad\xbe\xef\x01\x23\x45\x67\x89";
      "\x07\xff\xff\xff\xff\xff\xff\xff\xff\xff" ]
  in
  let bss = List.map Bitstring.bitstring_of_string raw in
    let rich =
    Bitstring.bitstring_of_string
      "\xa5\x3c\x7e\x01\xff\x80\x42\x99\xde\xad\xbe\xef\x01\x23\x45\x67\x89\xab"
  in
  let prefixes =
    List.init (Bitstring.bitstring_length rich + 1) (fun n ->
        Bitstring.takebits n rich)
  in
  let misaligned =
    List.init 7 (fun k -> Bitstring.dropbits (k + 1) rich)
  in
  bss @ prefixes @ misaligned

let check name f g =
  List.iteri
    (fun i bs ->
      if f bs <> g bs then (
        Printf.printf "MISMATCH %s on subject %d\n" name i;
        exit 1))
    subjects;
  Printf.printf "%s: ok (%d subjects)\n" name (List.length subjects)

module SC = Matchers_staged.Constructors
module PC = Matchers_plain.Constructors

let bits_eq a b =
  Bitstring.bitstring_length a = Bitstring.bitstring_length b
  && Bitstring.string_of_bitstring a = Bitstring.string_of_bitstring b

let ccheck name f g =
  if not (bits_eq f g) then (
    Printf.printf "CONSTRUCT MISMATCH %s\n" name;
    exit 1);
  Printf.printf "construct %s: ok\n" name

let same_failure name f g =
  let outcome h =
    match h () with
    | (_ : Bitstring.t) -> `Ok
    | exception Bitstring.Construct_failure _ -> `CF
    | exception Exit -> `Exit
  in
  if outcome f <> outcome g then (
    Printf.printf "FAILURE-MODE MISMATCH %s\n" name;
    exit 1);
  Printf.printf "failure mode %s: ok\n" name

let () =
  ccheck "packet" (SC.packet 3 2 "hi" 0x1234) (PC.packet 3 2 "hi" 0x1234);
  (let sub = Bitstring.takebits 12 (Bitstring.bitstring_of_string "\xbe\xef") in
   ccheck "mixed"
     (SC.mixed true 17 (-100) 99999 0xdeadbeefl 0x123456789aL "ok" sub)
     (PC.mixed true 17 (-100) 99999 0xdeadbeefl 0x123456789aL "ok" sub));
  ccheck "dyn_i" (SC.dyn_i 7 0xffffL) (PC.dyn_i 7 0xffffL);
  ccheck "endian be" (SC.with_endian Bitstring.BigEndian 0x1234)
    (PC.with_endian Bitstring.BigEndian 0x1234);
  ccheck "endian le" (SC.with_endian Bitstring.LittleEndian 0x1234)
    (PC.with_endian Bitstring.LittleEndian 0x1234);
  ccheck "let%bitstring" (SC.lb 0x7f) (PC.lb 0x7f);
  same_failure "overflow" (fun () -> SC.mixed true 63 2047 1 0l 0L "xx"
    (Bitstring.takebits 12 (Bitstring.bitstring_of_string "\xbe\xef")))
    (fun () -> PC.mixed true 63 2047 1 0l 0L "xx"
    (Bitstring.takebits 12 (Bitstring.bitstring_of_string "\xbe\xef")));
  same_failure "bad length" (fun () -> SC.packet 3 2 "toolong" 0)
    (fun () -> PC.packet 3 2 "toolong" 0);
    (Random.init 42;
   for _ = 1 to 2000 do
     let magic = Random.int 65536
     and v1 = Random.int 16
     and v2 = Random.int 16
     and b = Random.bool ()
     and flags = Random.int 128
     and seq = Random.int32 Int32.max_int
     and name = String.init 4 (fun _ -> Char.chr (Random.int 256)) in
     if
       not
         (bits_eq
            (SC.hdr magic v1 v2 b flags seq name)
            (PC.hdr magic v1 v2 b flags seq name))
     then (
       print_endline "PACKER MISMATCH hdr";
       exit 1)
   done;
   print_endline "packer sweep (2000 random headers): ok");
  same_failure "packer range" (fun () -> SC.hdr 1 99 0 false 0 0l "abcd")
    (fun () -> PC.hdr 1 99 0 false 0 0l "abcd");
  same_failure "packer strlen" (fun () -> SC.hdr 1 1 0 false 0 0l "abc")
    (fun () -> PC.hdr 1 1 0 false 0 0l "abc")

let () =
  check "classify" S.classify P.classify;
  check "fields" S.fields P.fields;
  check "checked" S.checked P.checked;
  check "skipping" S.skipping P.skipping;
  check "dyn_int" S.dyn_int P.dyn_int;
  check "referred be" (S.referred Bitstring.BigEndian)
    (P.referred Bitstring.BigEndian);
  check "referred le" (S.referred Bitstring.LittleEndian)
    (P.referred Bitstring.LittleEndian);
  check "quals (map/save/bind)" S.quals P.quals;
    List.iteri
    (fun i bs ->
      if Bitstring.bitstring_length bs >= 32 || Bitstring.bitstring_length bs < 8
      then
        if S.seeked bs <> P.seeked bs then (
          Printf.printf "MISMATCH seeked on subject %d\n" i;
          exit 1))
    subjects;
  print_endline "seeked (well-defined subjects): ok";
  (let short = Bitstring.bitstring_of_string "\x01\x02\x03" in
   assert (S.seeked short = None));
  print_endline "seeked staged bounds-check: ok";
  check "aliased" S.aliased P.aliased;
  (let bs = Bitstring.bitstring_of_string "\x00rest" in
   assert (Matchers_staged.Staged_only.tail_string bs = Some "rest"));
  print_endline "-1:string staged semantics: ok";
  print_endline "staged-vs-ppx differential: all ok"
