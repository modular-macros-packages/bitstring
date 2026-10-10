
module S = Matchers_staged.Matchers
module P = Matchers_plain.Matchers
module SC = Matchers_staged.Constructors
module PC = Matchers_plain.Constructors

let time name f =
  let t0 = Unix.gettimeofday () in
  f ();
  let t1 = Unix.gettimeofday () in
  Printf.printf "  %-28s %8.1f ns/op\n" name (1e9 *. (t1 -. t0) /. 2e6)

let n = 2_000_000

let () =
  print_endline "construct (static header, 13 bytes):";
  time "classic ppx (Buffer)" (fun () ->
      for _ = 1 to n do
        ignore (Sys.opaque_identity (PC.hdr 0xCAFE 3 7 true 42 0xDEADBEEl "name"))
      done);
  time "staged (single alloc)" (fun () ->
      for _ = 1 to n do
        ignore (Sys.opaque_identity (SC.hdr 0xCAFE 3 7 true 42 0xDEADBEEl "name"))
      done);
  print_endline "construct (dynamic packet):";
  time "classic ppx" (fun () ->
      for _ = 1 to n do
        ignore (Sys.opaque_identity (PC.packet 3 2 "hi" 0x1234))
      done);
  time "staged (Buffer fallback)" (fun () ->
      for _ = 1 to n do
        ignore (Sys.opaque_identity (SC.packet 3 2 "hi" 0x1234))
      done);
    let subjects =
    Array.init 4 (fun k ->
        Bitstring.bitstring_of_string
          (String.init 24 (fun i -> Char.chr ((i * 37 + k * 11 + 5) land 0xff))))
  in
    let shorts =
    Array.init 4 (fun k ->
        Bitstring.bitstring_of_string
          (String.init 18 (fun i -> Char.chr ((i * 37 + k * 11 + 5) land 0xff))))
  in
  print_endline "parse, non-matching subject (fast reject):";
  time "classic ppx" (fun () ->
      for i = 1 to n do
        ignore
          (Sys.opaque_identity
             (P.fields (Array.unsafe_get shorts (i land 3))))
      done);
  time "staged (consolidated check)" (fun () ->
      for i = 1 to n do
        ignore
          (Sys.opaque_identity
             (S.fields (Array.unsafe_get shorts (i land 3))))
      done);
  print_endline "parse (9-field static match):";
  time "classic ppx" (fun () ->
      for i = 1 to n do
        ignore
          (Sys.opaque_identity
             (P.fields (Array.unsafe_get subjects (i land 3))))
      done);
  time "staged" (fun () ->
      for i = 1 to n do
        ignore
          (Sys.opaque_identity
             (S.fields (Array.unsafe_get subjects (i land 3))))
      done)
;;

let () =
  let mk tag = Bitstring.bitstring_of_string (String.make 1 (Char.chr tag) ^ "\x02\x01\x02\x03\x04\x05") in
  let cycling = Array.init 8 (fun k -> mk (k + 1)) in
  let last = Array.make 8 (mk 8) in
  let none = Array.make 8 (mk 0x40) in
  let run name subjects =
    Printf.printf "parse, 8-case tag dispatch (%s):\n" name;
    time "classic ppx" (fun () ->
        for i = 1 to n do
          ignore
            (Sys.opaque_identity
               (P.dispatch (Array.unsafe_get subjects (i land 7))))
        done);
    time "staged" (fun () ->
        for i = 1 to n do
          ignore
            (Sys.opaque_identity
               (S.dispatch (Array.unsafe_get subjects (i land 7))))
        done)
  in
  run "cycling tags" cycling;
  run "last tag" last;
  run "no matching tag" none
