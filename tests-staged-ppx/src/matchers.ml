
let classify bs =
  match%bitstring bs with
  | {| 0xab : 8 ; ver : 4 ; flags : 4 : littleendian ; len : 8 ;
       payload : len*8 : string ; crc : 16 : littleendian |}
    when ver > 0 ->
      `Framed (ver, flags, len, payload, crc)
  | {| tag : 8 ; body : -1 : bitstring |} ->
            `Raw (tag, Bitstring.string_of_bitstring body)
  | {| _ |} -> `Empty

let fields bs =
  match%bitstring bs with
  | {| b : 1 ; c : 5 ; i12 : 12 : signed ; i20 : 20 : littleendian ;
       w : 32 ; g : 48 : littleendian ; s : 16 : string ;
       sub : 12 : bitstring ; rest : -1 : bitstring |} ->
      Some (b, c, i12, i20, w, g, s,
            Bitstring.string_of_bitstring sub,
            Bitstring.bitstring_length rest)
  | {| _ |} -> None

let checked bs =
  match%bitstring bs with
  | {| n : 8 : check (n land 1 = 0) ; rest : -1 : bitstring |} ->
      `Even (n, Bitstring.string_of_bitstring rest)
  | {| n : 8 ; rest : -1 : bitstring |} ->
      `Odd (n, Bitstring.string_of_bitstring rest)
  | {| _ |} -> `Other

let skipping bs =
  match%bitstring bs with
  | {| _ : 8 ; x : 8 |} -> Some x
  | {| _ |} -> None

let dyn_int bs =
  match%bitstring bs with
  | {| n : 5 ; v : n+33 ; rest : -1 : bitstring |} ->
      Some (n, v, Bitstring.bitstring_length rest)
  | {| _ |} -> None

let referred rt bs =
  match%bitstring bs with
  | {| v : 16 : endian (rt) |} -> Some v
  | {| _ |} -> None


let quals bs =
  match%bitstring bs with
  | {| n : 8 : map (fun v -> v * 2) ;
       m : 8 : save_offset_to (moff) ;
       k : 8 : bind (n + 100) |} ->
      Some (n, m, moff, k)
  | {| _ |} -> None

let seeked bs =
  match%bitstring bs with
  | {| n : 8 ; m : 8 : offset (24) |} -> Some (n, m)
  | {| _ |} -> None

let aliased bs =
  match%bitstring bs with
  | {| t : 8 |} as whole when t > 0 ->
      Some (t, Bitstring.bitstring_length whole,
            Bitstring.string_of_bitstring whole)
  | {| _ |} -> None
