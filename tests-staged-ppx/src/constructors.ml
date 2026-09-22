
let packet ver len payload crc =
  [%bitstring
    {| 0xab : 8 ; ver : 4 ; 0x2 : 4 ; len : 8 ;
       payload : (String.length payload * 8) : string ;
       crc : 16 : littleendian |}]

let mixed b c i12 i20 w g s bits =
  [%bitstring
    {| b : 1 ; c : 5 ; i12 : 12 : signed ; i20 : 20 : littleendian ;
       w : 32 ; g : 48 : littleendian ; s : 16 : string ;
       bits : 12 : bitstring |}]

let dyn_i n v = [%bitstring {| n : 5 ; v : n+33 |}]

let with_endian rt v = [%bitstring {| v : 16 : endian (rt) |}]

let lb x =
  let%bitstring b = {| x : 8 ; 1 : 1 ; 0 : 7 |} in
  b

let hdr magic v1 v2 b flags seq name =
  [%bitstring
    {| magic : 16 ; v1 : 4 ; v2 : 4 ; b : 1 ; flags : 7 ; seq : 32 ;
       name : 32 : string ; 0x3 : 2 ; 0 : 6 |}]
