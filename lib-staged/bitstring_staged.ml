
type sign = Unsigned | Signed
type endian = Big | Little | Native | Referred of Bitstring.endian expr
type size = Const of int | Dyn of int expr | All

type int_desc = { size : int; sign : sign; endian : endian } 
type int64_desc = { size64 : size; endian64 : endian } 

type 'r spec =
  | Done : 'r expr -> 'r spec
  | Bit : (bool expr -> 'r spec) -> 'r spec
  | Int : int_desc * (int expr -> 'r spec) -> 'r spec
  | IntLit : int_desc * int * 'r spec -> 'r spec
        | Int32 : endian * (int32 expr -> 'r spec) -> 'r spec
  | Int64 : int64_desc * (int64 expr -> 'r spec) -> 'r spec
  | String : size * (string expr -> 'r spec) -> 'r spec
  | Bits : size * (Bitstring.t expr -> 'r spec) -> 'r spec
  | Guard : bool expr * 'r spec -> 'r spec
        | Let : 'a expr * ('a expr -> 'r spec) -> 'r spec
        | SaveOffset : (int expr -> 'r spec) -> 'r spec
        | Seek : size * 'r spec -> 'r spec
        | Matched : (Bitstring.t expr -> 'r spec) -> 'r spec
      
type consumed = Static of int | Dynamic of int expr

$let dummy_bits_ : Bitstring.t expr = << Bitstring.empty_bitstring >>

$let validate_ : 'r. 'r spec -> unit = fun spec ->
  let rec go : 'r spec -> unit = function
    | Done _ -> ()
    | Guard (_, rest) -> go rest
    | Let (e, f) -> go (f e)
    | SaveOffset f -> go (f << 0 >>)
    | Seek (All, _) -> failwith "Bitstring_staged: Seek size cannot be All"
    | Seek (_, rest) -> go rest
    | Matched f -> go (f dummy_bits_)
    | Bit f -> go (f << true >>)
    | Int ({ size; _ }, f) ->
        if size < 2 || size > 31 then
          failwith
            (Printf.sprintf "Bitstring_staged: Int size %d not in 2..31" size);
        go (f << 0 >>)
    | IntLit ({ size; _ }, _, rest) ->
        if size < 2 || size > 31 then
          failwith
            (Printf.sprintf "Bitstring_staged: IntLit size %d not in 2..31"
               size);
        go rest
    | Int32 (_, f) -> go (f << 0l >>)
    | Int64 ({ size64 = Const n; _ }, f) ->
        if n < 33 || n > 64 then
          failwith
            (Printf.sprintf "Bitstring_staged: Int64 size %d not in 33..64" n);
        go (f << 0L >>)
    | Int64 ({ size64 = Dyn _; _ }, f) -> go (f << 0L >>)
    | Int64 ({ size64 = All; _ }, _) ->
        failwith "Bitstring_staged: integer fields cannot have size All"
    | String (Const n, f) ->
        if n < 0 || n mod 8 <> 0 then
          failwith
            (Printf.sprintf
               "Bitstring_staged: String size %d not a non-negative multiple \
                of 8"
               n);
        go (f << "" >>)
    | String ((Dyn _ | All), f) -> go (f << "" >>)
    | Bits (Const n, f) ->
        if n < 0 then failwith "Bitstring_staged: negative Bits size";
        go (f dummy_bits_)
    | Bits ((Dyn _ | All), f) -> go (f dummy_bits_)
  in
  go spec

$let static_bits_ : 'r. 'r spec -> int option = fun spec ->
  let add n = function Some m -> Some (n + m) | None -> None in
  let rec go : 'r spec -> int option = function
    | Done _ -> Some 0
    | Guard (_, rest) -> go rest
    | Let (e, f) -> go (f e)
    | SaveOffset f -> go (f << 0 >>)
    | Seek _ -> None
    | Matched f -> go (f dummy_bits_)
    | Bit f -> add 1 (go (f << true >>))
    | Int ({ size; _ }, f) -> add size (go (f << 0 >>))
    | IntLit ({ size; _ }, _, rest) -> add size (go rest)
    | Int32 (_, f) -> add 32 (go (f << 0l >>))
    | Int64 ({ size64 = Const n; _ }, f) -> add n (go (f << 0L >>))
    | Int64 ({ size64 = Dyn _ | All; _ }, _) -> None
    | String (Const n, f) -> add n (go (f << "" >>))
    | String (Dyn _, _) -> None
    | String (All, f) -> (
                match go (f << "" >>) with Some 0 -> Some 0 | _ -> None)
    | Bits (Const n, f) -> add n (go (f dummy_bits_))
    | Bits (Dyn _, _) -> None
    | Bits (All, f) -> (
        match go (f dummy_bits_) with Some 0 -> Some 0 | _ -> None)
  in
  go spec


$let advance_ : int expr -> consumed -> size -> consumed = fun blen c s ->
  match (c, s) with
  | _, All -> Dynamic blen
  | Static n, Const m -> Static (n + m)
  | Static n, Dyn e -> Dynamic << $(Expr.int n) + $e >>
  | Dynamic e, Const m -> Dynamic << $e + $(Expr.int m) >>
  | Dynamic e, Dyn e' -> Dynamic << $e + $e' >>

$let abs_off_ : int expr -> consumed -> int expr = fun boff c ->
  match c with
  | Static 0 -> boff
  | Static n -> << $boff + $(Expr.int n) >>
  | Dynamic e -> << $boff + $e >>

$let remaining_ : int expr -> consumed -> int expr = fun blen c ->
  match c with
  | Static 0 -> blen
  | Static n -> << $blen - $(Expr.int n) >>
  | Dynamic e -> << $blen - $e >>

$let size_expr_ : size -> int expr = function
  | Const n -> Expr.int n
  | Dyn e -> e
  | All -> failwith "Bitstring_staged: size_expr_ applied to All"


$let int_extract_ :
  sign -> endian -> data:bytes expr -> off:int expr -> rem:int expr ->
  size:int expr -> int expr =
  fun sign endian ~data ~off ~rem ~size ->
  match (endian, sign) with
  | Big, Unsigned ->
      << Bitstring.extract_int_be_unsigned $data $off $rem $size >>
  | Big, Signed -> << Bitstring.extract_int_be_signed $data $off $rem $size >>
  | Little, Unsigned ->
      << Bitstring.extract_int_le_unsigned $data $off $rem $size >>
  | Little, Signed ->
      << Bitstring.extract_int_le_signed $data $off $rem $size >>
  | Native, Unsigned ->
      << Bitstring.extract_int_ne_unsigned $data $off $rem $size >>
  | Native, Signed ->
      << Bitstring.extract_int_ne_signed $data $off $rem $size >>
  | Referred e, Unsigned ->
      << Bitstring.extract_int_ee_unsigned $e $data $off $rem $size >>
  | Referred e, Signed ->
      << Bitstring.extract_int_ee_signed $e $data $off $rem $size >>

$let char_extract_ :
  sign -> data:bytes expr -> off:int expr -> rem:int expr ->
  size:int expr -> int expr =
  fun sign ~data ~off ~rem ~size ->
  match sign with
  | Unsigned -> << Bitstring.extract_char_unsigned $data $off $rem $size >>
  | Signed -> << Bitstring.extract_char_signed $data $off $rem $size >>

$let int_field_extract_ :
  int_desc -> data:bytes expr -> off:int expr -> rem:int expr -> int expr =
  fun { size; sign; endian } ~data ~off ~rem ->
  if size <= 8 then char_extract_ sign ~data ~off ~rem ~size:(Expr.int size)
  else int_extract_ sign endian ~data ~off ~rem ~size:(Expr.int size)

$let int32_extract_ :
  endian -> data:bytes expr -> off:int expr -> rem:int expr -> int32 expr =
  fun endian ~data ~off ~rem ->
  match endian with
  | Big -> << Bitstring.extract_int32_be_unsigned $data $off $rem 32 >>
  | Little -> << Bitstring.extract_int32_le_unsigned $data $off $rem 32 >>
  | Native -> << Bitstring.extract_int32_ne_unsigned $data $off $rem 32 >>
  | Referred e ->
      << Bitstring.extract_int32_ee_unsigned $e $data $off $rem 32 >>

$let int64_extract_ :
  endian -> data:bytes expr -> off:int expr -> rem:int expr ->
  size:int expr -> int64 expr =
  fun endian ~data ~off ~rem ~size ->
  match endian with
  | Big -> << Bitstring.extract_int64_be_unsigned $data $off $rem $size >>
  | Little -> << Bitstring.extract_int64_le_unsigned $data $off $rem $size >>
  | Native -> << Bitstring.extract_int64_ne_unsigned $data $off $rem $size >>
  | Referred e ->
      << Bitstring.extract_int64_ee_unsigned $e $data $off $rem $size >>


$let walk_ :
  'r. 'r spec -> data:bytes expr -> boff:int expr -> blen:int expr ->
  start:consumed -> checked:bool -> fail:'r expr -> 'r expr =
  fun spec ~data ~boff ~blen ~start ~checked ~fail ->
  let rec go : 'r spec -> consumed -> 'r expr =
    fun spec c ->
      let guard ~need body =
        if checked then body
        else
          << if $(remaining_ blen c) >= $(size_expr_ need) then $body
             else $fail >>
      in
      let off = abs_off_ boff c in
      let rem = remaining_ blen c in
      match spec with
      | Done body -> body
      | Guard (cond, rest) -> << if $cond then $(go rest c) else $fail >>
      | Let (e, f) -> << let v = $e in $(go (f << v >>) c) >>
      | SaveOffset f ->
          let off_e =
            match c with Static n -> Expr.int n | Dynamic e -> e
          in
          go (f off_e) c
      | Seek (All, _) -> failwith "Bitstring_staged: Seek size cannot be All"
      | Seek (Const n, rest) -> go rest (Static n)
      | Seek (Dyn e, rest) -> go rest (Dynamic e)
      | Matched f ->
          let consumed_e =
            match c with Static n -> Expr.int n | Dynamic e -> e
          in
          go (f << ($data, $boff, $consumed_e) >>) c
      | Bit f ->
          guard ~need:(Const 1)
            << let v = Bitstring.extract_bit $data $off $rem 1 in
               $(go (f << v >>) (advance_ blen c (Const 1))) >>
      | Int (({ size; _ } as desc), f) ->
          let ex = int_field_extract_ desc ~data ~off ~rem in
          guard ~need:(Const size)
            << let v = $ex in $(go (f << v >>) (advance_ blen c (Const size))) >>
      | IntLit (({ size; _ } as desc), lit, rest) ->
          let ex = int_field_extract_ desc ~data ~off ~rem in
          guard ~need:(Const size)
            << if $ex = $(Expr.int lit) then
                 $(go rest (advance_ blen c (Const size)))
               else $fail >>
      | Int32 (endian, f) ->
          guard ~need:(Const 32)
            << let v = $(int32_extract_ endian ~data ~off ~rem) in
               $(go (f << v >>) (advance_ blen c (Const 32))) >>
      | Int64 (({ size64; endian64 } : int64_desc), f) ->
          guard ~need:size64
            << let v =
                 $(int64_extract_ endian64 ~data ~off ~rem
                     ~size:(size_expr_ size64))
               in
               $(go (f << v >>) (advance_ blen c size64)) >>
      | String (All, f) ->
          << let v = Bitstring.string_of_bitstring ($data, $off, $rem) in
             $(go (f << v >>) (Dynamic blen)) >>
      | String (size, f) ->
          guard ~need:size
            << let v =
                 Bitstring.string_of_bitstring
                   ($data, $off, $(size_expr_ size))
               in
               $(go (f << v >>) (advance_ blen c size)) >>
      | Bits (All, f) ->
          << let v = ($data, $off, $rem) in
             $(go (f << v >>) (Dynamic blen)) >>
      | Bits (size, f) ->
          guard ~need:size
            << let v = ($data, $off, $(size_expr_ size)) in
               $(go (f << v >>) (advance_ blen c size)) >>
  in
  go spec start


$let max_switch_bits_ : int = 8

$let dispatch_key_ : 'r. 'r spec -> (int * sign) option = function
  | IntLit ({ size; sign; _ }, _, _) when size <= max_switch_bits_ ->
      Some (size, sign)
  | _ -> None

$let leading_run_ :
  'r. 'r spec list -> ((int * sign) * 'r spec list * 'r spec list) option =
  fun cases ->
  match cases with
  | [] -> None
  | first :: _ -> (
      match dispatch_key_ first with
      | None -> None
      | Some key ->
          let rec split acc = function
            | c :: rest when dispatch_key_ c = Some key -> split (c :: acc) rest
            | rest -> (List.rev acc, rest)
          in
          let run, rest = split [] cases in
          Some (key, run, rest))

$let buckets_ : 'r. 'r spec list -> (int * 'r spec list) list = fun run ->
  let rec add lit tail = function
    | [] -> [ (lit, [ tail ]) ]
    | (l, tails) :: more when l = lit -> (l, tails @ [ tail ]) :: more
    | b :: more -> b :: add lit tail more
  in
  List.fold_left
    (fun acc spec ->
      match spec with
      | IntLit (_, lit, tail) -> add lit tail acc
      | _ -> failwith "Bitstring_staged: buckets_ applied to a non-literal case")
    [] run

$let one_case_ :
  'r. 'r spec -> data:bytes expr -> boff:int expr -> blen:int expr ->
  skip:int -> known:int -> fail:'r expr -> 'r expr =
  fun spec ~data ~boff ~blen ~skip ~known ~fail ->
  match static_bits_ spec with
  | Some need ->
      let body =
        walk_ spec ~data ~boff ~blen ~start:(Static skip) ~checked:true ~fail
      in
      if skip + need <= known then body
      else << if $blen >= $(Expr.int (skip + need)) then $body else $fail >>
  | None ->
      walk_ spec ~data ~boff ~blen ~start:(Static skip) ~checked:false ~fail

$let match_ :
  'r. Bitstring.t expr -> 'r spec list -> default:(unit -> 'r) expr ->
  'r expr =
  fun bs cases ~default ->
  let rec cascade :
    'r spec list -> data:bytes expr -> boff:int expr -> blen:int expr ->
    skip:int -> known:int -> fin:'r expr -> 'r expr =
    fun cases ~data ~boff ~blen ~skip ~known ~fin ->
      match cases with
      | [] -> fin
      | spec :: rest -> (
          match leading_run_ cases with
          | Some ((size, sign), run, rest) when List.length run >= 2 ->
              List.iter validate_ run;
              let next = cascade rest ~data ~boff ~blen ~skip ~known ~fin in
              << let next () = $next in
                 $(dispatch run ~size ~sign ~data ~boff ~blen ~skip ~known
                     ~next:<< next () >>) >>
          | _ ->
              validate_ spec;
              let next = cascade rest ~data ~boff ~blen ~skip ~known ~fin in
              << let next () = $next in
                 $(one_case_ spec ~data ~boff ~blen ~skip ~known
                     ~fail:<< next () >>) >>)
  and dispatch :
    'r spec list -> size:int -> sign:sign -> data:bytes expr ->
    boff:int expr -> blen:int expr -> skip:int -> known:int -> next:'r expr ->
    'r expr =
    fun run ~size ~sign ~data ~boff ~blen ~skip ~known ~next ->
      let desc =
        match run with
        | IntLit (d, _, _) :: _ -> d
        | _ -> failwith "Bitstring_staged: dispatch on a non-literal run"
      in
      let shift = match sign with Unsigned -> 0 | Signed -> 1 lsl (size - 1) in
      let numconsts = 1 lsl size in
      let known' = skip + size in
      let arms =
        List.filter_map
          (fun (lit, tails) ->
            let i = lit + shift in
            if i < 0 || i >= numconsts then None
            else
              Some
                ( i,
                  cascade tails ~data ~boff ~blen ~skip:known' ~known:known'
                    ~fin:next ))
          (buckets_ run)
      in
      match arms with
      | [] -> next
      | _ ->
          let c = Static skip in
          let ex =
            int_field_extract_ desc ~data ~off:(abs_off_ boff c)
              ~rem:(remaining_ blen c)
          in
          let body =
            Expr.switch (module Int)
              (if shift = 0 then ex else << $ex + $(Expr.int shift) >>)
              ~numconsts arms (Some next)
          in
          if known' <= known then body
          else << if $blen >= $(Expr.int known') then $body else $next >>
  in
  << let bs_data, bs_boff, bs_blen = $bs in
     $(cascade cases ~data:<< bs_data >> ~boff:<< bs_boff >>
         ~blen:<< bs_blen >> ~skip:0 ~known:0 ~fin:<< $default () >>) >>


type cfield =
  | CBit of bool expr
  | CInt of int_desc * int expr 
  | CInt32 of endian * int32 expr
  | CInt64 of int64_desc * int64 expr 
  | CString of size * string expr
        | CBits of Bitstring.t expr

$let construct_int_ :
  sign -> endian -> buf:Bitstring.Buffer.t expr -> v:int expr ->
  size:int expr -> exn:exn expr -> unit expr =
  fun sign endian ~buf ~v ~size ~exn ->
  match (endian, sign) with
  | Big, Unsigned -> << Bitstring.construct_int_be_unsigned $buf $v $size $exn >>
  | Big, Signed -> << Bitstring.construct_int_be_signed $buf $v $size $exn >>
  | Little, Unsigned -> << Bitstring.construct_int_le_unsigned $buf $v $size $exn >>
  | Little, Signed -> << Bitstring.construct_int_le_signed $buf $v $size $exn >>
  | Native, Unsigned -> << Bitstring.construct_int_ne_unsigned $buf $v $size $exn >>
  | Native, Signed -> << Bitstring.construct_int_ne_signed $buf $v $size $exn >>
  | Referred e, Unsigned ->
      << Bitstring.construct_int_ee_unsigned $e $buf $v $size $exn >>
  | Referred e, Signed ->
      << Bitstring.construct_int_ee_signed $e $buf $v $size $exn >>

$let construct_int32_ :
  endian -> buf:Bitstring.Buffer.t expr -> v:int32 expr -> exn:exn expr ->
  unit expr =
  fun endian ~buf ~v ~exn ->
  match endian with
  | Big -> << Bitstring.construct_int32_be_unsigned $buf $v 32 $exn >>
  | Little -> << Bitstring.construct_int32_le_unsigned $buf $v 32 $exn >>
  | Native -> << Bitstring.construct_int32_ne_unsigned $buf $v 32 $exn >>
  | Referred e ->
      << Bitstring.construct_int32_ee_unsigned $e $buf $v 32 $exn >>

$let construct_int64_ :
  endian -> buf:Bitstring.Buffer.t expr -> v:int64 expr ->
  size:int expr -> exn:exn expr -> unit expr =
  fun endian ~buf ~v ~size ~exn ->
  match endian with
  | Big -> << Bitstring.construct_int64_be_unsigned $buf $v $size $exn >>
  | Little -> << Bitstring.construct_int64_le_unsigned $buf $v $size $exn >>
  | Native -> << Bitstring.construct_int64_ne_unsigned $buf $v $size $exn >>
  | Referred e ->
      << Bitstring.construct_int64_ee_unsigned $e $buf $v $size $exn >>

$let construct_field_ :
  buf:Bitstring.Buffer.t expr -> exn:exn expr -> cfield -> unit expr =
  fun ~buf ~exn field ->
  match field with
  | CBit v -> << Bitstring.construct_bit $buf $v 1 $exn >>
  | CInt ({ size; sign; endian }, v) ->
      if size < 2 || size > 31 then
        failwith
          (Printf.sprintf "Bitstring_staged: CInt size %d not in 2..31" size);
      if size <= 8 then
        match sign with
        | Unsigned ->
            << Bitstring.construct_char_unsigned $buf $v $(Expr.int size)
                 $exn >>
        | Signed ->
            << Bitstring.construct_char_signed $buf $v $(Expr.int size)
                 $exn >>
      else
        construct_int_ sign endian ~buf ~v ~size:(Expr.int size) ~exn
  | CInt32 (endian, v) -> construct_int32_ endian ~buf ~v ~exn
  | CInt64 ({ size64; endian64 }, v) ->
      let size =
        match size64 with
        | Const n ->
            if n < 33 || n > 64 then
              failwith
                (Printf.sprintf
                   "Bitstring_staged: CInt64 size %d not in 33..64" n);
            Expr.int n
        | Dyn e -> e
        | All -> failwith "Bitstring_staged: CInt64 size cannot be All"
      in
      construct_int64_ endian64 ~buf ~v ~size ~exn
  | CString (_, v) -> << Bitstring.construct_string $buf $v >>
  | CBits v -> << Bitstring.construct_bitstring $buf $v >>


type cpiece =
  | PBits of int * int * [ `Bool | `Int | `I32 ] 
  | PStr of int * int 

$let static_plan_ : cfield list -> (int * cpiece list) option = fun fields ->
  let rec go off acc = function
    | [] -> Some (off, List.rev acc)
    | CBit _ :: r -> go (off + 1) (PBits (off, 1, `Bool) :: acc) r
    | CInt ({ size; sign = Unsigned; endian = Big }, _) :: r
      when size >= 2 && size <= 31 ->
        go (off + size) (PBits (off, size, `Int) :: acc) r
    | CInt32 (Big, _) :: r -> go (off + 32) (PBits (off, 32, `I32) :: acc) r
    | CString (Const n, _) :: r when off land 7 = 0 && n mod 8 = 0 && n >= 0
      ->
        go (off + n) (PStr (off asr 3, n asr 3) :: acc) r
    | _ -> None
  in
  go 0 [] fields

$let pack_static_ :
  exn:exn expr -> total:int -> (cpiece * cfield) list -> Bitstring.t expr =
  fun ~exn ~total pieces ->
  let nbytes = (total + 7) asr 3 in
    let bytes : (int expr list) array = Array.make (max nbytes 1) [] in
  let strs : (int * int * string expr) list ref = ref [] in
    let rec emit_values b rev_srcs = function
    | [] -> finish b (List.rev rev_srcs)
    | (PBits (_, _, `Bool), CBit v) :: rest ->
        << let s = if $v then 1 else 0 in
           $(emit_values b (Some << s >> :: rev_srcs) rest) >>
    | (PBits (_, w, `Int), CInt (_, v)) :: rest ->
        << let s = $v in
           if s lsr $(Expr.int w) <> 0 then raise $exn;
           $(emit_values b (Some << s >> :: rev_srcs) rest) >>
    | (PBits (_, _, `I32), CInt32 (_, v)) :: rest ->
        << let s = Int32.to_int $v land 0xFFFFFFFF in
           $(emit_values b (Some << s >> :: rev_srcs) rest) >>
    | (PStr (bo, bn), CString (_, v)) :: rest ->
        strs := (bo, bn, v) :: !strs;
        << if String.length $v <> $(Expr.int bn) then raise Exit;
           $(emit_values b (None :: rev_srcs) rest) >>
    | _ -> failwith "Bitstring_staged: pack_static_ plan mismatch"
  and finish b srcs =
        List.iteri
      (fun i (piece, _) ->
        match (piece, List.nth srcs i) with
        | PBits (off, width, _), Some src ->
            let last = off + width in
            let j0 = off asr 3 and j1 = (last - 1) asr 3 in
            for j = j0 to j1 do
              let hi = max off (8 * j) and lo = min last ((8 * j) + 8) in
              let w = lo - hi in
              let shift_out = 8 * j + 8 - lo in
              let shift_in = last - lo in
              let mask = (1 lsl w) - 1 in
              let piece_e =
                if shift_in = 0 && mask = 255 then src
                else if shift_in = 0 then
                  << $src land $(Expr.int mask) >>
                else
                  << ($src lsr $(Expr.int shift_in))
                     land $(Expr.int mask) >>
              in
              let piece_e =
                if shift_out = 0 then piece_e
                else << $piece_e lsl $(Expr.int shift_out) >>
              in
              bytes.(j) <- piece_e :: bytes.(j)
            done
        | PStr _, None -> ()
        | _ -> failwith "Bitstring_staged: pack_static_ source mismatch")
      pieces;
    let rec writes j =
      if j >= nbytes then blits !strs
      else
        match List.rev bytes.(j) with
        | [] -> writes (j + 1)
        | e :: es ->
            let composed =
              List.fold_left (fun acc e -> << $acc lor $e >>) e es
            in
            << Bytes.unsafe_set $b $(Expr.int j)
                 (Char.unsafe_chr $composed);
               $(writes (j + 1)) >>
    and blits = function
      | [] -> << ($b, 0, $(Expr.int total)) >>
      | (bo, bn, v) :: rest ->
          << Bytes.blit_string $v 0 $b $(Expr.int bo) $(Expr.int bn);
             $(blits rest) >>
    in
    writes 0
  in
  << let b = Bytes.make $(Expr.int nbytes) '\000' in
     $(emit_values << b >> [] pieces) >>

$let construct_ :
  loc:string * int * int -> ?expect:int expr -> cfield list ->
  Bitstring.t expr =
  fun ~loc:(file, line, char) ?expect fields ->
  let exn_e =
    << Bitstring.Construct_failure
         ( "Bad field value",
           $(Expr.string file),
           $(Expr.int line),
           $(Expr.int char) ) >>
  in
  let finish buf =
    match expect with
    | None -> << Bitstring.Buffer.contents $buf >>
    | Some n ->
        << let _res = Bitstring.Buffer.contents $buf in
           if Stdlib.( = ) (Bitstring.bitstring_length _res) $n then _res
           else raise Exit >>
  in
  let rec seq buf exn = function
    | [] -> finish buf
    | f :: rest ->
        << $(construct_field_ ~buf ~exn f);
           $(seq buf exn rest) >>
  in
  match static_plan_ fields with
  | Some (total, pieces) ->
      << let exn = $exn_e in
         $(pack_static_ ~exn:<< exn >> ~total
             (List.combine pieces fields)) >>
  | None ->
      << let buf = Bitstring.Buffer.create () in
         let exn = $exn_e in
         $(seq << buf >> << exn >> fields) >>
